# ｖ0.1.3 20260309
# ｖ0.1.4 20260310
#    BGMの再生中に途切れる現象（音飛び）を防ぐために、BGMや環境音を一度メモリ上にロードしてキャッシュするように変更
#    「シーンBGM」から「defaultのBGM」に切り替わる場合の分岐の中にフェードアウト処理が書かれてい難いのを修正
#    このPythonプロセス自身が現在システム全体に対してどのくらいCPUを使用しているか（0〜100%）を表示する機能を追加
#    「※メニューを開いた時など」というテキストを画面から削除
#    「ツール動作FPS」という表記をすべて「FPS: -- / CPU: 0.0%」に統一
# ｖ0.1.8 20260312 (Integrated Version)
#    消失していた「Auto Volume Sync」「閾値/間隔/猶予時間」「環境音自動切替」を完全復元
# ｖ0.2.1 20260312 (Thread Safety)
#    案A(Lock)と案B(Join)を盛り込み、スレッド競合とクラッシュの種を完全排除
# ｖ0.2.5 20260312 (Delayed Write Implementation)
#    スライダー操作中の頻繁なディスク保存を廃止し、マウスボタンを離した瞬間に保存する仕様へ変更
# ｖ0.2.6 20260312 (Deadlock Fix)
#    シーン切替時のデッドロック(フリーズ)を解決するため、Lockを RLock に変更
# ｖ0.2.8 20260312 (Crash Fix)
#    長時間再生時の ModPlug_Load failed クラッシュを namehint の追加と例外処理で解決
# ｖ0.2.9 20260312 (Volume Forecast Fix)
#    BGM音量設定時に「参考最大出力(Boost 200%時)」を表示し、100%超えで警告する機能を追加
# ｖ0.3.0 20260312 (Rounding Consistency Fix)
#    音量表示と最大出力予測の計算基準を整数値に統一し、表示の不整合（25%なのに最大51%など）を修正
# ｖ0.3.1 20260314 (Mild Ambient Removal)
#    環境音機能をUIから隠し、処理を停止。BGM機能への影響を与えないようマイルドに工事。
# ｖ0.3.2 20260314 (Interval Limit Expansion)
#    監視間隔の最大値を 5.0 秒から 10.0 秒へ拡張。
# ｖ0.3.3 20260314 (Fade Time Configuration)
#    フェードアウト時間の設定項目を追加。判定猶予の横に配置し、切り替えテンポを一元管理。
import time
import os
import sys
import glob
import random
import json
import threading
import io
import gc
import tkinter as tk
from tkinter import ttk, messagebox
import psutil

try:
    import sv_ttk
    import darkdetect
    HAS_THEME_LIBS = True
except ImportError:
    HAS_THEME_LIBS = False

import bettercam
import cv2
import numpy as np
import pygame

try:
    from pycaw.pycaw import AudioUtilities, ISimpleAudioVolume, IAudioMeterInformation
    from ctypes import cast, POINTER
    HAS_PYCAW = True
except ImportError:
    HAS_PYCAW = False

CONFIG_FILE = "config.json"

# --- グローバル変数 ---
play_history = []
ambient_play_history = []
bgm_cache = {}
bgm_cache_order = []
MAX_BGM_CACHE = 10

ambient_sound_cache = {}
ambient_cache_order = []
MAX_AMBIENT_CACHE = 20

current_bgm_io = None
step_count = 1

# スレッド安全のためのロックオブジェクト (再入可能ロック)
config_lock = threading.RLock()
bgm_thread = None
sync_thread = None

def log_debug(func_name, message=""):
    global step_count
    print(f"[Step {step_count}] ▶ [{func_name}] {message}")
    step_count += 1

# --- キャッシュ管理 (LRU) ---
def load_cached_bgm(file_path):
    """BGMファイルをメモリにロードし、BytesIOとして返す。"""
    global current_bgm_io, bgm_cache, bgm_cache_order
    if file_path in bgm_cache:
        bgm_cache_order.remove(file_path)
        bgm_cache_order.append(file_path)
    else:
        try:
            if len(bgm_cache) >= MAX_BGM_CACHE:
                oldest = bgm_cache_order.pop(0)
                if oldest in bgm_cache: del bgm_cache[oldest]
            with open(file_path, "rb") as f:
                bgm_cache[file_path] = f.read()
                bgm_cache_order.append(file_path)
        except Exception as e:
            log_debug("load_cached_bgm", f"Fail: {e}")
            return file_path
    current_bgm_io = io.BytesIO(bgm_cache[file_path])
    return current_bgm_io

def get_cached_ambient(file_path):
    """(現在は非アクティブ) 環境音ファイルをキャッシュ。"""
    global ambient_sound_cache, ambient_cache_order
    if file_path in ambient_sound_cache:
        ambient_cache_order.remove(file_path)
        ambient_cache_order.append(file_path)
    else:
        try:
            if len(ambient_sound_cache) >= MAX_AMBIENT_CACHE:
                oldest = ambient_cache_order.pop(0)
                if oldest in ambient_sound_cache: del ambient_sound_cache[oldest]
            ambient_sound_cache[file_path] = pygame.mixer.Sound(file_path)
            ambient_cache_order.append(file_path)
        except Exception as e:
            log_debug("get_cached_ambient", f"Fail: {e}")
            return None
    return ambient_sound_cache.get(file_path)

# --- 楽曲選択ロジック ---
def get_random_bgm(files_list):
    global play_history
    if not files_list: return None
    available = [f for f in files_list if f not in play_history[-2:]]
    if not available: available = files_list
    choice = random.choice(available)
    play_history.append(choice)
    if len(play_history) > 10: play_history.pop(0)
    return choice

# --- 設定管理 ---
DEFAULT_CONFIG = {
    "global_volume": 0.5,
    "global_ambient_volume": 0.5,
    "match_threshold": 0.8,
    "check_interval_sec": 1.0,
    "fade_ms": 3000,
    "grace_period_sec": 5.0,
    "region_anchor": "top_left",
    "region_width": 0,
    "region_height": 0,
    "scene_anchors": {},
    "scene_widths": {},
    "scene_heights": {},
    "sync_app_name": "",
    "sync_mode": "None",
    "sync_strength": 0.5,
    "sync_smoothness": 5.0
}

SCENE_CONFIG = [{"id": i, "template": f"target/scene{i}.png", "bgm": f"bgm/scene{i}.mp3"} for i in range(1, 9)]

config = {}
is_running = False
current_volume_modifier = 1.0
ambient_channel = None
current_ambient_path = None
current_ambient_sound = None

def load_config():
    global config
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                config = json.load(f)
            for k, v in DEFAULT_CONFIG.items():
                if k not in config: config[k] = v
        except Exception: config = DEFAULT_CONFIG.copy()
    else:
        config = DEFAULT_CONFIG.copy()
        save_config()

def save_config():
    try:
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            with config_lock:
                json.dump(config, f, indent=4)
        log_debug("save_config", "Config saved to disk.")
    except Exception as e: log_debug("save_config", str(e))

# --- 音量制御 ---
def apply_volumes(modifier=1.0):
    if not pygame.mixer.get_init(): return
    with config_lock:
        bgm_vol = config["global_volume"]
    pygame.mixer.music.set_volume(bgm_vol * modifier)

def update_volume(val):
    v_float = float(val)
    v_int = int(v_float) 
    with config_lock:
        config["global_volume"] = v_float / 100.0
    if 'lbl_vol_val' in globals():
        max_v = v_int * 2
        warn = " ⚠️" if max_v > 100 else ""
        text = f"{v_int}% (最大:{max_v}%{warn})"
        lbl_vol_val.config(text=text, foreground="#ff6b6b" if max_v > 100 else "")
    apply_volumes(current_volume_modifier)

def update_threshold(val):
    with config_lock:
        config["match_threshold"] = float(val) / 100.0
    if 'lbl_thresh_val' in globals():
        lbl_thresh_val.config(text=f"{config['match_threshold']:.2f}")

def update_interval(val):
    with config_lock:
        config["check_interval_sec"] = float(val)
    if 'lbl_interval_val' in globals():
        lbl_interval_val.config(text=f"{config['check_interval_sec']:.1f} 秒")

def update_grace_period(event=None):
    try:
        val = float(grace_period_var.get())
        with config_lock:
            config["grace_period_sec"] = max(0.0, val)
    except ValueError: pass
    save_config()

def update_fade_time(event=None):
    """フェードアウト時間をミリ秒に変換して保存。"""
    try:
        val = float(fade_time_var.get())
        with config_lock:
            config["fade_ms"] = int(max(0.0, val) * 1000)
    except ValueError: pass
    save_config()

def update_sync_settings(*args):
    with config_lock:
        if 'sync_app_name_var' in globals():
            config["sync_app_name"] = sync_app_name_var.get()
        if 'sync_mode_var' in globals():
            config["sync_mode"] = sync_mode_var.get()
        try:
            if 'sync_strength_var' in globals():
                config["sync_strength"] = float(sync_strength_var.get()) / 100.0
            if 'sync_smoothness_var' in globals():
                config["sync_smoothness"] = float(sync_smoothness_var.get())
        except ValueError: pass

def update_region(event=None):
    selected = target_scene_var.get()
    anchor = region_anchor_var.get()
    try:
        w, h = int(region_width_var.get()), int(region_height_var.get())
    except ValueError: w, h = 0, 0
    
    with config_lock:
        if selected == "共通設定 (全てのシーンに適用)":
            config["region_anchor"], config["region_width"], config["region_height"] = anchor, w, h
        else:
            sid = selected.split(":")[0].strip()
            config.setdefault("scene_anchors", {})[sid] = anchor
            config.setdefault("scene_widths", {})[sid] = w
            config.setdefault("scene_heights", {})[sid] = h
    save_config()

def on_target_scene_change(event=None):
    selected = target_scene_var.get()
    with config_lock:
        if selected == "共通設定 (全てのシーンに適用)":
            region_anchor_var.set(config.get("region_anchor", "top_left"))
            region_width_var.set(str(config.get("region_width", 0)))
            region_height_var.set(str(config.get("region_height", 0)))
        else:
            sid = selected.split(":")[0].strip()
            region_anchor_var.set(config.get("scene_anchors", {}).get(sid, config["region_anchor"]))
            region_width_var.set(str(config.get("scene_widths", {}).get(sid, config["region_width"])))
            region_height_var.set(str(config.get("scene_heights", {}).get(sid, config["region_height"])))

# --- 画像処理 ---
def crop_image(image, anchor, width, height):
    if width <= 0 and height <= 0: return image
    ih, iw = image.shape[:2]
    w, h = min(width if width > 0 else iw, iw), min(height if height > 0 else ih, ih)
    x, y = 0, 0
    if anchor == "top_right": x = iw - w
    elif anchor == "bottom_left": y = ih - h
    elif anchor == "bottom_right": x, y = iw - w, ih - h
    elif anchor == "center": x, y = (iw - w) // 2, (ih - h) // 2
    return image[y:y+h, x:x+w]

def detect_scene(screen_gray, templates):
    with config_lock:
        base_anchor = config["region_anchor"]
        base_w = config["region_width"]
        base_h = config["region_height"]
        s_anchors = config.get("scene_anchors", {}).copy()
        s_widths = config.get("scene_widths", {}).copy()
        s_heights = config.get("scene_heights", {}).copy()
        threshold = config["match_threshold"]

    for tmpl in templates:
        sid = str(tmpl["id"])
        anchor = s_anchors.get(sid, base_anchor)
        w = s_widths.get(sid, base_w)
        h = s_heights.get(sid, base_h)
        
        try:
            cropped = crop_image(screen_gray, anchor, w, h)
            res = cv2.matchTemplate(cropped, tmpl["image"], cv2.TM_CCOEFF_NORMED)
            _, max_val, _, _ = cv2.minMaxLoc(res)
            if max_val >= threshold:
                log_debug("detect_scene", f"Scene {sid} matched ({max_val:.2f})")
                return tmpl
        except cv2.error:
            continue
    return None

def save_debug_screenshot():
    try:
        camera = bettercam.create(output_color="RGB")
        frame = camera.grab()
        camera.release()
        if frame is None: return
        bgr = cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
        
        with config_lock:
            selected = target_scene_var.get()
            if selected == "共通設定 (全てのシーンに適用)":
                anchor, w, h = config["region_anchor"], config["region_width"], config["region_height"]
            else:
                sid = selected.split(":")[0].strip()
                anchor = config.get("scene_anchors", {}).get(sid, config["region_anchor"])
                w, h = config.get("scene_widths", {}).get(sid, config["region_width"]), config.get("scene_heights", {}).get(sid, config["region_height"])
        
        cropped = crop_image(bgr, anchor, w, h)
        cv2.imwrite("debug_screenshot.png", cropped)
        messagebox.showinfo("保存完了", f"debug_screenshot.png を保存しました。")
    except Exception as e: messagebox.showerror("エラー", str(e))

# --- オーディオ・バックグラウンド ---
def get_scene_bgm_files(scene_id_or_default):
    files = []
    base = "default" if scene_id_or_default == "default" else f"scene{scene_id_or_default}"
    for d in [".", "bgm"]:
        if os.path.exists(d):
            for ext in (".mp3", ".ogg", ".wav", ".flac"):
                files.extend(glob.glob(os.path.join(d, f"{base}*{ext}")))
    return files

def change_bgm(current_bgm_id, new_scene):
    with config_lock:
        fade_ms = config["fade_ms"]
    
    new_id = "default" if new_scene is None else new_scene["id"]

    if current_bgm_id == new_id and pygame.mixer.music.get_busy(): return current_bgm_id
    pygame.mixer.music.fadeout(fade_ms)
    time.sleep(fade_ms / 1000.0)
    
    files = get_scene_bgm_files(new_id)
    if files:
        path = get_random_bgm(files)
        try:
            cached_io = load_cached_bgm(path)
            if isinstance(cached_io, io.BytesIO):
                pygame.mixer.music.load(cached_io, namehint=path)
            else:
                pygame.mixer.music.load(cached_io)
                
            apply_volumes(current_volume_modifier)
            pygame.mixer.music.play(0)
            return new_id
        except Exception as e:
            log_debug("change_bgm", f"Error loading {path}: {e}")
            return None
    return None

def find_app_peak_volume(app_name):
    if not HAS_PYCAW or not app_name: return 0.0
    try:
        sessions = AudioUtilities.GetAllSessions()
        for session in sessions:
            if session.Process and session.Process.name().lower() == app_name.lower():
                if hasattr(session, "_ctl"):
                    meter = session._ctl.QueryInterface(IAudioMeterInformation)
                    return meter.GetPeakValue() if meter else 0.0
    except Exception: pass
    return 0.0

def volume_sync_loop():
    global is_running, current_volume_modifier
    smoothed_peak = 0.0
    while is_running:
        with config_lock:
            mode = config.get("sync_mode", "None")
            app = config.get("sync_app_name", "").strip()
            strength = config.get("sync_strength", 0.5)
            smoothness = config.get("sync_smoothness", 5.0)

        if mode == "None" or not app or not HAS_PYCAW:
            if current_volume_modifier != 1.0:
                current_volume_modifier = 1.0
                apply_volumes(1.0)
            time.sleep(0.5); continue
        
        alpha = max(0.01, 1.0 / (smoothness * 4.0))
        peak = find_app_peak_volume(app)
        smoothed_peak = (alpha * peak) + ((1.0 - alpha) * smoothed_peak)
        
        if mode == "Ducking": modifier = 1.0 - (smoothed_peak * strength)
        elif mode == "Boost": modifier = (1.0 - strength) + (smoothed_peak * strength * 2.0)
        else: modifier = 1.0
        
        current_volume_modifier = max(0.0, min(2.0, modifier))
        apply_volumes(current_volume_modifier)
        try:
            if 'lbl_sync_status' in globals():
                root.after(0, lambda m=current_volume_modifier: lbl_sync_status.config(text=f"BGM倍率: {int(m * 100)}%"))
        except Exception: pass
        time.sleep(0.05)

def detection_loop():
    global is_running
    pygame.mixer.init(); pygame.mixer.set_num_channels(8)
    global ambient_channel; ambient_channel = pygame.mixer.Channel(7)
    templates = []
    for c in SCENE_CONFIG:
        img = cv2.imread(c["template"], cv2.IMREAD_GRAYSCALE)
        if img is not None: templates.append({"id": c["id"], "image": img})
    
    try:
        camera = bettercam.create(output_color="RGB")
        current_bgm_id = None
        last_matched_scene = None
        last_match_time = 0
        proc = psutil.Process(); proc.cpu_percent(None)
        fps_time, loops = time.time(), 0
        
        while is_running:
            frame = camera.grab()
            with config_lock:
                interval = config["check_interval_sec"]
                grace_time = config.get("grace_period_sec", 0.0)

            if frame is not None:
                current_time = time.time()
                scene = detect_scene(cv2.cvtColor(frame, cv2.COLOR_RGB2GRAY), templates)
                
                if scene:
                    last_matched_scene = scene
                    last_match_time = current_time
                    current_bgm_id = change_bgm(current_bgm_id, scene)
                else:
                    if last_matched_scene and (current_time - last_match_time) <= grace_time:
                        pass 
                    else:
                        last_matched_scene = None
                        current_bgm_id = change_bgm(current_bgm_id, None)
            
            loops += 1
            if time.time() - fps_time >= 1.0:
                fps = loops / (time.time() - fps_time)
                cpu = proc.cpu_percent() / psutil.cpu_count()
                rss = proc.memory_info().rss / (1024*1024)
                m_cache = sum(len(v) for v in bgm_cache.values()) / (1024*1024)
                root.after(0, lambda f=fps, c=cpu, r=rss, m=m_cache: 
                    lbl_fps.config(text=f"FPS: {f:.1f} / CPU: {c:.1f}% / MEM: {r:.0f}MB(Music:{m:.1f}MB)"))
                loops, fps_time = 0, time.time()
            
            for _ in range(int(interval * 10)):
                if not is_running: break
                time.sleep(0.1)
    finally:
        if camera: camera.release()

def toggle_running():
    global is_running, bgm_thread, sync_thread
    if not is_running:
        is_running = True
        btn_start_stop.config(text="■ 停止 (実行中)")
        bgm_thread = threading.Thread(target=detection_loop, daemon=True)
        sync_thread = threading.Thread(target=volume_sync_loop, daemon=True)
        bgm_thread.start()
        sync_thread.start()
    else:
        is_running = False
        btn_start_stop.config(text="停止中 (終了処理中...)")
        if bgm_thread: bgm_thread.join(timeout=1.5)
        if sync_thread: sync_thread.join(timeout=1.5)
        btn_start_stop.config(text="▶ 開始 (停止中)")
        bgm_cache.clear(); bgm_cache_order.clear(); ambient_sound_cache.clear(); ambient_cache_order.clear()
        gc.collect(); pygame.mixer.music.stop()
        if ambient_channel: ambient_channel.stop()
        lbl_fps.config(text=f"FPS: -- / CPU: 0.0% / MEM: {psutil.Process().memory_info().rss/(1024*1024):.0f}MB(Music:0.0MB)")
        if 'lbl_sync_status' in globals():
            lbl_sync_status.config(text="BGM倍率: 100%", foreground="green")

# --- UI構築 ---
def create_gui():
    global root, lbl_vol_val, lbl_thresh_val, lbl_interval_val, grace_period_var, fade_time_var
    global target_scene_var, region_anchor_var, region_width_var, region_height_var
    global sync_app_name_var, sync_mode_var, sync_strength_var, sync_smoothness_var, lbl_sync_status
    global btn_start_stop, lbl_fps
    load_config()
    root = tk.Tk(); root.title("Auto BGM Changer v0.3.3")
    root.minsize(520, 100); root.resizable(False, True) 
    
    main_f = ttk.Frame(root, padding=15); main_f.pack(fill=tk.BOTH, expand=True)
    ttk.Label(main_f, text="設定 / Settings", font=("Meiryo", 12, "bold")).pack(pady=(0, 10))

    # 音量設定
    vol_f = ttk.LabelFrame(main_f, text="音量設定", padding=5); vol_f.pack(fill=tk.X, pady=5)
    row_bgm = ttk.Frame(vol_f); row_bgm.pack(fill=tk.X, pady=2)
    ttk.Label(row_bgm, text="BGM:", width=10).pack(side=tk.LEFT)
    s_bgm = ttk.Scale(row_bgm, from_=0, to=100, orient=tk.HORIZONTAL, command=update_volume)
    s_bgm.set(config["global_volume"]*100); s_bgm.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
    s_bgm.bind("<ButtonRelease-1>", lambda e: save_config())
    lbl_vol_val = ttk.Label(row_bgm, text="", width=22, anchor=tk.E)
    lbl_vol_val.pack(side=tk.RIGHT)
    update_volume(config["global_volume"]*100)

    # 判定設定
    match_f = ttk.LabelFrame(main_f, text="判定の動作設定", padding=5); match_f.pack(fill=tk.X, pady=5)
    row1 = ttk.Frame(match_f); row1.pack(fill=tk.X, pady=2)
    ttk.Label(row1, text="厳しさ:", width=10).pack(side=tk.LEFT)
    s_th = ttk.Scale(row1, from_=50, to=100, orient=tk.HORIZONTAL, command=update_threshold)
    s_th.set(config["match_threshold"]*100); s_th.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
    s_th.bind("<ButtonRelease-1>", lambda e: save_config())
    lbl_thresh_val = ttk.Label(row1, text=f"{config['match_threshold']:.2f}", width=5); lbl_thresh_val.pack(side=tk.RIGHT)
    
    row2 = ttk.Frame(match_f); row2.pack(fill=tk.X, pady=2)
    ttk.Label(row2, text="監視間隔:", width=10).pack(side=tk.LEFT)
    s_int = ttk.Scale(row2, from_=0.1, to=10.0, orient=tk.HORIZONTAL, command=update_interval)
    s_int.set(config["check_interval_sec"]); s_int.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
    s_int.bind("<ButtonRelease-1>", lambda e: save_config())
    lbl_interval_val = ttk.Label(row2, text=f"{config['check_interval_sec']:.1f} 秒", width=6); lbl_interval_val.pack(side=tk.RIGHT)
    
    # 判定猶予とフェードアウト時間を横並びに配置
    row3 = ttk.Frame(match_f); row3.pack(fill=tk.X, pady=2)
    ttk.Label(row3, text="判定猶予(秒):", width=12).pack(side=tk.LEFT)
    grace_period_var = tk.StringVar(value=str(config["grace_period_sec"]))
    ge = ttk.Entry(row3, textvariable=grace_period_var, width=6); ge.pack(side=tk.LEFT); ge.bind("<FocusOut>", update_grace_period)
    
    ttk.Label(row3, text="フェード(秒):", width=12).pack(side=tk.LEFT, padx=(15, 0))
    fade_time_var = tk.StringVar(value=str(config["fade_ms"] / 1000.0))
    fe = ttk.Entry(row3, textvariable=fade_time_var, width=6); fe.pack(side=tk.LEFT); fe.bind("<FocusOut>", update_fade_time)

    # シーン個別範囲
    reg_f = ttk.LabelFrame(main_f, text="判定範囲の個別設定 (シーン単位)", padding=5); reg_f.pack(fill=tk.X, pady=5)
    target_scene_var = tk.StringVar(value="共通設定 (全てのシーンに適用)")
    scenes = ["共通設定 (全てのシーンに適用)"] + [f"{c['id']}: {os.path.basename(c['template'])}" for c in SCENE_CONFIG]
    cb = ttk.Combobox(reg_f, textvariable=target_scene_var, values=scenes, state="readonly"); cb.pack(fill=tk.X, pady=2); cb.bind("<<ComboboxSelected>>", on_target_scene_change)
    
    anc_f = ttk.Frame(reg_f); anc_f.pack(fill=tk.X, pady=2)
    region_anchor_var = tk.StringVar(value=config["region_anchor"])
    for t, v in [("左上","top_left"), ("右上","top_right"), ("左下","bottom_left"), ("右下","bottom_right"), ("中央","center")]:
        ttk.Radiobutton(anc_f, text=t, variable=region_anchor_var, value=v, command=update_region).pack(side=tk.LEFT, padx=3)
        
    sz_f = ttk.Frame(reg_f); sz_f.pack(fill=tk.X, pady=2)
    region_width_var, region_height_var = tk.StringVar(value=str(config["region_width"])), tk.StringVar(value=str(config["region_height"]))
    ttk.Label(sz_f, text="W:").pack(side=tk.LEFT); ttk.Entry(sz_f, textvariable=region_width_var, width=6).pack(side=tk.LEFT, padx=2)
    ttk.Label(sz_f, text="高さ(H):").pack(side=tk.LEFT); ttk.Entry(sz_f, textvariable=region_height_var, width=6).pack(side=tk.LEFT, padx=2)
    for ev in [region_width_var, region_height_var]: ev.trace_add("write", lambda *a: update_region())
    ttk.Button(reg_f, text="デバッグ撮影 (選択中の設定を使用)", command=save_debug_screenshot).pack(fill=tk.X, pady=2)

    # Auto Volume Sync
    sync_f = ttk.LabelFrame(main_f, text="自動音量調整 (Auto Volume Sync)", padding=5); sync_f.pack(fill=tk.X, pady=5)
    if not HAS_PYCAW: ttk.Label(sync_f, text="※要 pycaw", foreground="red").pack()
    row_s1 = ttk.Frame(sync_f); row_s1.pack(fill=tk.X)
    ttk.Label(row_s1, text="EXE名:").pack(side=tk.LEFT)
    sync_app_name_var = tk.StringVar(value=config["sync_app_name"])
    sa = ttk.Entry(row_s1, textvariable=sync_app_name_var, width=12); sa.pack(side=tk.LEFT, padx=5); sa.bind("<FocusOut>", update_sync_settings)
    sync_mode_var = tk.StringVar(value=config["sync_mode"])
    sm = ttk.Combobox(row_s1, textvariable=sync_mode_var, values=["None", "Ducking", "Boost"], state="readonly", width=8); sm.pack(side=tk.LEFT); sm.bind("<<ComboboxSelected>>", update_sync_settings)
    lbl_sync_status = ttk.Label(row_s1, text="BGM倍率: 100%", foreground="green", width=12, anchor=tk.E); lbl_sync_status.pack(side=tk.RIGHT)
    
    row_s2 = ttk.Frame(sync_f); row_s2.pack(fill=tk.X, pady=2)
    sync_strength_var, sync_smoothness_var = tk.StringVar(value=str(int(config["sync_strength"]*100))), tk.StringVar(value=str(config["sync_smoothness"]))
    ttk.Label(row_s2, text="振幅%:").pack(side=tk.LEFT)
    s_sync_str = ttk.Scale(row_s2, from_=0, to=100, command=lambda v: [sync_strength_var.set(str(int(float(v)))), update_sync_settings()])
    s_sync_str.set(config["sync_strength"]*100); s_sync_str.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
    s_sync_str.bind("<ButtonRelease-1>", lambda e: save_config())
    ttk.Label(row_s2, textvariable=sync_strength_var, width=3).pack(side=tk.LEFT)
    ttk.Label(row_s2, text="滑らかさ:").pack(side=tk.LEFT)
    s_sync_smo = ttk.Scale(row_s2, from_=1, to=20, command=lambda v: [sync_smoothness_var.set(f"{float(v):.1f}"), update_sync_settings()])
    s_sync_smo.set(config["sync_smoothness"]); s_sync_smo.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
    s_sync_smo.bind("<ButtonRelease-1>", lambda e: save_config())
    ttk.Label(row_s2, textvariable=sync_smoothness_var, width=4).pack(side=tk.LEFT)

    btn_start_stop = ttk.Button(main_f, text="▶ 開始 (停止中)", command=toggle_running); btn_start_stop.pack(fill=tk.X, pady=10)
    lbl_fps = ttk.Label(main_f, text="FPS: -- / CPU: 0.0% / MEM: --MB", foreground="gray"); lbl_fps.pack(side=tk.RIGHT)

    if HAS_THEME_LIBS:
        theme = darkdetect.theme(); sv_ttk.set_theme(theme)
        if theme == "Dark":
            try:
                import ctypes; root.update_idletasks() 
                hwnd = ctypes.windll.user32.GetParent(root.winfo_id())
                ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 20, ctypes.byref(ctypes.c_int(1)), 4)
            except Exception: pass
    root.mainloop()

if __name__ == "__main__":
    os.makedirs("bgm", exist_ok=True); os.makedirs("target", exist_ok=True); os.makedirs("amb", exist_ok=True)
    create_gui()