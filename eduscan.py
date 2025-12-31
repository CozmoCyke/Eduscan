import os
import sys
import tempfile
import zipfile
import subprocess
import re
import unicodedata
import requests
import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter.scrolledtext import ScrolledText
from tkinter import ttk
import io
import time

from pdf2image import convert_from_path
import pytesseract
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4
from reportlab.lib.utils import ImageReader
from docx import Document
import language_tool_python
from spellchecker import SpellChecker
from google.cloud import vision
from PyPDF2 import PdfReader
from PyPDF2.generic import IndirectObject
from PIL import Image, ImageTk  # ← Image ajouté

# ─────────────────────────────────────────
# CONFIG TESSERACT (décommente si besoin)
# ─────────────────────────────────────────
# pytesseract.pytesseract.tesseract_cmd = r"C:\Program Files\Tesseract-OCR\tesseract.exe"

# LanguageTool
tool = language_tool_python.LanguageTool("fr")

# Correcteur lexical FR
spell = SpellChecker(language="fr")

# Mots protégés
PROTECTED_WORDS = {
    "doppler",
    "tsunami",
    "uaa",
    "oscillogramme",
    "foudre",
    "sismique",
}

for w in PROTECTED_WORDS:
    spell.word_frequency.add(w)

# Log des corrections lexicales
correction_log = []

POPPLER_CACHE_DIR_NAME = "poppler-windows"
POPPLER_BIN_CACHE_FILE = "poppler_bin_path.txt"

# État courant
current_pdf_path = None
current_page_image = None  # PhotoImage pour le label
current_pdf_type = None    # "native", "image_only", "searchable", "unknown"

# Gestion multi-pages (progressif)
page_images = []           # list[PhotoImage], une par page
current_page_index = 1     # 1-based
integrated_page_texts = [] # list[str], texte intégré par page

# Cache d’images extraites du PDF : liste de (page_index, tk_image)
pdf_images_cache = []

# Onglets : clé → {"frame": frame, "text": text_widget, "title": title}
tabs = {}
page_tabs_content = {}  # page_index -> { key: {"title": str, "content": str} }
page_best_texts = {}    # page_index -> str
winner_tab_key = None  # onglet actuellement marqué comme "meilleur"

# ─────────────────────────────────────────
# UTILITAIRES TEXTE
# ─────────────────────────────────────────

def levenshtein(a: str, b: str) -> int:
    if a == b:
        return 0
    if abs(len(a) - len(b)) > 3:
        return 999
    dp = list(range(len(b) + 1))
    for i, ca in enumerate(a, start=1):
        prev = dp[0]
        dp[0] = i
        for j, cb in enumerate(b, start=1):
            temp = dp[j]
            if ca == cb:
                dp[j] = prev
            else:
                dp[j] = 1 + min(prev, dp[j], dp[j - 1])
            prev = temp
    return dp[-1]


def smart_clean(text: str) -> str:
    # Normalisation des accents et apostrophes
    text = unicodedata.normalize("NFC", text)
    text = text.replace("’", "'").replace("‘", "'")
    text = text.replace("''", "'")      # d''acuité -> d'acuité
    text = text.replace("’'", "'")
    text = text.replace("{f", "")

    # ⚠ IMPORTANT : on ne touche PLUS aux retours à la ligne
    text = re.sub(r"[ \t]{2,}", " ", text)

    # Corrections OCR spécifiques repérées dans tes scans
    text = text.replace("pourlesquels", "pour lesquels")
    text = text.replace(" sismique.", " sismiques.")

    return text.strip(" \t")


def dict_clean(text: str, stage: str = "", mode: str = "doux") -> str:
    """
    Correction lexicale avec dictionnaire FR.
    mode = "doux"  → distance 1 maximum
    mode = "agressif" → distance 2 maximum
    """
    global correction_log

    max_dist = 1 if mode == "doux" else 2

    def fix_word(token: str) -> str:
        if not re.search(r"[A-Za-zÀ-ÖØ-öø-ÿ]", token):
            return token

        prefix = re.match(r"^\W*", token, flags=re.UNICODE).group(0)
        suffix = re.search(r"\W*$", token, flags=re.UNICODE).group(0)
        core = token[len(prefix):len(token) - len(suffix)]

        if not core:
            return token

        if re.search(r"\d", core):
            return token

        lower = core.lower()

        if lower in PROTECTED_WORDS:
            return token

        if len(core) <= 3:
            return token

        if core[0].isupper():
            return token

        if lower in spell:
            return token

        candidate = spell.correction(lower)
        if not candidate:
            return token

        dist = levenshtein(lower, candidate)
        if dist > max_dist:
            return token

        corrected_core = candidate
        corrected = prefix + corrected_core + suffix

        if corrected != token:
            entry = (stage, core, corrected_core)
            if entry not in correction_log:
                correction_log.append(entry)

        return corrected

    tokens = re.findall(r"\w+|\W+", text, flags=re.UNICODE)
    tokens = [fix_word(t) for t in tokens]
    return "".join(tokens)


def clean_text(text: str, stage: str) -> str:
    """
    Pipeline de nettoyage :
      - smart_clean (apostrophes, espaces, petites erreurs OCR)
      - dict_clean optionnel selon auto_lexical_correction + mode doux/agressif
    """
    global correction_log
    correction_log = []

    t = smart_clean(text)

    if auto_lexical_correction.get():
        mode = cleaning_mode.get()  # "doux" ou "agressif"
        t = dict_clean(t, stage=stage, mode=mode)
    else:
        mode = None

    if correction_log and auto_lexical_correction.get():
        print(f"\n[LOG] Corrections lexicales ({stage}) [mode={mode}] :")
        for st, orig, corr in correction_log:
            print(f" - [{st}] {orig} → {corr}")
    elif auto_lexical_correction.get():
        print(f"\n[LOG] Aucune correction lexicale pour le stage {stage}.")
    else:
        print(f"\n[LOG] Correction lexicale désactivée pour le stage {stage}.")

    return t

# ─────────────────────────────────────────
# MÉTRIQUE QUALITÉ TEXTE
# ─────────────────────────────────────────

def estimate_text_quality(text: str):
    """
    Estime la qualité d’un texte OCR :
    - nb de mots
    - ratio de mots “inconnus”
    - ratio de caractères bizarres
    - score global (plus grand = meilleur)
    """
    words = re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ'-]+", text)
    total_words = len(words)

    if total_words == 0:
        return {
            "words": 0,
            "bad_words": 0,
            "bad_ratio": 1.0,
            "noise_ratio": 1.0,
            "score": 0.0,
        }

    bad = 0
    for w in words:
        lw = w.lower()

        if lw in PROTECTED_WORDS:
            continue
        if len(lw) <= 2:
            continue
        if any(c.isdigit() for c in lw):
            continue
        if w[0].isupper():
            continue

        if lw not in spell:
            bad += 1

    bad_ratio = bad / total_words

    weird_chars = re.findall(r"[^A-Za-z0-9À-ÖØ-öø-ÿ\s.,;:!?()'\"-]", text)
    noise_ratio = len(weird_chars) / max(1, len(text))

    good_words = total_words - bad

    penalty = 1.0
    penalty *= (1.0 - min(0.7, bad_ratio))
    penalty *= (1.0 - min(0.7, noise_ratio * 5))

    score = max(0.0, good_words * penalty)

    return {
        "words": total_words,
        "bad_words": bad,
        "bad_ratio": bad_ratio,
        "noise_ratio": noise_ratio,
        "score": score,
    }

# ─────────────────────────────────────────
# POPPLER
# ─────────────────────────────────────────

def get_script_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))


def save_poppler_bin_path(bin_path, cache_file):
    os.makedirs(os.path.dirname(cache_file), exist_ok=True)
    with open(cache_file, "w", encoding="utf-8") as f:
        f.write(bin_path)


def find_poppler_bin(root_dir):
    for dirpath, dirnames, filenames in os.walk(root_dir):
        if os.path.basename(dirpath).lower() == "bin":
            return dirpath
    return None


def download_and_extract_poppler(target_dir):
    print("Téléchargement de Poppler Windows 64 bits…")
    api_url = "https://api.github.com/repos/oschwartz10612/poppler-windows/releases/latest"
    headers = {"User-Agent": "python-ocr-poppler-installer"}

    resp = requests.get(api_url, headers=headers, timeout=60)
    resp.raise_for_status()
    release = resp.json()
    assets = release.get("assets", [])

    asset_zip = None
    for a in assets:
        name = a.get("name", "").lower()
        if "win64" in name and name.endswith(".zip"):
            asset_zip = a
            break
    if asset_zip is None:
        for a in assets:
            name = a.get("name", "").lower()
            if name.endswith(".zip"):
                asset_zip = a
                break
    if asset_zip is None:
        raise RuntimeError("Aucun asset .zip trouvé pour Poppler.")

    download_url = asset_zip["browser_download_url"]
    os.makedirs(target_dir, exist_ok=True)

    with tempfile.TemporaryDirectory() as tmpdir:
        zip_path = os.path.join(tmpdir, "poppler.zip")
        with requests.get(download_url, stream=True, timeout=300) as r:
            r.raise_for_status()
            with open(zip_path, "wb") as f:
                for chunk in r.iter_content(chunk_size=8192):
                    if chunk:
                        f.write(chunk)

        with zipfile.ZipFile(zip_path, "r") as zf:
            zf.extractall(target_dir)

    bin_path = find_poppler_bin(target_dir)
    return bin_path


def ensure_poppler():
    base_dir = get_script_dir()
    cache_dir = os.path.join(base_dir, POPPLER_CACHE_DIR_NAME)
    cache_file = os.path.join(base_dir, POPPLER_BIN_CACHE_FILE)

    if os.path.exists(cache_file):
        with open(cache_file, "r", encoding="utf-8") as f:
            bin_path = f.read().strip()
        if os.path.isdir(bin_path):
            return bin_path

    if os.path.isdir(cache_dir):
        bin_path = find_poppler_bin(cache_dir)
        if bin_path:
            save_poppler_bin_path(bin_path, cache_file)
            return bin_path

    bin_path = download_and_extract_poppler(cache_dir)
    if not bin_path:
        raise RuntimeError("Poppler téléchargé mais dossier bin introuvable.")
    save_poppler_bin_path(bin_path, cache_file)
    return bin_path

# ─────────────────────────────────────────
# TESSDATA FR
# ─────────────────────────────────────────

def detect_tessdata_dir():
    cmd = getattr(pytesseract.pytesseract, "tesseract_cmd", None)
    if cmd and os.path.isfile(cmd):
        base = os.path.dirname(cmd)
        td = os.path.join(base, "tessdata")
        if os.path.isdir(td):
            return td

    try:
        if os.name == "nt":
            out = subprocess.check_output(["where", "tesseract"], encoding="utf-8", stderr=subprocess.STDOUT)
            first = out.splitlines()[0].strip('" \n\r')
            if os.path.isfile(first):
                base = os.path.dirname(first)
                td = os.path.join(base, "tessdata")
                if os.path.isdir(td):
                    return td
    except Exception:
        pass

    candidates = [
        r"C:\Program Files\Tesseract-OCR\tessdata",
        r"C:\Program Files (x86)\Tesseract-OCR\tessdata",
    ]
    for c in candidates:
        if os.path.isdir(c):
            return c

    return None


def ensure_fra_traineddata():
    tessdata_dir = detect_tessdata_dir()
    if not tessdata_dir:
        raise RuntimeError(
            "Impossible de localiser le dossier 'tessdata' de Tesseract.\n"
            "Vérifie que Tesseract est bien installé."
        )

    fra_path = os.path.join(tessdata_dir, "fra.traineddata")
    if os.path.isfile(fra_path):
        return fra_path

    os.makedirs(tessdata_dir, exist_ok=True)

    url = "https://github.com/tesseract-ocr/tessdata/raw/main/fra.traineddata"
    try:
        print(f"Téléchargement de fra.traineddata dans {tessdata_dir}…")
        resp = requests.get(url, stream=True, timeout=300)
        resp.raise_for_status()
        with open(fra_path, "wb") as f:
            for chunk in resp.iter_content(chunk_size=8192):
                if chunk:
                    f.write(chunk)
    except Exception as e:
        raise RuntimeError(f"Échec du téléchargement de fra.traineddata : {e}")

    return fra_path

# ─────────────────────────────────────────
# VISION
# ─────────────────────────────────────────

def ocr_image_vision(path: str) -> str:
    client = vision.ImageAnnotatorClient()

    with io.open(path, "rb") as image_file:
        content = image_file.read()

    if len(content) == 0:
        raise RuntimeError("Fichier image vide, rien à envoyer à Vision.")

    image = vision.Image(content=content)
    response = client.document_text_detection(image=image)

    if response.error.message:
        raise RuntimeError(f"Vision API error: {response.error.message}")

    return response.full_text_annotation.text

# ─────────────────────────────────────────
# NAVIGATION PAGES (préparation multi-pages)
# ─────────────────────────────────────────

def update_page_nav_label():
    total_pages = len(page_images) if page_images else len(integrated_page_texts)
    if total_pages <= 0:
        page_nav_label.config(text="Page 0/0")
        return
    page_nav_label.config(text=f"Page {current_page_index}/{total_pages}")


def show_page(page_index: int):
    global current_page_index, current_page_image
    total_pages = len(page_images) if page_images else len(integrated_page_texts)
    if total_pages <= 0:
        update_page_nav_label()
        return

    page_index = max(1, min(page_index, total_pages))
    current_page_index = page_index

    if page_images and 1 <= page_index <= len(page_images):
        current_page_image = page_images[page_index - 1]
        pdf_image_label.configure(image=current_page_image)

    update_page_nav_label()


def go_first_page():
    show_page(1)


def go_prev_page():
    show_page(current_page_index - 1)


def go_next_page():
    show_page(current_page_index + 1)


def go_last_page():
    total_pages = len(page_images) if page_images else len(integrated_page_texts)
    if total_pages <= 0:
        show_page(1)
        return
    show_page(total_pages)

# ─────────────────────────────────────────
# UI PRINCIPALE
# ─────────────────────────────────────────

root = tk.Tk()
root.title("Eduscan v2.3 – Comparateur OCR (Scanner + Tesseract + Vision + Corrections)")
root.geometry("1300x750")

status_var = tk.StringVar()
status_var.set("Prêt – Eduscan v2.3")
status_bar = tk.Label(root, textvariable=status_var, anchor="w", relief=tk.SUNKEN)
status_bar.pack(side=tk.BOTTOM, fill=tk.X)

# Option : créer deux onglets (brut + nettoyé) pour l’OCR
create_raw_and_clean = tk.BooleanVar(value=True)

# Mode de nettoyage : "doux" (distance 1) ou "agressif" (distance 2)
cleaning_mode = tk.StringVar(value="doux")

# Correction lexicale automatique après le nettoyage
auto_lexical_correction = tk.BooleanVar(value=True)

# Split horizontal : gauche image / droite onglets
main_pane = ttk.Panedwindow(root, orient=tk.HORIZONTAL)
main_pane.pack(fill=tk.BOTH, expand=True)

left_frame = tk.Frame(main_pane, width=500, bg="grey")
right_frame = tk.Frame(main_pane)

main_pane.add(left_frame, weight=1)
main_pane.add(right_frame, weight=2)

# Image du PDF à gauche
pdf_image_label = tk.Label(left_frame, bg="black")
pdf_image_label.pack(fill=tk.BOTH, expand=True)

# Barre de navigation pages (préparation multi-pages)
nav_frame = tk.Frame(left_frame, bg="grey")
nav_frame.pack(fill=tk.X, pady=4)

btn_first_page = tk.Button(nav_frame, text="⏮", width=3, command=lambda: go_first_page())
btn_prev_page = tk.Button(nav_frame, text="◀", width=3, command=lambda: go_prev_page())
btn_next_page = tk.Button(nav_frame, text="▶", width=3, command=lambda: go_next_page())
btn_last_page = tk.Button(nav_frame, text="⏭", width=3, command=lambda: go_last_page())

btn_first_page.pack(side=tk.LEFT, padx=2)
btn_prev_page.pack(side=tk.LEFT, padx=2)

page_nav_label = tk.Label(nav_frame, text="Page 0/0", bg="grey")
page_nav_label.pack(side=tk.LEFT, padx=8)

btn_next_page.pack(side=tk.LEFT, padx=2)
btn_last_page.pack(side=tk.LEFT, padx=2)

# Notebook à droite
notebook = ttk.Notebook(right_frame)
notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

# ─────────────────────────────────────────
# GESTION DES ONGLETS
# ─────────────────────────────────────────

def clear_all_tabs():
    global tabs, winner_tab_key
    for info in list(tabs.values()):
        notebook.forget(info["frame"])
    tabs.clear()
    winner_tab_key = None


def set_tab(key: str, title: str, content: str):
    """
    Crée ou met à jour un onglet identifié par 'key'.
    Affiche un petit ✖ dans le titre.
    Et lance automatiquement la comparaison des versions en mode silencieux.
    """
    global tabs
    display_title = f"{title} ✖"

    if key in tabs:
        txt = tabs[key]["text"]
        tabs[key]["title"] = title
        idx = notebook.index(tabs[key]["frame"])
        notebook.tab(idx, text=display_title)
        txt.config(state=tk.NORMAL, bg="white")
        txt.delete("1.0", tk.END)
        txt.insert(tk.END, content)
        txt.config(state=tk.NORMAL)
        notebook.select(tabs[key]["frame"])
    else:
        frame = tk.Frame(notebook)
        txt = ScrolledText(frame, wrap=tk.WORD, font=("Consolas", 10), bg="white")
        txt.pack(fill=tk.BOTH, expand=True)
        txt.insert(tk.END, content)
        notebook.add(frame, text=display_title)
        tabs[key] = {"frame": frame, "text": txt, "title": title}
        notebook.select(frame)

    comparer_versions(show_dialog=False)


def get_active_text_widget():
    tab_id = notebook.select()
    if not tab_id:
        return None
    for info in tabs.values():
        if str(info["frame"]) == str(tab_id):
            return info["text"]
    return None


def get_active_tab_key():
    tab_id = notebook.select()
    if not tab_id:
        return None
    for key, info in tabs.items():
        if str(info["frame"]) == str(tab_id):
            return key
    return None


def close_tab_event(event):
    """
    Ferme un onglet sur clic du milieu ou clic droit,
    puis recalcule la numérotation et le meilleur onglet.
    """
    global winner_tab_key

    try:
        idx = notebook.index(f"@{event.x},{event.y}")
    except tk.TclError:
        return

    tab_id = notebook.tabs()[idx]
    deleted_key = None

    for key, info in list(tabs.items()):
        if str(info["frame"]) == str(tab_id):
            notebook.forget(info["frame"])
            del tabs[key]
            deleted_key = key
            if winner_tab_key == key:
                winner_tab_key = None
            break

    # Renumérotation / recomparaison si des onglets restent
    if tabs:
        comparer_versions(show_dialog=False)

notebook.bind("<Button-2>", close_tab_event)
notebook.bind("<Button-3>", close_tab_event)

# ─────────────────────────────────────────
# DÉTECTION TYPE DE PDF
# ─────────────────────────────────────────

def detect_pdf_type(pdf_path: str) -> str:
    """
    Essaie de distinguer :
      - "native"     : PDF texte vectoriel (Word, LaTeX, etc.)
      - "searchable" : PDF scanné avec image + couche texte OCR
      - "image_only" : PDF scanné sans aucun texte
      - "unknown"    : si on n’arrive pas à décider
    """
    text_found = False
    image_found = False

    try:
        reader = PdfReader(pdf_path)
        for page in reader.pages:
            t = page.extract_text() or ""
            if t.strip():
                text_found = True

            resources = page.get("/Resources")

            try:
                if isinstance(resources, IndirectObject):
                    resources = resources.get_object()
            except Exception:
                pass

            if isinstance(resources, dict):
                xObject = resources.get("/XObject")
                if xObject:
                    try:
                        if isinstance(xObject, IndirectObject):
                            xObject = xObject.get_object()
                    except Exception:
                        pass

                    if isinstance(xObject, dict):
                        for obj in xObject.values():
                            try:
                                if isinstance(obj, IndirectObject):
                                    obj = obj.get_object()
                            except Exception:
                                pass

                            if hasattr(obj, "get"):
                                subtype = obj.get("/Subtype")
                                if subtype == "/Image":
                                    image_found = True
                                    break

            if text_found and image_found:
                break

    except Exception as e:
        print(f"[DEBUG] detect_pdf_type error: {e}")
        return "unknown"

    if text_found and not image_found:
        return "native"
    if text_found and image_found:
        return "searchable"
    if not text_found and image_found:
        return "image_only"
    return "unknown"

# ─────────────────────────────────────────
# EXTRACTION D’IMAGES PDF + FENÊTRE D’APERÇU
# ─────────────────────────────────────────

def extract_pdf_images(pdf_path: str):
    """
    Extrait les images du PDF et les stocke dans pdf_images_cache
    sous forme de (page_index, tk_image).
    """
    global pdf_images_cache
    pdf_images_cache.clear()
    count = 0

    try:
        reader = PdfReader(pdf_path)
        for page_index, page in enumerate(reader.pages):
            resources = page.get("/Resources")
            try:
                if isinstance(resources, IndirectObject):
                    resources = resources.get_object()
            except Exception:
                pass

            if not isinstance(resources, dict):
                continue

            xObject = resources.get("/XObject")
            if not xObject:
                continue

            try:
                if isinstance(xObject, IndirectObject):
                    xObject = xObject.get_object()
            except Exception:
                pass

            if not isinstance(xObject, dict):
                continue

            for obj in xObject.values():
                try:
                    if isinstance(obj, IndirectObject):
                        obj = obj.get_object()
                except Exception:
                    continue

                if not hasattr(obj, "get"):
                    continue

                subtype = obj.get("/Subtype")
                if subtype != "/Image":
                    continue

                try:
                    data = obj.get_data()
                except Exception:
                    try:
                        data = obj._data
                    except Exception:
                        continue

                try:
                    img = Image.open(io.BytesIO(data))
                    img.thumbnail((300, 300))
                    tk_img = ImageTk.PhotoImage(img)
                    pdf_images_cache.append((page_index + 1, tk_img))
                    count += 1
                except Exception:
                    continue

        print(f"[DEBUG] extract_pdf_images : {count} image(s) trouvée(s)")
    except Exception as e:
        print(f"[DEBUG] extract_pdf_images error: {e}")

    return pdf_images_cache


def show_pdf_images_window():
    """
    Affiche les images extraites dans une fenêtre séparée (scrollable).
    """
    if not current_pdf_path:
        messagebox.showerror("Images PDF", "Aucun PDF chargé.")
        return

    if not pdf_images_cache:
        try:
            extract_pdf_images(current_pdf_path)
        except Exception as e:
            messagebox.showerror("Images PDF", f"Erreur lors de l’extraction des images :\n{e}")
            return

    if not pdf_images_cache:
        messagebox.showinfo("Images PDF", "Aucune image détectée dans ce PDF.")
        return

    win = tk.Toplevel(root)
    win.title("Images extraites du PDF")
    win.geometry("600x400")

    canvas_w = tk.Canvas(win)
    scrollbar = tk.Scrollbar(win, orient="vertical", command=canvas_w.yview)
    frame = tk.Frame(canvas_w)

    frame.bind(
        "<Configure>",
        lambda e: canvas_w.configure(scrollregion=canvas_w.bbox("all"))
    )

    canvas_w.create_window((0, 0), window=frame, anchor="nw")
    canvas_w.configure(yscrollcommand=scrollbar.set)

    canvas_w.pack(side="left", fill="both", expand=True)
    scrollbar.pack(side="right", fill="y")

    for idx, (page_index, img) in enumerate(pdf_images_cache, start=1):
        lbl = tk.Label(frame, text=f"Page {page_index} – image {idx}", anchor="w")
        lbl.pack(fill="x", padx=5, pady=(8, 0))

        img_label = tk.Label(frame, image=img)
        img_label.image = img  # garder la référence
        img_label.pack(padx=10, pady=4)

# ─────────────────────────────────────────
# TITRE DE FENÊTRE DYNAMIQUE
# ─────────────────────────────────────────

def format_pdf_type_label(pdf_type: str | None, nb_images: int) -> str:
    if pdf_type == "native":
        base = "pdf/native"
    elif pdf_type == "searchable":
        base = "pdf/searchable"
    elif pdf_type == "image_only":
        base = "pdf/image-only"
    elif pdf_type == "unknown":
        base = "pdf/unknown"
    else:
        base = "aucun PDF"

    if nb_images > 1:
        return f"{base}, {nb_images} images"
    return base


def update_window_title():
    if not current_pdf_path:
        root.title("Eduscan v2.3 – Comparateur OCR (Scanner + Tesseract + Vision + Corrections)")
        return

    pdf_type = current_pdf_type or "unknown"
    nb_images = len(pdf_images_cache)
    label = format_pdf_type_label(pdf_type, nb_images)
    fname = os.path.basename(current_pdf_path)

    root.title(
        f"{fname} ({label}) – Eduscan v2.3 – Comparateur OCR (Scanner + Tesseract + Vision + Corrections)"
    )

# ─────────────────────────────────────────
# FONCTIONS PRINCIPALES
# ─────────────────────────────────────────

def analyser_pdf():
    """
    Charge un PDF :
    - efface les onglets existants
    - affiche 1ʳᵉ page en image
    - extrait texte intégré
    - détecte natif / searchable / image-only
    - compte les images et affiche une fenêtre d’aperçu si > 1
    """
    global current_pdf_path, current_page_image, current_pdf_type
    global page_images, current_page_index, integrated_page_texts
    global page_tabs_content, page_best_texts

    pdf_path = filedialog.askopenfilename(
        filetypes=[("PDF Files", "*.pdf")],
        title="Choisis un PDF à analyser"
    )
    if not pdf_path:
        return

    clear_all_tabs()
    page_tabs_content.clear()
    page_best_texts.clear()
    current_pdf_path = pdf_path
    page_images = []
    integrated_page_texts = []
    current_page_index = 1

    pdf_type = detect_pdf_type(pdf_path)
    current_pdf_type = pdf_type

    # Extraction des images pour comptage + éventuel aperçu
    try:
        images = extract_pdf_images(pdf_path)
        nb_images = len(images)
    except Exception as e:
        print(f"[DEBUG] erreur lors de extract_pdf_images dans analyser_pdf : {e}")
        nb_images = 0

    # Aperçu visuel : charger toutes les pages en images (multi-pages)
    global page_images, current_page_image, current_page_index

    try:
        poppler_bin = ensure_poppler()
        pages = convert_from_path(pdf_path, 150, poppler_path=poppler_bin)
        if not pages:
            raise RuntimeError("Aucune page dans le PDF ?")
    except Exception as e:
        messagebox.showerror("Aperçu PDF", f"Impossible de lire le PDF :\n{e}")
        return

    # Préparer les images redimensionnées pour chaque page
    page_images = []
    max_width, max_height = 600, 700

    for img in pages:
        w, h = img.size
        scale = min(max_width / w, max_height / h, 1.0)
        if scale < 1.0:
            img = img.resize((int(w * scale), int(h * scale)))
        tk_img = ImageTk.PhotoImage(img)
        page_images.append(tk_img)

    # Afficher la première page si disponible
    if page_images:
        current_page_index = 1
        current_page_image = page_images[0]
        pdf_image_label.configure(image=current_page_image)
        update_page_nav_label()

    # Texte intégré
    text_integrated = ""
    try:
        reader = PdfReader(pdf_path)
        for page in reader.pages:
            t = page.extract_text() or ""
            integrated_page_texts.append(t)
            text_integrated += t + "\n\n"
    except Exception as e:
        text_integrated = f"[Erreur lors de l’extraction du texte intégré : {e}]"
        integrated_page_texts = []

    text_integrated = text_integrated.strip()
    if text_integrated:
        if pdf_type == "native":
            tab_title = "Texte intégré (PDF natif)"
        elif pdf_type == "searchable":
            tab_title = "Texte intégré (searchable)"
        else:
            tab_title = "Texte intégré (scanner)"

        set_tab("integrated", tab_title, text_integrated)
    else:
        set_tab(
            "integrated",
            "Texte intégré (aucun)",
            "[Aucun texte intégré détecté – PDF probablement image-only]"
        )

    # Message de statut + images
    if pdf_type == "native":
        status_var.set(
            f"PDF analysé : PDF natif (texte vectoriel). "
            f"Idéal pour export avancé (Pandoc, etc.). Images détectées : {nb_images}."
        )
    elif pdf_type == "searchable":
        status_var.set(
            f"PDF analysé : PDF scanné avec couche texte OCR (searchable). "
            f"Images détectées : {nb_images}."
        )
    elif pdf_type == "image_only":
        status_var.set(
            f"PDF analysé : PDF scanné image-only (aucune couche texte). "
            f"Utilise Tesseract ou Vision pour récupérer le texte. Images détectées : {nb_images}."
        )
    else:
        status_var.set(
            f"PDF analysé : type non déterminé (unknown). "
            f"Images détectées : {nb_images}."
        )

    update_page_nav_label()

    # Afficher les images dans une fenêtre séparée seulement s'il y en a PLUS d'une
    if nb_images > 1:
        show_pdf_images_window()

    # Mettre à jour le titre de fenêtre avec type + nb images
    update_window_title()


def ocr_tesseract():
    """
    OCR Tesseract sur le PDF courant (ou demander un PDF si aucun chargé).
    """
    global current_pdf_path

    if not current_pdf_path:
        pdf_path = filedialog.askopenfilename(
            filetypes=[("PDF Files", "*.pdf")],
            title="Choisis un PDF pour OCR Tesseract"
        )
        if not pdf_path:
            return
        current_pdf_path = pdf_path

    try:
        poppler_bin = ensure_poppler()
    except Exception as e:
        messagebox.showerror("Poppler", f"Impossible d’installer/utiliser Poppler :\n{e}")
        return

    try:
        ensure_fra_traineddata()
    except Exception as e:
        messagebox.showerror("Tesseract (fra)", f"Langue FR introuvable :\n{e}")
        return

    try:
        pages = convert_from_path(current_pdf_path, 300, poppler_path=poppler_bin)
    except Exception as e:
        messagebox.showerror("Erreur PDF", f"Impossible de lire le PDF :\n{e}")
        return

    start = time.time()
    extracted = ""
    try:
        for i, page in enumerate(pages, start=1):
            root.title(f"OCR Tesseract… page {i}/{len(pages)}")
            extracted += pytesseract.image_to_string(page, lang="fra") + "\n"
    except Exception as e:
        messagebox.showerror("Erreur OCR", f"Erreur pendant l’OCR :\n{e}")
        return
    finally:
        # On restaure le titre dynamique basé sur le PDF courant
        update_window_title()

    duration = time.time() - start

    if create_raw_and_clean.get():
        set_tab("tess_raw", "Texte Tesseract (brut)", extracted.strip())
        cleaned = clean_text(extracted, stage="Tesseract")
        set_tab("tess_clean", "Texte Tesseract (nettoyé)", cleaned)
    else:
        cleaned = clean_text(extracted, stage="Tesseract")
        set_tab("tesseract", "Texte Tesseract", cleaned)

    status_var.set(f"OCR Tesseract – {len(pages)} page(s), {duration:.1f} s")


def ocr_vision():
    """
    OCR Vision sur le PDF courant (ou demander un PDF si aucun chargé).
    """
    global current_pdf_path

    if not current_pdf_path:
        path = filedialog.askopenfilename(
            filetypes=[("PDF ou images", "*.pdf;*.png;*.jpg;*.jpeg")],
            title="Choisis un PDF ou une image pour OCR Vision"
        )
        if not path:
            return
        current_pdf_path = path

    start = time.time()
    all_text = ""
    nb_pages = 1

    try:
        if current_pdf_path.lower().endswith(".pdf"):
            poppler_bin = ensure_poppler()
            pages = convert_from_path(current_pdf_path, 300, poppler_path=poppler_bin)
            nb_pages = len(pages)
            for i, page in enumerate(pages, start=1):
                root.title(f"OCR Vision… page {i}/{len(pages)}")
                tmp_img = tempfile.NamedTemporaryFile(suffix=".png", delete=False)
                page.save(tmp_img.name, "PNG")
                txt = ocr_image_vision(tmp_img.name)
                all_text += txt + "\n\n"
                tmp_img.close()
        else:
            all_text = ocr_image_vision(current_pdf_path)
    except Exception as e:
        messagebox.showerror("OCR Vision", f"Erreur Vision API :\n{e}")
        return
    finally:
        # On restaure le titre dynamique basé sur le PDF courant
        update_window_title()

    duration = time.time() - start

    if create_raw_and_clean.get():
        set_tab("vision_raw", "Texte Vision (brut)", all_text.strip())
        cleaned = clean_text(all_text, stage="Vision")
        set_tab("vision_clean", "Texte Vision (nettoyé)", cleaned)
    else:
        cleaned = clean_text(all_text, stage="Vision")
        set_tab("vision", "Texte Vision", cleaned)

    status_var.set(f"OCR Vision – {nb_pages} page(s), {duration:.1f} s")


def corriger_onglet_actif():
    """
    Applique LanguageTool + clean_text sur le texte de l’onglet actif.
    Crée un nouvel onglet "Corrigé – <titre>".
    """
    key = get_active_tab_key()
    txt_widget = get_active_text_widget()
    if not key or not txt_widget:
        messagebox.showerror("Correction", "Aucun onglet actif.")
        return

    original_title = tabs[key]["title"]
    text = txt_widget.get("1.0", tk.END)
    if not text.strip():
        messagebox.showerror("Correction", "Texte vide dans l’onglet actif.")
        return

    try:
        matches = tool.check(text)
        corrected = language_tool_python.utils.correct(text, matches)
    except Exception as e:
        messagebox.showerror("Erreur correction", f"Erreur LanguageTool :\n{e}")
        return

    cleaned = clean_text(corrected, stage=f"Corrigé {original_title}")
    new_key = f"corr_{key}_{len([k for k in tabs if k.startswith('corr_'+key)])}"
    new_title = f"Corrigé – {original_title}"

    set_tab(new_key, new_title, cleaned)
    status_var.set(f"Correction appliquée sur : {original_title}")


def comparer_versions(show_dialog: bool = True):
    """
    Compare les versions disponibles et suggère la meilleure.
    Marque la meilleure version :
      - ✅ dans le titre
      - fond vert clair dans le texte
    Numérote les onglets de 1. (meilleur), 2., 3., ...
    """
    global winner_tab_key

    if not tabs:
        if show_dialog:
            messagebox.showinfo("Comparer", "Aucun texte à comparer.")
        return

    ranking = []  # (key, info, title, metrics, score_effectif)

    for key, info in tabs.items():
        title = info["title"]
        txt_widget = info["text"]
        text = txt_widget.get("1.0", tk.END)

        if not text.strip():
            continue

        metrics = estimate_text_quality(text)
        base_score = metrics["score"]

        low_title = title.lower()
        score = base_score

        if low_title.startswith("corrigé") or low_title.startswith("corrige"):
            score *= 1.12

        if "nettoyé" in low_title or "nettoye" in low_title:
            score *= 1.08

        if "vision" in low_title:
            score *= 1.03

        if "brut" in low_title:
            score *= 0.96

        if "intégré" in low_title or "integre" in low_title:
            score *= 0.90

        ranking.append((key, info, title, metrics, score))

    if not ranking:
        if show_dialog:
            messagebox.showinfo("Comparer", "Impossible de déterminer une version meilleure.")
        return

    # Tri par score décroissant
    ranking.sort(key=lambda x: x[4], reverse=True)

    best_key, best_info, best_title, best_metrics, best_score = ranking[0]

    # Remise à blanc des fonds
    for k, info in tabs.items():
        info["text"].config(bg="white")

    winner_tab_key = best_key

    # Construction du détail pour la boîte de dialogue
    lines = []
    for rank_idx, (key, info, title, metrics, score) in enumerate(ranking, start=1):
        frame = info["frame"]
        label_base = f"{rank_idx}. {title}"

        if key == best_key:
            info["text"].config(bg="#e5ffe5")
            notebook.tab(frame, text=f"✅ {label_base} ✖")
        else:
            notebook.tab(frame, text=f"{label_base} ✖")

        lines.append(
            f"• {label_base}\n"
            f"  - mots : {metrics['words']}\n"
            f"  - mots inconnus : {metrics['bad_words']} ({metrics['bad_ratio']*100:.1f} %)\n"
            f"  - bruit : {metrics['noise_ratio']*100:.2f} % des caractères\n"
            f"  - score : {score:.1f}\n"
        )

    # Sélectionne l’onglet gagnant
    notebook.select(best_info["frame"])
    status_var.set(f"Suggestion : {best_title}")

    if show_dialog:
        msg = (
            f"La version la plus probable comme “meilleure” est :\n\n"
            f"👉 {best_title}\n\n"
            f"Détail des scores :\n\n" + "\n".join(lines)
        )
        messagebox.showinfo("Suggestion Eduscan – Comparaison", msg)

# ─────────────────────────────────────────
# AMÉLIORATION DU PDF (Tool)
# ─────────────────────────────────────────

def ameliorer_pdf():
    """
    Crée un nouveau PDF 'amélioré' :
    - conserve l'image/scan des pages
    - remplace/ajoute une couche texte avec la meilleure version (onglet n°1)
    """
    global current_pdf_path

    if not current_pdf_path:
        messagebox.showerror(
            "Améliorer PDF",
            "Aucun PDF n’est actuellement chargé.\n"
            "Utilise d’abord Scan → Analyser PDF…"
        )
        return

    if not tabs:
        messagebox.showerror(
            "Améliorer PDF",
            "Aucune version de texte n’est disponible.\n"
            "Fais d’abord un OCR ou une correction."
        )
        return

    # On s’assure que winner_tab_key est à jour
    comparer_versions(show_dialog=False)

    if not winner_tab_key or winner_tab_key not in tabs:
        messagebox.showerror(
            "Améliorer PDF",
            "Impossible de déterminer la meilleure version du texte."
        )
        return

    best_info = tabs[winner_tab_key]
    best_text = best_info["text"].get("1.0", tk.END).strip()
    if not best_text:
        messagebox.showerror(
            "Améliorer PDF",
            "Le texte de la meilleure version est vide."
        )
        return

    base, ext = os.path.splitext(current_pdf_path)
    default_out = base + "_improved.pdf"

    out_path = filedialog.asksaveasfilename(
        initialfile=os.path.basename(default_out),
        defaultextension=".pdf",
        filetypes=[("PDF", "*.pdf")],
        title="Enregistrer le PDF amélioré"
    )
    if not out_path:
        return

    try:
        poppler_bin = ensure_poppler()
        pages = convert_from_path(current_pdf_path, 300, poppler_path=poppler_bin)
    except Exception as e:
        messagebox.showerror(
            "Améliorer PDF",
            f"Impossible de relire le PDF d’origine :\n{e}"
        )
        return

    try:
        c = canvas.Canvas(out_path, pagesize=A4)
        width, height = A4

        first = True
        for page in pages:
            img = page
            img_w, img_h = img.size
            scale = min(width / img_w, height / img_h)
            new_w, new_h = img_w * scale, img_h * scale
            x = (width - new_w) / 2
            y = (height - new_h) / 2

            c.drawImage(ImageReader(img), x, y, new_w, new_h)

            if first:
                # Texte overlay minuscule, blanc, pour rendre le PDF searchable
                c.setFont("Helvetica", 1)
                c.setFillColorRGB(1, 1, 1)
                text_obj = c.beginText(1, 1)
                text_obj.textLines(best_text)
                c.drawText(text_obj)
                first = False

            c.showPage()

        c.save()
    except Exception as e:
        messagebox.showerror(
            "Améliorer PDF",
            f"Erreur lors de la création du PDF amélioré :\n{e}"
        )
        return

    status_var.set(f"PDF amélioré enregistré : {out_path}")
    messagebox.showinfo(
        "Améliorer PDF",
        "PDF amélioré créé avec la meilleure version du texte.\n"
        "L’image du scan est conservée, mais le PDF devient pleinement searchable."
    )

# ─────────────────────────────────────────
# EXPORTS
# ─────────────────────────────────────────

def get_active_text_widget_text():
    txt = get_active_text_widget()
    if not txt:
        return None
    return txt.get("1.0", tk.END)


def export_txt():
    text = get_active_text_widget_text()
    if not text or not text.strip():
        messagebox.showerror("Export TXT", "Aucun texte dans l’onglet actif.")
        return

    out = filedialog.asksaveasfilename(
        defaultextension=".txt",
        filetypes=[("Texte", "*.txt")],
        title="Enregistrer le texte (TXT)"
    )
    if not out:
        return

    try:
        with open(out, "w", encoding="utf-8") as f:
            f.write(text)
    except Exception as e:
        messagebox.showerror("Export TXT", f"Erreur lors de l’enregistrement :\n{e}")
        return

    status_var.set("Export TXT terminé ✔")


def text_to_markdown(text: str) -> str:
    md_lines = []
    for raw_line in text.split("\n"):
        line = raw_line.rstrip()

        if not line.strip():
            md_lines.append("")
            continue

        stripped = line.strip()

        if (
            len(stripped) <= 40
            and stripped == stripped.upper()
            and any(c.isalpha() for c in stripped)
        ) or stripped.lower().startswith("uaa "):
            md_lines.append(f"# {stripped}")
            continue

        if stripped.endswith(":") and "." not in stripped:
            md_lines.append(f"### {stripped[:-1]}")
            continue

        if re.match(r"^[-–—]\s*", stripped):
            core = re.sub(r"^[-–—]\s*", "", stripped)
            md_lines.append(f"- {core}")
            continue

        if stripped.startswith("•"):
            md_lines.append("- " + stripped.lstrip("•").lstrip())
            continue

        md_lines.append(line)

    return "\n".join(md_lines)


def export_md():
    text = get_active_text_widget_text()
    if not text or not text.strip():
        messagebox.showerror("Export Markdown", "Aucun texte dans l’onglet actif.")
        return

    out = filedialog.asksaveasfilename(
        defaultextension=".md",
        filetypes=[("Markdown", "*.md")],
        title="Enregistrer en Markdown"
    )
    if not out:
        return

    try:
        md = text_to_markdown(text)
        with open(out, "w", encoding="utf-8") as f:
            f.write(md)
    except Exception as e:
        messagebox.showerror("Export Markdown", f"Erreur lors de l’enregistrement :\n{e}")
        return

    status_var.set("Export Markdown terminé ✔ (avec mise en forme de base)")


def export_docx():
    text = get_active_text_widget_text()
    if not text or not text.strip():
        messagebox.showerror("Export DOCX", "Aucun texte dans l’onglet actif.")
        return

    out = filedialog.asksaveasfilename(
        defaultextension=".docx",
        filetypes=[("Word", "*.docx")],
        title="Enregistrer le DOCX"
    )
    if not out:
        return

    try:
        doc = Document()
        for line in text.split("\n"):
            doc.add_paragraph(line)
        doc.save(out)
    except Exception as e:
        messagebox.showerror("Export DOCX", f"Erreur lors de la création du DOCX :\n{e}")
        return

    status_var.set("Export DOCX terminé ✔")


def export_pdf():
    text = get_active_text_widget_text()
    if not text or not text.strip():
        messagebox.showerror("Export PDF", "Aucun texte dans l’onglet actif.")
        return

    out = filedialog.asksaveasfilename(
        defaultextension=".pdf",
        filetypes=[("PDF", "*.pdf")],
        title="Enregistrer le PDF texte"
    )
    if not out:
        return

    try:
        c = canvas.Canvas(out, pagesize=A4)
        width, height = A4
        x_margin = 50
        y = height - 50
        line_height = 14

        for line in text.split("\n"):
            if y < 50:
                c.showPage()
                y = height - 50
            c.drawString(x_margin, y, line)
            y -= line_height

        c.save()
    except Exception as e:
        messagebox.showerror("Export PDF", f"Erreur lors de la création du PDF :\n{e}")
        return

    status_var.set("Export PDF texte (searchable) terminé ✔")

# ─────────────────────────────────────────
# EXPORTS AVANCÉS VIA PANDOC
# ─────────────────────────────────────────

def run_pandoc_on_text(input_text: str, output_path: str, to_format: str):
    with tempfile.NamedTemporaryFile(delete=False, suffix=".md", mode="w", encoding="utf-8") as tmp:
        tmp_md_path = tmp.name
        tmp.write(input_text)

    cmd = ["pandoc", tmp_md_path, "-o", output_path]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=False
        )
    except FileNotFoundError:
        messagebox.showerror(
            "Pandoc introuvable",
            "Pandoc ne semble pas installé ou accessible dans le PATH.\n\n"
            "Installe-le depuis https://pandoc.org puis réessaie."
        )
        return False

    if result.returncode != 0:
        messagebox.showerror(
            "Erreur Pandoc",
            f"Commande : {' '.join(cmd)}\n\n"
            f"Code retour : {result.returncode}\n\n"
            f"stderr :\n{result.stderr}"
        )
        return False

    return True


def export_docx_pandoc():
    text = get_active_text_widget_text()
    if not text or not text.strip():
        messagebox.showerror("Export DOCX (Pandoc)", "Aucun texte dans l’onglet actif.")
        return

    out = filedialog.asksaveasfilename(
        defaultextension=".docx",
        filetypes=[("Word", "*.docx")],
        title="Enregistrer le DOCX (via Pandoc)"
    )
    if not out:
        return

    md = text_to_markdown(text)

    ok = run_pandoc_on_text(md, out, to_format="docx")
    if ok:
        status_var.set("Export DOCX via Pandoc terminé ✔")


def export_html_pandoc():
    text = get_active_text_widget_text()
    if not text or not text.strip():
        messagebox.showerror("Export HTML (Pandoc)", "Aucun texte dans l’onglet actif.")
        return

    out = filedialog.asksaveasfilename(
        defaultextension=".html",
        filetypes=[("HTML", "*.html;*.htm")],
        title="Enregistrer le HTML (via Pandoc)"
    )
    if not out:
        return

    md = text_to_markdown(text)

    ok = run_pandoc_on_text(md, out, to_format="html")
    if ok:
        status_var.set("Export HTML via Pandoc terminé ✔")


def export_google_docs():
    messagebox.showinfo(
        "Export Google Docs",
        "Export Google Docs n’est pas encore implémenté.\n\n"
        "Étapes prévues :\n"
        "- Utiliser l’API Google Drive/Docs\n"
        "- Créer un document depuis le texte de l’onglet actif\n"
        "- Obtenir un lien partageable.\n\n"
        "Tu pourras l’ajouter plus tard quand tu seras prêt à configurer les APIs Google."
    )

# ─────────────────────────────────────────
# AUTRES
# ─────────────────────────────────────────

def show_corrections():
    if not correction_log:
        messagebox.showinfo("Corrections", "Aucune correction lexicale enregistrée pour le dernier traitement.")
        return

    win = tk.Toplevel(root)
    win.title("Corrections lexicales (dernier nettoyage)")
    win.geometry("500x400")

    txt = ScrolledText(win, wrap=tk.WORD, font=("Consolas", 10))
    txt.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

    for stage, orig, corr in correction_log:
        txt.insert(tk.END, f"[{stage}] {orig} → {corr}\n")

    txt.config(state=tk.DISABLED)


def show_about():
    messagebox.showinfo(
        "À propos d’Eduscan",
        "Eduscan v2.3\n\n"
        "Comparateur OCR pour profs :\n"
        "- Image PDF à gauche\n"
        "- Scanner / Tesseract / Vision / Corrections en onglets à droite\n"
        "- Export TXT / MD / DOCX / PDF texte\n\n"
        "Et comparaison automatique à chaque nouvelle version 😎"
    )

# ─────────────────────────────────────────
# MENUS & BARRE DE BOUTONS
# ─────────────────────────────────────────

menubar = tk.Menu(root)

# ───── Menu Scan ─────
menu_scan = tk.Menu(menubar, tearoff=0)
menu_scan.add_command(label="🔍 Analyser PDF…", command=analyser_pdf)
menu_scan.add_command(label="📄 OCR Tesseract", command=ocr_tesseract)
menu_scan.add_command(label="👁️ OCR Vision", command=ocr_vision)
menubar.add_cascade(label="Scan", menu=menu_scan)

# ───── Menu Tool ─────
menu_tool = tk.Menu(menubar, tearoff=0)
menu_tool.add_command(
    label="✨ Améliorer PDF (meilleure version)",
    command=ameliorer_pdf
)
menubar.add_cascade(label="Tool", menu=menu_tool)

# ───── Menu Export ─────
menu_export = tk.Menu(menubar, tearoff=0)
menu_export.add_command(label="📄 Export TXT…", command=export_txt)
menu_export.add_command(label="📄 Export Markdown…", command=export_md)
menu_export.add_command(label="📝 Export DOCX…", command=export_docx)
menu_export.add_command(label="📑 Export PDF (searchable)…", command=export_pdf)

# Sous-partie Pandoc
menu_export.add_separator()
menu_export.add_command(label="📝 Export DOCX via Pandoc…", command=export_docx_pandoc)
menu_export.add_command(label="🌐 Export HTML via Pandoc…", command=export_html_pandoc)

menu_export.add_separator()
menu_export.add_command(label="☁ Export Google Docs (à venir)…", command=export_google_docs)

menubar.add_cascade(label="Export", menu=menu_export)

# ───── Menu Analyse ─────
menu_analyse = tk.Menu(menubar, tearoff=0)
menu_analyse.add_command(label="Voir corrections lexicales", command=show_corrections)
menu_analyse.add_command(label="⚖️ Comparer versions", command=lambda: comparer_versions(show_dialog=True))
menubar.add_cascade(label="Analyse", menu=menu_analyse)

# ───── Menu Option ─────
menu_option = tk.Menu(menubar, tearoff=0)
menu_option.add_checkbutton(
    label="Créer onglets brut + nettoyé pour OCR",
    variable=create_raw_and_clean,
    onvalue=True,
    offvalue=False
)

menu_option.add_separator()

menu_option.add_radiobutton(
    label="Nettoyage doux (recommandé)",
    variable=cleaning_mode,
    value="doux"
)
menu_option.add_radiobutton(
    label="Nettoyage agressif (plus de corrections)",
    variable=cleaning_mode,
    value="agressif"
)

menu_option.add_separator()

menu_option.add_checkbutton(
    label="Correction lexicale automatique (dictionnaire FR)",
    variable=auto_lexical_correction,
    onvalue=True,
    offvalue=False
)

menubar.add_cascade(label="Option", menu=menu_option)

# ───── Menu Aide ─────
menu_aide = tk.Menu(menubar, tearoff=0)
menu_aide.add_command(label="À propos d’Eduscan", command=show_about)
menubar.add_cascade(label="Aide", menu=menu_aide)

root.config(menu=menubar)

# Barre de boutons
top_frame = tk.Frame(root)
top_frame.pack(side=tk.TOP, fill=tk.X, pady=2)

# On NE GARDE QUE le bouton de correction à droite
btn_corr = tk.Button(top_frame, text="🧠 Corriger onglet actif", command=corriger_onglet_actif, width=22)
btn_corr.pack(side=tk.RIGHT, padx=5)

root.mainloop()
