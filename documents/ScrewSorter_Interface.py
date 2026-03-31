import tkinter as tk
from tkinter import ttk
import time
import threading
from datetime import datetime
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.pyplot as plt
import socket
import struct
import pickle
from PIL import Image, ImageTk
import cv2
import os
from matplotlib.ticker import MultipleLocator


# ================= SERIAL CONFIG =================
USE_SERIAL = True
SERIAL_PORT = "/dev/cu.usbserial-10"
BAUDRATE = 115200
ser = None

if USE_SERIAL:
    try:
        import serial
        ser = serial.Serial(SERIAL_PORT, BAUDRATE, timeout=0.1)
        time.sleep(2)
    except Exception as e:
        ser = None
        USE_SERIAL = False
        print("Error opening serial port:", e)


# ================= SERIAL HELPER FUNCTION =================
def send_one_combo(diam, length, mag):
    """Envoi d'une combinaison via série"""
    if ser is None:
        return "NO SERIAL"
    msg = f"D={diam};L={length};M={mag}\n"
    try:
        ser.write(msg.encode())
        return f"Sent -> {msg.strip()}"
    except Exception as e:
        return f"Send error: {e}"

# ================= CONSTANTS =================
ALLOWED_DIAMS = sorted(["M3", "M4", "M5", "M6"], key=lambda x: int(x[1:]))
ALLOWED_LEN = sorted([10, 20, 30, 40, 50, 60, 70])

class RoundedButton(tk.Canvas):
    """Bouton avec coins arrondis"""
    def __init__(self, parent, text, command, bg, fg, radius=12, **kwargs):
        tk.Canvas.__init__(self, parent, highlightthickness=0, **kwargs)
        self.command = command
        self.text = text
        self.bg_color = bg
        self.fg_color = fg
        self.radius = radius
        self.configure(bg=parent['bg'])
        
        self.bind('<Button-1>', lambda e: self.command())
        self.bind('<Enter>', self.on_enter)
        self.bind('<Leave>', self.on_leave)
        
        self.draw()
        
    def draw(self):
        self.delete('all')
        w, h = self.winfo_reqwidth(), self.winfo_reqheight()
        if w < 10 or h < 10:
            w, h = 200, 50
            
        r = self.radius
        self.create_polygon([
            r, 0,
            w-r, 0,
            w, 0,
            w, r,
            w, h-r,
            w, h,
            w-r, h,
            r, h,
            0, h,
            0, h-r,
            0, r,
            0, 0
        ], fill=self.bg_color, smooth=True, outline='')
        
        self.create_text(w//2, h//2, text=self.text, fill=self.fg_color, 
                        font=('Inter', 11, 'bold'))
        
    def on_enter(self, e):
        self.config(cursor='hand2')
        
    def on_leave(self, e):
        self.config(cursor='')

class RoundedFrame(tk.Canvas):
    """Frame avec coins arrondis et ombre"""
    def __init__(self, parent, radius=20, bg='white', shadow=True, **kwargs):
        tk.Canvas.__init__(self, parent, highlightthickness=0, **kwargs)
        self.radius = radius
        self.bg_color = bg
        self.shadow = shadow
        self.configure(bg=parent['bg'])
        self.bind('<Configure>', lambda e: self.draw())
        
    def draw(self):
        self.delete('all')
        w, h = self.winfo_width(), self.winfo_height()
        r = self.radius
        
        # Ombre (version simplifiée sans transparence)
        if self.shadow:
            shadow_offset = 3
            shadow_color = '#d0d0d0'  # Gris clair pour l'ombre
            self.create_oval(r, shadow_offset, r*2, r*2+shadow_offset, 
                           fill=shadow_color, outline='')
            self.create_oval(w-r*2, shadow_offset, w-r, r*2+shadow_offset, 
                           fill=shadow_color, outline='')
            self.create_oval(r, h-r*2+shadow_offset, r*2, h-r+shadow_offset, 
                           fill=shadow_color, outline='')
            self.create_oval(w-r*2, h-r*2+shadow_offset, w-r, h-r+shadow_offset, 
                           fill=shadow_color, outline='')
            self.create_rectangle(r, shadow_offset, w-r, h+shadow_offset, 
                                fill=shadow_color, outline='')
            self.create_rectangle(0, r+shadow_offset, w, h-r+shadow_offset, 
                                fill=shadow_color, outline='')
        
        # Fond avec coins arrondis
        self.create_oval(0, 0, r*2, r*2, fill=self.bg_color, outline='')
        self.create_oval(w-r*2, 0, w, r*2, fill=self.bg_color, outline='')
        self.create_oval(0, h-r*2, r*2, h, fill=self.bg_color, outline='')
        self.create_oval(w-r*2, h-r*2, w, h, fill=self.bg_color, outline='')
        self.create_rectangle(r, 0, w-r, h, fill=self.bg_color, outline='')
        self.create_rectangle(0, r, w, h-r, fill=self.bg_color, outline='')

class ModernScrewSorterApp:
    def __init__(self):
        # Data
        self.counts = {1: 0, 2: 0, 3: 0, 4: 0, 5: 0}
        self.current_combos = ["Bin 1", "Bin 2", "Bin 3", "Bin 4"]
        self.speed_values = []
        self.MAX_SPEED_POINTS = 200
        self.log_messages = []
        self.is_dark_mode = False
        self.config_mode = "1_diam_4_len"
        
        # ============ AJOUT POUR L'ÉNERGIE ============
        self.torque_values = []
        self.energy_values = []
        self.conveyor_speed_values = []
        self.motor2_speed_values = []
        self.conveyor_speed_ms_values = []  # ✅ NOUVEAU : Vitesse en m/s
        
        # États des composants (0 = idle, 1 = actif)
        self.arduino_state = {
            "servo_13kg_1": 0,
            "servo_35kg": 0,
            "servo_3A1": 0,
            "servo_3A2": 0,
        }
        
        # Énergie cumulée
        self.energy_cumulative = [0]
        self.last_time = time.time()
        # ==============================================
        
        # Setup
        self.setup_window()
        self.setup_themes()
        self.create_main_interface()
        self.start_serial_polling()
        
    def setup_window(self):
        """Configuration de la fenêtre principale"""
        self.root = tk.Tk()
        self.root.title("ScrewSorter Pro - Modern Dashboard")
        self.root.geometry("1400x900")
        
    def setup_themes(self):
        """Thèmes modernes avec meilleur contraste"""
        self.themes = {
            'light': {
                'bg_primary': '#ffffff',
                'bg_secondary': '#f7f9fc',
                'bg_accent': '#e8ecf4',
                'bg_card': '#ffffff',
                'text_primary': '#0d1b2a',
                'text_secondary': '#415a77',
                'text_accent': '#778da9',
                'border': '#d8e2ef',
                'button_primary': '#0066ff',
                'button_hover': '#0052cc',
                'success': '#00b341',
                'warning': '#ff8c00',
                'danger': '#ff3b30',
                'sidebar': '#0d1b2a',
                'sidebar_text': '#ffffff',
                'sidebar_hover': '#1e3a5f',
                'card_shadow': '#a0b3cc40'
            },
            'dark': {
                'bg_primary': '#0a0e1a',
                'bg_secondary': '#050810',
                'bg_accent': '#151b2e',
                'bg_card': '#0f1523',
                'text_primary': '#e8ecf4',
                'text_secondary': '#a0b3cc',
                'text_accent': '#6b8099',
                'border': '#1e2d44',
                'button_primary': '#0066ff',
                'button_hover': '#0052cc',
                'success': '#00e65c',
                'warning': '#ffaa00',
                'danger': '#ff5247',
                'sidebar': '#050810',
                'sidebar_text': '#e8ecf4',
                'sidebar_hover': '#0f1523',
                'card_shadow': '#00000060'
            }
        }
        
        self.current_theme = self.themes['light']
        
    def apply_theme(self):
        """Applique le thème"""
        theme = self.current_theme
        self.root.configure(bg=theme['bg_secondary'])
        
        if hasattr(self, 'sidebar'):
            self.sidebar.configure(bg=theme['sidebar'])
        if hasattr(self, 'content_area'):
            self.content_area.configure(bg=theme['bg_secondary'])
        if hasattr(self, 'current_page_frame'):
            self.show_page(self.current_page)
            
    def toggle_theme(self):
        """Bascule le thème"""
        self.is_dark_mode = not self.is_dark_mode
        self.current_theme = self.themes['dark'] if self.is_dark_mode else self.themes['light']
        self.apply_theme()
        
        icon = "🌙" if not self.is_dark_mode else "☀️"
        text = "Dark Mode" if not self.is_dark_mode else "Light Mode"
        if hasattr(self, 'theme_button_text'):
            self.theme_button_text.configure(text=f"{icon} {text}")
        
    def create_main_interface(self):
        """Interface principale"""
        main_container = tk.Frame(self.root, bg=self.current_theme['bg_secondary'])
        main_container.pack(fill='both', expand=True)
        
        self.create_sidebar(main_container)
        
        self.content_area = tk.Frame(main_container, bg=self.current_theme['bg_secondary'])
        self.content_area.pack(side='right', fill='both', expand=True)
        
        self.create_header()
        
        self.current_page = 'dashboard'
        self.create_pages()
        self.show_page('dashboard')
        
    def create_sidebar(self, parent):
        """Sidebar moderne avec gradient"""
        self.sidebar = tk.Frame(parent, bg=self.current_theme['sidebar'], width=280)
        self.sidebar.pack(side='left', fill='y')
        self.sidebar.pack_propagate(False)
        
        # Logo
        logo_frame = tk.Frame(self.sidebar, bg=self.current_theme['sidebar'])
        logo_frame.pack(fill='x', pady=35, padx=25)
        
        logo_label = tk.Label(logo_frame, 
                             text="🔧 ScrewSorter",
                             bg=self.current_theme['sidebar'],
                             fg=self.current_theme['sidebar_text'],
                             font=('SF Pro Display', 20, 'bold'))
        logo_label.pack()
        
        version_label = tk.Label(logo_frame,
                               text="Pro Edition v3.0",
                               bg=self.current_theme['sidebar'],
                               fg=self.current_theme['text_accent'],
                               font=('SF Pro Display', 9))
        version_label.pack(pady=(5, 0))
        
        # Navigation
        nav_frame = tk.Frame(self.sidebar, bg=self.current_theme['sidebar'])
        nav_frame.pack(fill='x', pady=30)

        self.nav_buttons = {}

        # Nouvel ordre et nouvelles pages
        nav_items = [
            ('config', '⚙️', 'Configuration'),
            ('dashboard', '📊', 'Dashboard'),
            ('matrix', '🗃️', 'Screw Matrix'),
            ('analytics', '📈', 'Analytics'),
            ('monitor', '📡', 'Monitoring'),
            ('camera', '🎥', 'Camera'),
            ('testing', '🧪', 'Testing'),
            ('project', '📋', 'Our Project')
        ]

        for page_id, icon, title in nav_items:
            self.create_nav_button(nav_frame, page_id, icon, title)

        spacer = tk.Frame(self.sidebar, bg=self.current_theme['sidebar'])
        spacer.pack(fill='both', expand=True)
        
        # Status
        status_frame = tk.Frame(self.sidebar, bg=self.current_theme['sidebar'])
        status_frame.pack(fill='x', padx=25, pady=(15, 5))
        
        status_color = self.current_theme['success'] if USE_SERIAL else self.current_theme['danger']
        status_text = "● Connected" if USE_SERIAL else "● Disconnected"
        
        self.status_label = tk.Label(status_frame,
                                   text=status_text,
                                   bg=self.current_theme['sidebar'],
                                   fg=status_color,
                                   font=('SF Pro Display', 11, 'bold'))
        self.status_label.pack()

        # ---------------- AJOUT DU JOUR ET HEURE ----------------
        time_frame = tk.Frame(self.sidebar, bg=self.current_theme['sidebar'])
        time_frame.pack(fill='x', padx=25, pady=(5, 15))

        self.sidebar_time_label = tk.Label(time_frame,
                                          bg=self.current_theme['sidebar'],
                                          fg=self.current_theme['sidebar_text'],
                                          font=('SF Pro Display', 12, 'bold'))
        self.sidebar_time_label.pack()
        
        self.sidebar_date_label = tk.Label(time_frame,
                                          bg=self.current_theme['sidebar'],
                                          fg=self.current_theme['text_accent'],
                                          font=('SF Pro Display', 10))
        self.sidebar_date_label.pack()

        def update_sidebar_time():
            now = datetime.now()
            self.sidebar_time_label.configure(text=now.strftime("%H:%M:%S"))
            self.sidebar_date_label.configure(text=now.strftime("%A %d/%m/%Y"))
            self.root.after(1000, update_sidebar_time)
        update_sidebar_time()
        # ---------------------------------------------------------

        # Bouton thème avec coins arrondis
        theme_container = tk.Frame(self.sidebar, bg=self.current_theme['sidebar'])
        theme_container.pack(fill='x', padx=25, pady=(10, 30))
        
        theme_btn_canvas = tk.Canvas(theme_container, 
                                    height=50, 
                                    bg=self.current_theme['sidebar'],
                                    highlightthickness=0)
        theme_btn_canvas.pack(fill='x')
        
        theme_btn_canvas.bind('<Button-1>', lambda e: self.toggle_theme())
        theme_btn_canvas.bind('<Enter>', lambda e: theme_btn_canvas.config(cursor='hand2'))
        theme_btn_canvas.bind('<Leave>', lambda e: theme_btn_canvas.config(cursor=''))
        
        def draw_theme_button():
            theme_btn_canvas.delete('all')
            w, h = theme_btn_canvas.winfo_width(), 50
            r = 12
            
            theme_btn_canvas.create_oval(0, 0, r*2, h, fill=self.current_theme['button_primary'], outline='')
            theme_btn_canvas.create_oval(w-r*2, 0, w, h, fill=self.current_theme['button_primary'], outline='')
            theme_btn_canvas.create_rectangle(r, 0, w-r, h, fill=self.current_theme['button_primary'], outline='')
            
            icon = "🌙" if not self.is_dark_mode else "☀️"
            text = "Dark Mode" if not self.is_dark_mode else "Light Mode"
            self.theme_button_text = theme_btn_canvas.create_text(w//2, h//2, 
                                                                  text=f"{icon} {text}",
                                                                  fill='white',
                                                                  font=('SF Pro Display', 12, 'bold'))

        theme_btn_canvas.bind('<Configure>', lambda e: draw_theme_button())

    def create_nav_button(self, parent, page_id, icon, title):
        """Bouton de navigation avec coins arrondis"""
        button_container = tk.Frame(parent, bg=self.current_theme['sidebar'])
        button_container.pack(fill='x', padx=20, pady=5)
        
        btn_canvas = tk.Canvas(button_container, 
                              height=50, 
                              bg=self.current_theme['sidebar'],
                              highlightthickness=0)
        btn_canvas.pack(fill='x')
        
        def draw_button(is_active=False):
            btn_canvas.delete('all')
            w, h = btn_canvas.winfo_width(), 50
            r = 12
            
            bg = self.current_theme['button_primary'] if is_active else self.current_theme['sidebar']
            
            btn_canvas.create_oval(0, 0, r*2, h, fill=bg, outline='')
            btn_canvas.create_oval(w-r*2, 0, w, h, fill=bg, outline='')
            btn_canvas.create_rectangle(r, 0, w-r, h, fill=bg, outline='')
            
            btn_canvas.create_text(25, h//2, text=icon, 
                                 fill=self.current_theme['sidebar_text'],
                                 font=('SF Pro Display', 16))
            btn_canvas.create_text(55, h//2, text=title, anchor='w',
                                 fill=self.current_theme['sidebar_text'],
                                 font=('SF Pro Display', 13, 'bold'))
        
        btn_canvas.bind('<Button-1>', lambda e: self.show_page(page_id))
        btn_canvas.bind('<Enter>', lambda e: [btn_canvas.config(cursor='hand2'), 
                                              draw_button(page_id == self.current_page)])
        btn_canvas.bind('<Leave>', lambda e: [btn_canvas.config(cursor=''), 
                                              draw_button(page_id == self.current_page)])
        btn_canvas.bind('<Configure>', lambda e: draw_button(page_id == self.current_page))
        
        self.nav_buttons[page_id] = (btn_canvas, draw_button)
        
    def create_header(self):
        """En-tête avec titre dans un cadre bleu simple"""
        header_frame = tk.Frame(self.content_area, bg=self.current_theme['bg_secondary'], height=100)
        header_frame.pack(fill='x', padx=35, pady=(35, 0))
        header_frame.pack_propagate(False)

        # Frame bleu SANS padding qui crée les bords blancs
        header_bg = self.current_theme['button_primary']
        self.title_frame = tk.Frame(header_frame, bg=header_bg, bd=0)
        self.title_frame.pack(fill='both', expand=True)  # ✅ fill='both' et expand=True

        self.page_title = tk.Label(self.title_frame,
                                   text="Dashboard",
                                   bg=header_bg,
                                   fg="white",
                                   font=('SF Pro Display', 40, 'bold'))
        self.page_title.pack(expand=True)  # ✅ Centré verticalement

    
        
    def create_pages(self):
        """Container des pages"""
        self.pages_container = tk.Frame(self.content_area, bg=self.current_theme['bg_secondary'])
        self.pages_container.pack(fill='both', expand=True, padx=35, pady=30)
        
    def show_page(self, page_id):
        """Affiche une page"""
        for btn_id, (canvas, draw_func) in self.nav_buttons.items():
            draw_func(btn_id == page_id)
        
        for widget in self.pages_container.winfo_children():
            widget.destroy()
            
        titles = {
            'dashboard': 'Dashboard',
            'project': 'Our Project',
            'config': 'Configuration',
            'analytics': 'Analytics',
            'monitor': 'Monitoring',
            'camera': 'Camera',
            'testing': 'Testing'
        }
        self.page_title.configure(text=titles.get(page_id, 'Page'))
        
        if page_id == 'dashboard':
            self.create_dashboard_page()
        elif page_id == 'project':
            self.create_project_page()
        elif page_id == 'config':
            self.create_config_page()
        elif page_id == 'analytics':
            self.create_analytics_page()
        elif page_id == 'monitor':
            self.create_monitor_page()
        elif page_id == 'camera':
            self.create_camera_page()
        elif page_id == 'matrix':
            self.create_matrix_page()
        elif page_id == 'testing':
            self.create_testing_page()

            
        self.current_page = page_id

    def create_modern_card(self, parent, title=None, height=None):
        """Carte avec coins arrondis et ombre"""
        card_container = tk.Frame(parent, bg=self.current_theme['bg_secondary'])
        
        # Frame standard au lieu de RoundedFrame pour plus de stabilité
        card = tk.Frame(card_container, bg=self.current_theme['bg_card'], 
                       relief='raised', bd=1, highlightbackground=self.current_theme['border'],
                       highlightthickness=1)
        card.pack(fill='both', expand=True, padx=2, pady=2)
        
        if title:
            title_label = tk.Label(card,
                                 text=title,
                                 bg=self.current_theme['bg_card'],
                                 fg=self.current_theme['text_primary'],
                                 font=('SF Pro Display', 18, 'bold'))
            title_label.pack(pady=(25, 15), padx=30, anchor='w')
        
        if height:
            card.configure(height=height)
            card.pack_propagate(False)
            
        return card_container
        
    def create_dashboard_page(self):
        """Page dashboard avec statistiques, bacs à gauche et graphe à droite"""
        # ===== Statistiques =====
        stats_frame = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        stats_frame.pack(fill='x', pady=(0,0))

        total_screws = sum(self.counts.values())
        stats = [
            ("Total Screws", str(total_screws), "📦", "#3b82f6"),   # Bleu vif
            ("Active Bins", str(len([c for c in self.counts.values() if c > 0])), "🗂️", "#10b981"), # Vert vif
            ("Speed", f"{self.speed_values[-1] if self.speed_values else 0} RPM", "⚡", "#f97316"), # Orange vif
            ("Status", "Online" if USE_SERIAL else "Offline", "🔗", "#ef4444") # Rouge vif
        ]

        for i, (title, value, icon, color) in enumerate(stats):
            self.create_modern_stat_card(stats_frame, title, value, icon, color, i)

        # ===== Section principale =====
        main_frame = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        main_frame.pack(fill='both', expand=True)

        # Configurer grid pour 2 colonnes avec poids différent
        main_frame.grid_rowconfigure(0, weight=1)
        main_frame.grid_columnconfigure(0, weight=2)  # Bacs → 1/4 largeur
        main_frame.grid_columnconfigure(1, weight=1)  # Graphe → 3/4 largeur

        # --- Bacs de Tri (à gauche) ---
        bins_container = tk.Frame(main_frame, bg=self.current_theme['bg_secondary'])
        bins_container.grid(row=0, column=0, sticky='nsew', padx=(0, 10))

        bins_title = tk.Label(bins_container,
                              text="🗂️ Sorting bins",
                              bg=self.current_theme['bg_secondary'],
                              fg=self.current_theme['text_primary'],
                              font=('SF Pro Display', 22, 'bold'))
        bins_title.pack(pady=(0, 10))

        # Création des bacs
        self.create_ultra_modern_bins(bins_container)

        # --- Graphe Performance (à droite) ---
        graph_container_parent = tk.Frame(main_frame, bg=self.current_theme['bg_secondary'])
        graph_container_parent.grid(row=0, column=1, sticky='nsew', padx=(10,0))

        graph_title = tk.Label(graph_container_parent,
                               text="📈 Performance",
                               bg=self.current_theme['bg_secondary'],
                               fg=self.current_theme['text_primary'],
                               font=('SF Pro Display', 22, 'bold'))
        graph_title.pack(pady=(0, 10))

        # Container du graphe
        graph_container = tk.Frame(graph_container_parent, bg=self.current_theme['bg_secondary'])
        graph_container.pack(fill='both', expand=True)

        # Graphique matplotlib
        self.fig_speed = Figure(figsize=(6, 4), facecolor=self.current_theme['bg_secondary'])
        self.ax_speed = self.fig_speed.add_subplot(111)
        self.ax_speed.set_facecolor(self.current_theme['bg_secondary'])
        self.ax_speed.set_xlabel('Time [s]', color=self.current_theme['text_secondary'], fontsize=10)
        self.ax_speed.set_ylabel('RPM', color=self.current_theme['text_secondary'], fontsize=10)
        self.ax_speed.grid(True, alpha=0.15, color=self.current_theme['text_accent'], linestyle='-', linewidth=0.5)
        self.ax_speed.tick_params(colors=self.current_theme['text_secondary'], labelsize=9)
        self.ax_speed.spines['top'].set_visible(False)
        self.ax_speed.spines['right'].set_visible(False)
        self.ax_speed.spines['left'].set_color(self.current_theme['text_accent'])
        self.ax_speed.spines['bottom'].set_color(self.current_theme['text_accent'])
                # ✅ AJOUTE après la configuration des axes
        from matplotlib.ticker import MaxNLocator
        self.ax_speed.xaxis.set_major_locator(MaxNLocator(nbins=12, integer=True))

        self.line_speed, = self.ax_speed.plot([], [], color=self.current_theme['button_primary'], linewidth=2.5, alpha=0.9)

        self.canvas_speed = FigureCanvasTkAgg(self.fig_speed, master=graph_container)
        self.canvas_speed.get_tk_widget().pack(fill='both', expand=True)
        self.canvas_speed.get_tk_widget().configure(bg=self.current_theme['bg_secondary'], highlightthickness=0)
        self.fig_speed.tight_layout()


            
    def create_modern_stat_card(self, parent, title, value, icon, color, index):
        """Carte statistique arrondie avec taille uniforme"""
        card_height = 150  # Hauteur uniforme réduite
        card = tk.Frame(parent, bg=self.current_theme['bg_card'],
                        relief='raised', bd=1, highlightbackground=self.current_theme['border'],
                        highlightthickness=1, height=card_height)
        card.pack(side='left', fill='both', expand=True, padx=(0 if index == 0 else 12, 0))
        card.pack_propagate(False)  # Ne pas laisser le contenu redimensionner la carte

        # Contenu
        content = tk.Frame(card, bg=self.current_theme['bg_card'])
        content.pack(fill='both', expand=True, padx=15, pady=10)  # padding réduit

        # Icône avec fond coloré
        icon_frame = tk.Frame(content, bg=color, width=50, height=50)
        icon_frame.pack(pady=(5, 8))
        icon_frame.pack_propagate(False)
        icon_label = tk.Label(icon_frame, text=icon, bg=color, fg='white', font=('SF Pro Display', 20))
        icon_label.place(relx=0.5, rely=0.5, anchor='center')

        # Valeur
        value_label = tk.Label(content,
                               text=value,
                               bg=self.current_theme['bg_card'],
                               fg=self.current_theme['text_primary'],
                               font=('SF Pro Display', 20, 'bold'))
        value_label.pack()

        # Titre
        title_label = tk.Label(content,
                               text=title,
                               bg=self.current_theme['bg_card'],
                               fg=self.current_theme['text_secondary'],
                               font=('SF Pro Display', 10))
        title_label.pack(pady=(2, 5))

    def create_ultra_modern_bins(self, parent):
        """Bacs avec design arrondi et compteurs correctement visibles"""
        # Récupérer le frame card
        if isinstance(parent, tk.Frame):
            card = parent
        else:
            card = parent.winfo_children()[0]

        bins_container = tk.Frame(card, bg=self.current_theme['bg_secondary'])
        bins_container.pack(fill='both', expand=True, padx=10, pady=10)

        self.bin_labels = {}
        self.bin_frames = {}

        colors = ['#3b82f6', '#10b981', '#f97316', '#ef4444', '#8b5cf6']  # bleu, vert, orange, rouge, violet
        positions = [(0, 1), (1, 0), (1, 2), (2, 0), (2, 2)]

        for i, (bin_id, (row, col)) in enumerate(zip([5, 2, 3, 1, 4], positions)):
            # Frame coloré
            bin_frame = tk.Frame(bins_container, bg=colors[i], width=180, height=160)
            bin_frame.grid(row=row, column=col, padx=12, pady=12, sticky='nsew')
            bin_frame.pack_propagate(False)
            bin_frame.grid_propagate(False)

            # Label du bac - utiliser current_combos
            label_text = self.current_combos[bin_id-1] if bin_id <= 4 and (bin_id-1) < len(self.current_combos) else "Others"
            label = tk.Label(bin_frame,
                             text=label_text,
                             bg=colors[i],
                             fg='white',
                             font=('SF Pro Display', 12, 'bold'))
            label.pack(pady=(10, 5))

            # Compteur
            count_label = tk.Label(bin_frame,
                                   text=str(self.counts[bin_id]),
                                   bg=colors[i],
                                   fg='white',
                                   font=('SF Pro Display', 36, 'bold'))
            count_label.pack(expand=True, fill='both')
            count_label.configure(anchor='center')

            # Indicateur
            status_label = tk.Label(bin_frame,
                                    text="●",
                                    bg=colors[i],
                                    fg='white',
                                    font=('SF Pro Display', 10))
            status_label.pack(pady=(5, 5))

            self.bin_labels[bin_id] = count_label
            self.bin_frames[bin_id] = bin_frame

        # Configurer le grid pour que tout prenne de l'espace
        for i in range(3):
            bins_container.grid_rowconfigure(i, weight=1)
            bins_container.grid_columnconfigure(i, weight=1)


        
    def create_project_page(self):
        """Page projet avec photos"""
        # Canvas scrollable
        project_card = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        project_card.pack(fill='both', expand=True)

        canvas = tk.Canvas(project_card, bg=self.current_theme['bg_card'], highlightthickness=0)
        scrollbar = tk.Scrollbar(project_card, orient="vertical", command=canvas.yview)
        scrollable_frame = tk.Frame(canvas, bg=self.current_theme['bg_card'])
        
        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        content = tk.Frame(scrollable_frame, bg=self.current_theme['bg_card'])
        content.pack(fill='both', expand=True, padx=45, pady=35)
        
        # Titre
        title_label = tk.Label(content, text="🔧 ScrewSorter Pro",
                              bg=self.current_theme['bg_card'],
                              fg=self.current_theme['text_primary'],
                              font=('SF Pro Display', 28, 'bold'))
        title_label.pack(pady=(0,10))
            
        subtitle_label = tk.Label(content, text="Automated Intelligent Sorting System",
                                 bg=self.current_theme['bg_card'],
                                 fg=self.current_theme['text_secondary'],
                                 font=('SF Pro Display', 15))
        subtitle_label.pack(pady=(0, 35))
        
        # === SECTION PHOTOS ===
        # Chemins des photos
        machine_photo = "/Users/giando/Desktop/machine.jpg"
        group_photo = "/Users/giando/Desktop/group_photocopie.jpg"
        
        # Vérifier si AU MOINS une photo existe
        has_photos = os.path.exists(machine_photo) or os.path.exists(group_photo)
        
        # Créer photos_frame SEULEMENT si on a des photos
        if has_photos:
            photos_frame = tk.Frame(content, bg=self.current_theme['bg_card'])
            photos_frame.pack(fill='x', pady=(0, 35))
            
            # Photo de la machine
            if os.path.exists(machine_photo):
                try:
                    img = Image.open(machine_photo)
                    if img.width > 800:
                        img = img.resize((800, int(img.height * 800 / img.width)), Image.Resampling.LANCZOS)
                    photo = ImageTk.PhotoImage(img)
                    
                    machine_frame = tk.Frame(photos_frame, bg=self.current_theme['bg_card'])
                    machine_frame.pack(pady=(0, 20))
                    
                    tk.Label(machine_frame, text="📷 Our Machine",
                            bg=self.current_theme['bg_card'],
                            fg=self.current_theme['text_primary'],
                            font=('SF Pro Display', 18, 'bold')).pack(pady=(0, 15))
                    
                    label = tk.Label(machine_frame, image=photo, bg=self.current_theme['bg_card'])
                    label.image = photo
                    label.pack()
                except Exception as e:
                    print(f"Erreur chargement machine photo: {e}")
            
            # Photo de l'équipe
            if os.path.exists(group_photo):
                try:
                    img = Image.open(group_photo)
                    if img.width > 800:
                        img = img.resize((800, int(img.height * 800 / img.width)), Image.Resampling.LANCZOS)
                    photo = ImageTk.PhotoImage(img)
                    
                    group_frame = tk.Frame(photos_frame, bg=self.current_theme['bg_card'])
                    group_frame.pack(pady=(0, 20))
                    
                    tk.Label(group_frame, text="👥 Our Team",
                            bg=self.current_theme['bg_card'],
                            fg=self.current_theme['text_primary'],
                            font=('SF Pro Display', 18, 'bold')).pack(pady=(0, 15))
                    
                    label = tk.Label(group_frame, image=photo, bg=self.current_theme['bg_card'])
                    label.image = photo
                    label.pack()
                except Exception as e:
                    print(f"Erreur chargement group photo: {e}")
        
        # === SECTIONS DESCRIPTIVES ===
 
            sections = [
                ('🎯 Objective', 'Automatically sort and classify screws by diameter, length and magnetic properties.'),
                ('⚙️ Features', '• M3-M6 Classification\n• 10-60mm Measurement\n• Magnetic Detection\n• Modern Interface\n• Real-time Monitoring'),
                ('🔬 Technologies', '• Advanced Sensors\n• Arduino/ESP32\n• Python + Tkinter\n• Serial Communication\n• Data Visualization'),
                ('📊 Benefits', '• Error Reduction\n• Increased Productivity\n• Complete Traceability\n• Ergonomic Interface')
            ]
        
        for title, content_text in sections:
            self.create_project_section(content, title, content_text)
                    


    def create_project_section(self, parent, title, content_text):
        """Section projet"""
        section_frame = tk.Frame(parent, bg=self.current_theme['bg_card'])
        section_frame.pack(fill='x', pady=(0, 25))
        
        title_label = tk.Label(section_frame,
                             text=title,
                             bg=self.current_theme['bg_card'],
                             fg=self.current_theme['text_primary'],
                             font=('SF Pro Display', 17, 'bold'))
        title_label.pack(anchor='w', pady=(0, 10))
        
        content_label = tk.Label(section_frame,
                               text=content_text,
                               bg=self.current_theme['bg_card'],
                               fg=self.current_theme['text_secondary'],
                               font=('SF Pro Display', 12),
                               justify='left',
                               wraplength=900)
        content_label.pack(anchor='w')

    def create_config_page(self):
        """Page configuration améliorée avec centrage et espacement"""
        config_container = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        config_container.pack(fill='both', expand=True)

        # Message d'erreur / info
        self.config_message_var = tk.StringVar(value="")
        msg_label = tk.Label(config_container, textvariable=self.config_message_var,
                             bg=self.current_theme['bg_secondary'],
                             fg=self.current_theme['danger'],
                             font=('SF Pro Display', 12, 'bold'))
        msg_label.pack(pady=(15,10), padx=20, anchor='w')

        # Mode
        mode_frame = tk.Frame(config_container, bg=self.current_theme['bg_secondary'])
        mode_frame.pack(pady=(10,20), padx=20)
        
        tk.Label(mode_frame, text="🎛️ Configuration Mode",
                 bg=self.current_theme['bg_secondary'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 16, 'bold')).pack(pady=(0,15))

        self.mode_var = tk.StringVar(value=self.config_mode)
        rb_frame = tk.Frame(mode_frame, bg=self.current_theme['bg_secondary'])
        rb_frame.pack()

        tk.Radiobutton(rb_frame, text="📐 1 Diameter × 4 Length",
                       variable=self.mode_var, value="1_diam_4_len",
                       bg=self.current_theme['bg_secondary'],
                       fg=self.current_theme['text_primary'],
                       font=('SF Pro Display', 12, 'bold'),
                       command=self.update_config_selection).pack(side='left', padx=20)

        tk.Radiobutton(rb_frame, text="📏 2 Diameters × 2 Lengths",
                       variable=self.mode_var, value="2_diam_2_len",
                       bg=self.current_theme['bg_secondary'],
                       fg=self.current_theme['text_primary'],
                       font=('SF Pro Display', 12, 'bold'),
                       command=self.update_config_selection).pack(side='left', padx=20)

        # Diamètres et longueurs
        form_frame = tk.Frame(config_container, bg=self.current_theme['bg_secondary'])
        form_frame.pack(pady=(10,30), padx=20, fill='x')

        # Diamètres
        tk.Label(form_frame, text="Select Diameter:",
                 bg=self.current_theme['bg_secondary'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 14, 'bold')).grid(row=0, column=0, sticky='w', pady=(0,10))
        
        self.diam_vars = []
        for i in range(2):
            var = tk.StringVar()
            cb = ttk.Combobox(form_frame, textvariable=var, values=ALLOWED_DIAMS, width=6,
                              font=('SF Pro Display', 12), state='readonly')
            cb.grid(row=0, column=i+1, padx=(5,10))
            self.diam_vars.append(var)

        # Longueurs
        tk.Label(form_frame, text="Select Length:",
                 bg=self.current_theme['bg_secondary'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 14, 'bold')).grid(row=1, column=0, sticky='w', pady=(15,10))

        self.len_vars = []
        len_values = [str(l) for l in ALLOWED_LEN]
        for i in range(4):
            var = tk.StringVar()
            cb = ttk.Combobox(form_frame, textvariable=var, values=len_values, width=6,
                              font=('SF Pro Display', 12), state='readonly')
            cb.grid(row=1, column=i+1, padx=(5,10))
            self.len_vars.append(var)

        # Bouton Configurer avec Canvas pour contrôle total de la couleur
        btn_frame = tk.Frame(config_container, bg=self.current_theme['bg_secondary'])
        btn_frame.pack(pady=(10,30))

        btn_canvas = tk.Canvas(btn_frame, width=200, height=45, 
                              bg=self.current_theme['bg_secondary'],
                              highlightthickness=0)
        btn_canvas.pack()
        
        def draw_config_button(hover=False):
            btn_canvas.delete('all')
            w, h = 200, 45
            r = 10
            
            # Couleur bleu clair
            bg_color = "#3b82f6" if hover else "#60a5fa"
            
            # Dessiner le bouton arrondi
            btn_canvas.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            btn_canvas.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            btn_canvas.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            # Texte
            btn_canvas.create_text(w//2, h//2, text="Configure",
                                  fill='white',
                                  font=('SF Pro Display', 12, 'bold'))
        
        draw_config_button()
        
        btn_canvas.bind('<Button-1>', lambda e: self.apply_configuration())
        btn_canvas.bind('<Enter>', lambda e: [btn_canvas.config(cursor='hand2'), draw_config_button(True)])
        btn_canvas.bind('<Leave>', lambda e: [btn_canvas.config(cursor=''), draw_config_button(False)])

        # Cadre des configurations déduites
        self.deduced_frame = tk.Frame(config_container, bg=self.current_theme['bg_card'],
                                      relief='solid', bd=1)
        self.deduced_frame.pack(fill='x', padx=20, pady=(10,10))
        self.deduced_text_var = tk.StringVar(value="Derived Configuration : ")
        tk.Label(self.deduced_frame, textvariable=self.deduced_text_var,
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 12),
                 justify='left', anchor='w').pack(padx=10, pady=10, anchor='w')

        # Initialisation
        self.update_config_selection()



    def apply_configuration(self):
        """Récupère la config, met à jour les bacs ET envoie à l'Arduino"""
        mode = self.mode_var.get()
        
        # Récupérer les valeurs selon le mode
        if mode == "1_diam_4_len":
            d1 = self.diam_vars[0].get()
            d2 = ""
            l1 = self.len_vars[0].get()
            l2 = self.len_vars[1].get()
            l3 = self.len_vars[2].get()
            l4 = self.len_vars[3].get()
            
            if not d1 or not l1 or not l2 or not l3 or not l4:
                self.config_message_var.set("⚠️ Select 1 diameter et 4 lengths")
                return
            
            # Trier les longueurs
            lengths = sorted([int(l1), int(l2), int(l3), int(l4)])
            combos = [(d1, lengths[0]), (d1, lengths[1]), (d1, lengths[2]), (d1, lengths[3])]
            
        elif mode == "2_diam_2_len":
            d1 = self.diam_vars[0].get()
            d2 = self.diam_vars[1].get()
            l1 = self.len_vars[0].get()
            l2 = self.len_vars[1].get()
            
            if not d1 or not d2 or not l1 or not l2:
                self.config_message_var.set("⚠️ Sélectionnez 2 diameters et 2 lengths")
                return
            
            if d1 == d2:
                self.config_message_var.set("⚠️ D1 != D2 required")
                return
            
            if l1 == l2:
                self.config_message_var.set("⚠️ L1 != L2 required")
                return
            
            # Créer les 4 combinaisons
            combos = [(d1, int(l1)), (d1, int(l2)), (d2, int(l1)), (d2, int(l2))]
        
        else:
            self.config_message_var.set("⚠️ Invalid Mode")
            return
        
        # Mettre à jour current_combos
        self.current_combos = [f"{d} × {l}mm" for d, l in combos]
        
        # Mise à jour du cadre des configurations déduites
        self.deduced_text_var.set("Derived Configuration :\n" + "\n".join(self.current_combos))
        
        # Mise à jour des labels des bacs dans le dashboard (avec vérification d'existence)
        self.update_bin_labels()
        
        # ENVOI À L'ARDUINO (appel à la fonction globale)
        mag = "yes"  # valeur par défaut
        logs = []
        for d, l in combos:
            result = send_one_combo(d, l, mag)
            logs.append(result)
        
        # Afficher le résultat
        self.config_message_var.set("✅ Sent Configuration:\n" + "\n".join(logs))
        self.add_log("Sent Configuration:")
        for log in logs:
            self.add_log(log)





    def update_bin_labels(self):
        """Met à jour les labels des bacs de manière sécurisée"""
        if not hasattr(self, 'bin_frames'):
            return
        
        for i, bin_id in enumerate([1, 2, 3, 4]):
            if i >= len(self.current_combos) or bin_id not in self.bin_frames:
                continue
            
            bin_frame = self.bin_frames[bin_id]
            
            # Vérifier que le widget existe toujours
            try:
                if not bin_frame.winfo_exists():
                    continue
            except:
                continue
            
            # Chercher et mettre à jour le label
            try:
                children = bin_frame.winfo_children()
                for child in children:
                    if isinstance(child, tk.Label):
                        # Vérifier que c'est bien le label du nom (pas le compteur ni l'indicateur)
                        font = child.cget('font')
                        if isinstance(font, tuple) and len(font) >= 2 and font[1] == 12:
                            child.configure(text=self.current_combos[i])
                            break
            except tk.TclError:
                # Le widget a été détruit entre temps, on ignore
                pass


    def update_config_selection(self):
        mode = self.mode_var.get()
        if mode == "1_diam_4_len":
            # 1 diamètre actif, 4 premières longueurs (déjà triées dans ALLOWED_LEN)
            for i, var in enumerate(self.diam_vars):
                var.set(ALLOWED_DIAMS[0] if i==0 else '')
            for i, var in enumerate(self.len_vars):
                var.set(str(ALLOWED_LEN[i]) if i<4 else '')
        elif mode == "2_diam_2_len":
            # 2 premiers diamètres actifs, 2 premières longueurs (déjà triés)
            for i, var in enumerate(self.diam_vars):
                var.set(ALLOWED_DIAMS[i] if i<2 else '')
            for i, var in enumerate(self.len_vars):
                var.set(str(ALLOWED_LEN[i]) if i<2 else '')


    def calculate_energy(self):
        """Calcule la consommation d'énergie en temps réel"""
        # Définition des composants
        components = {
            "raspberry_pi": {"V": 5, "I_idle": 0.3, "I_max": 3.1},
            "esp32": {"V": 5, "I_idle": 0.05, "I_max": 0.3},
            "servo_13kg_1": {"V": 5, "I_idle": 0.3, "I_max": 2.4},
            "servo_35kg": {"V": 5, "I_idle": 0.5, "I_max": 5},
            "servo_3A1": {"V": 5, "I_idle": 0.3, "I_max": 3},
            "servo_3A2": {"V": 5, "I_idle": 0.3, "I_max": 3},
            "camera_1": {"V": 5, "I_idle": 0.2, "I_max": 0.5},
        }
        
        # Calcul du temps écoulé
        now = time.time()
        dt = now - self.last_time
        self.last_time = now
        
        # Calcul de la puissance totale
        power_total = 0
        
        for name, comp in components.items():
            V = comp["V"]
            I_idle = comp["I_idle"]
            I_max = comp["I_max"]
            
            # Composants TOUJOURS actifs
            if name in ["raspberry_pi", "esp32", "camera_1"]:
                load = 1
                I = I_idle + (I_max - I_idle) * load
                P = V * I
                power_total += P
            
            # ✅ MOTEURS : seulement si état > 0
            else:
                load = self.arduino_state.get(name, 0)
                if load > 0:  # ← Ne calculer que si le moteur est actif
                    I = I_idle + (I_max - I_idle) * load
                    P = V * I
                    power_total += P
                # Sinon : P = 0, on n'ajoute rien
        
        # Énergie cumulée (Wh)
        last_E = self.energy_cumulative[-1]
        dE = (power_total * dt) / 3600
        new_E = last_E + dE
        
        self.energy_cumulative.append(new_E)
        self.energy_values.append(power_total)
        
        # Limiter la taille
        if len(self.energy_cumulative) > self.MAX_SPEED_POINTS:
            self.energy_cumulative = self.energy_cumulative[-self.MAX_SPEED_POINTS:]
        if len(self.energy_values) > self.MAX_SPEED_POINTS:
            self.energy_values = self.energy_values[-self.MAX_SPEED_POINTS:] 



    def create_analytics_page(self):
        """Page analytics avec 5 graphes empilés et scrollables"""
        # Container principal avec scrollbar
        analytics_container = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        analytics_container.pack(fill='both', expand=True)
        
        # Canvas pour le scrolling
        canvas = tk.Canvas(analytics_container, bg=self.current_theme['bg_secondary'], highlightthickness=0)
        scrollbar = tk.Scrollbar(analytics_container, orient="vertical", command=canvas.yview)
        scrollable_frame = tk.Frame(canvas, bg=self.current_theme['bg_secondary'])
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas_window = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        
        # Fonction pour ajuster la largeur du frame scrollable
        def configure_scroll_region(event):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas.itemconfig(canvas_window, width=event.width)
        
        canvas.bind('<Configure>', configure_scroll_region)
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Pack canvas et scrollbar
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # Bind mousewheel pour scroll
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        
        def _bind_to_mousewheel(event):
            canvas.bind_all("<MouseWheel>", _on_mousewheel)
        
        def _unbind_from_mousewheel(event):
            canvas.unbind_all("<MouseWheel>")
        
        canvas.bind('<Enter>', _bind_to_mousewheel)
        canvas.bind('<Leave>', _unbind_from_mousewheel)
        
        # ✅ Créer les 5 graphes
        self.create_analytics_graph(scrollable_frame, "speed", "🔄 Speed of the Conveyor's motor", "Speed (RPM)", "#f97316")
        self.create_analytics_graph(scrollable_frame, "speed_ms", "🚀 Speed of Conveyor", "Speed (m/s)", "#ff6b6b")  # ✅ NOUVEAU graphe
        self.create_analytics_graph(scrollable_frame, "energy", "⚡ Energy Consumption", "Energy (W)", "#10b981")
        self.create_analytics_graph(scrollable_frame, "motor2", "🎯 Speed of lifter motor", "Speed (RPM)", "#8b5cf6")
        self.create_analytics_graph(scrollable_frame, "torque", "⚙️ Torque of Conveyor", "Torque (Nm)", "#3b82f6")
        
        # Forcer une mise à jour initiale
        scrollable_frame.update_idletasks()
        canvas.configure(scrollregion=canvas.bbox("all"))

    def create_analytics_graph(self, parent, graph_type, title, ylabel, color):
        """Crée un graphe analytics individuel"""
        # Card container avec hauteur fixe
        card = tk.Frame(parent, bg=self.current_theme['bg_card'],
                       relief='raised', bd=1, highlightbackground=self.current_theme['border'],
                       highlightthickness=1)
        card.pack(fill='x', padx=20, pady=15, ipady=10)
        
        # Titre
        title_label = tk.Label(card,
                              text=title,
                              bg=self.current_theme['bg_card'],
                              fg=self.current_theme['text_primary'],
                              font=('SF Pro Display', 16, 'bold'))
        title_label.pack(pady=(15, 5), padx=30, anchor='w')
        
        # Container du graphe avec taille fixe
        graph_container = tk.Frame(card, bg=self.current_theme['bg_secondary'], width=1200, height=300)
        graph_container.pack(fill='both', padx=20, pady=(5, 15))
        graph_container.pack_propagate(False)
        
        # ✅ Style IDENTIQUE au dashboard
        fig = Figure(figsize=(12, 3.5), facecolor=self.current_theme['bg_secondary'], dpi=100)
        ax = fig.add_subplot(111)
        
        ax.set_facecolor(self.current_theme['bg_secondary'])
        ax.set_xlabel('Time', color=self.current_theme['text_secondary'], fontsize=10)
        ax.set_ylabel(ylabel, color=self.current_theme['text_secondary'], fontsize=10)
        ax.grid(True, alpha=0.15, color=self.current_theme['text_accent'], linestyle='-', linewidth=0.5)
        ax.tick_params(colors=self.current_theme['text_secondary'], labelsize=9)
        
        ax.spines['top'].set_visible(False)
        ax.spines['right'].set_visible(False)
        ax.spines['left'].set_color(self.current_theme['text_accent'])
        ax.spines['bottom'].set_color(self.current_theme['text_accent'])
        
        # ✅ Ligne avec le même style que le dashboard
        line, = ax.plot([], [], color=color, linewidth=2.5, alpha=0.9)
        
        fig.subplots_adjust(left=0.08, right=0.97, top=0.95, bottom=0.15)
        
        # Canvas
        canvas = FigureCanvasTkAgg(fig, master=graph_container)
        canvas.draw()
        canvas.get_tk_widget().pack(fill='both', expand=True)
        canvas.get_tk_widget().configure(bg=self.current_theme['bg_secondary'], highlightthickness=0)
        
        # Sauvegarder les références
        setattr(self, f'fig_{graph_type}', fig)
        setattr(self, f'ax_{graph_type}', ax)
        setattr(self, f'line_{graph_type}', line)
        setattr(self, f'canvas_{graph_type}', canvas)
        
    def update_analytics_graphs(self):
        """Met à jour tous les graphes de la page analytics"""
        graphs = [
            ('torque', self.torque_values, 'Torque (Nm)'),
            ('energy', self.energy_values, 'Puissance (W)'),
            ('speed', self.speed_values, 'Vitesse (RPM)'),
            ('speed_ms', self.conveyor_speed_ms_values, 'Vitesse (m/s)'),  # ✅ NOUVEAU graphe
            ('motor2', self.motor2_speed_values, 'Vitesse (RPM)')
        ]
        
        for graph_type, values, ylabel in graphs:
            if values and hasattr(self, f'line_{graph_type}'):
                try:
                    line = getattr(self, f'line_{graph_type}')
                    ax = getattr(self, f'ax_{graph_type}')
                    canvas = getattr(self, f'canvas_{graph_type}')
                    
                    times = list(range(len(values)))
                    line.set_data(times, values)
                    ax.set_xlim(0, max(len(values), 10))
                    
                    if values:
                        y_min, y_max = min(values), max(values)
                        margin = (y_max - y_min) * 0.1 if y_max != y_min else 10
                        ax.set_ylim(y_min - margin, y_max + margin)
                    
                    canvas.draw()
                except:
                    pass

            
    def create_monitor_page(self):
            """Page monitoring - Console minimaliste noire avec bordure simple"""
            monitor_container = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
            monitor_container.pack(fill='both', expand=True)
            
            # Zone de texte pour les logs avec scrollbar intégrée
            self.log_text = tk.Text(monitor_container,
                                   bg='#000000',  # Noir pur
                                   fg='#00ff88',  # Vert terminal
                                   font=('Courier New', 11),
                                   relief='solid',
                                   bd=1,  # Bordure simple de 1px
                                   highlightbackground='#333333',  # Bordure gris foncé
                                   highlightthickness=1,
                                   padx=15,
                                   pady=15,
                                   wrap='word')
            
            # Scrollbar
            scrollbar = tk.Scrollbar(monitor_container, command=self.log_text.yview, 
                                    bg='#1a1a1a', troughcolor='#000000', 
                                    activebackground='#333333')
            self.log_text.config(yscrollcommand=scrollbar.set)
            
            # Pack
            scrollbar.pack(side='right', fill='y', padx=(0, 20), pady=20)
            self.log_text.pack(side='left', fill='both', expand=True, padx=(20, 0), pady=20)
    
    
        # =============== STREAM CLIENT (pour la vidéo venant de la Raspberry) ===============
    def start_camera_client(self):
        IP_RASPBERRY = "172.20.10.2"   # <-- ton IP ici
        PORT = 9999

        self.client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

        try:
            print("Connexion au flux vidéo…")
            self.client_socket.connect((IP_RASPBERRY, PORT))
            print("Connecté au flux caméra Raspberry")
        except Exception as e:
            print("❌ Erreur connexion caméra:", e)
            return

        self.data = b""
        self.payload_size = struct.calcsize("Q")

        self.update_camera_stream()


    def update_camera_stream(self):
        try:
            # Lire la taille de l'image
            while len(self.data) < self.payload_size:
                packet = self.client_socket.recv(4096)
                if not packet:
                    return
                self.data += packet

            packed_msg_size = self.data[:self.payload_size]
            self.data = self.data[self.payload_size:]
            msg_size = struct.unpack("Q", packed_msg_size)[0]

            # Lire l'image complète
            while len(self.data) < msg_size:
                self.data += self.client_socket.recv(4096)

            frame_data = self.data[:msg_size]
            self.data = self.data[msg_size:]

            frame = pickle.loads(frame_data)
            frame = cv2.resize(frame, (800, 600))   # <-- Zoom visuel Tkinter
            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            img = Image.fromarray(frame)
            imgtk = ImageTk.PhotoImage(image=img)

            self.camera_label.imgtk = imgtk
            self.camera_label.configure(image=imgtk)

        except Exception as e:
            print("Erreur caméra:", e)

        self.root.after(10, self.update_camera_stream)



    def create_camera_page(self):
        camera_container = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        camera_container.pack(fill='both', expand=True, padx=20, pady=20)

        camera_frame = tk.Frame(camera_container, 
                               bg='#000000',
                               relief='solid',
                               bd=2,
                               highlightbackground='#3b82f6',
                               highlightthickness=2)
        camera_frame.pack(fill='both', expand=True)

        # Label dans lequel on mettra les images reçues
        self.camera_label = tk.Label(camera_frame, bg='#000000')
        self.camera_label.pack(expand=True)

        # Lancer la connexion au flux vidéo Raspberry
        self.start_camera_client()



    def create_matrix_page(self):
        """Page Matrice de vis - grand tableau, bordures bleues, longueurs 5 mm"""
        # Mettre le titre exact
        self.page_title.configure(text="Screw Matrix")

        # Container extérieur (pour centrer si nécessaire)
        outer = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        outer.pack(fill='both', expand=True, padx=0, pady=0)

        # On crée un frame central qui prendra toute la largeur disponible
        table_frame = tk.Frame(outer, bg=self.current_theme['bg_secondary'])
        table_frame.pack(fill='both', expand=True)

        # Diamètres et longueurs
        diams = ["M3", "M4", "M5", "M6"]
        longs = [str(l) for l in range(10, 80, 10)]  # 10,20,...,80

        self.matrix_cells = {}

        # Configurer grid pour expansion (chaque colonne prend de la place)
        for col in range(len(diams) + 1):
            table_frame.grid_columnconfigure(col, weight=1, uniform='col')
        for row in range(len(longs) + 1):
            table_frame.grid_rowconfigure(row, weight=1)

        border_color = '#3b82f6'  # bleu

        cell_width = 18
        cell_height = 3

        def make_cell(parent, text, row, col, is_header=False):
            # Frame extérieure = couleur de la bordure
            border = tk.Frame(parent, bg=border_color, bd=0)
            border.grid(row=row, column=col, padx=2, pady=2, sticky='nsew')
            # Intérieur = fond du thème (donne aspect "bordure")
            inner = tk.Frame(border, bg=self.current_theme['bg_secondary'])
            inner.pack(fill='both', expand=True, padx=2, pady=2)
            lbl = tk.Label(inner, text=text,
                           bg=self.current_theme['bg_secondary'],
                           fg=self.current_theme['text_primary'],
                           font=('SF Pro Display', 12, 'bold' if is_header else 'normal'))
            lbl.pack(expand=True, fill='both')
            return lbl

        # première cellule vide
        make_cell(table_frame, "", 0, 0, is_header=True)

        # entêtes diamètres
        for j, d in enumerate(diams):
            make_cell(table_frame, d, 0, j+1, is_header=True)

        # lignes longueurs + cellules
        for i, l in enumerate(longs):
            make_cell(table_frame, l, i+1, 0, is_header=True)
            for j, d in enumerate(diams):
                lbl = make_cell(table_frame, "0", i+1, j+1, is_header=False)
                self.matrix_cells[(d, str(l))] = lbl

        # Pour s'assurer que le tableau est centré et très large : on peut ajouter padding extérieur
        outer.update_idletasks()



    def add_vis_to_matrix(self, diameter, length):
        key = (diameter, str(length))
        if key in self.matrix_cells:
            current = int(self.matrix_cells[key]["text"])
            self.matrix_cells[key].config(text=str(current + 1))

        

    def create_testing_page(self):
        """Page testing avec contrôle des 3 moteurs Arduino + bouton TEST"""
        testing_container = tk.Frame(self.pages_container, bg=self.current_theme['bg_secondary'])
        testing_container.pack(fill='both', expand=True, padx=0, pady=0)
        
        # === EN-TÊTE AVEC BOUTONS TEST MODE ET STOP ===
        header_frame = tk.Frame(testing_container, bg=self.current_theme['bg_secondary'])
        header_frame.pack(fill='x', pady=(0,20))
        
        # Titre
        title_label = tk.Label(header_frame,
                              text="⚠️ TEST mode - Manual control of motors",
                              bg=self.current_theme['bg_secondary'],
                              fg=self.current_theme['warning'],
                              font=('SF Pro Display', 16, 'bold'))
        title_label.pack(side='left', anchor='w')
        
        # Container pour les boutons à droite
        buttons_container = tk.Frame(header_frame, bg=self.current_theme['bg_secondary'])
        buttons_container.pack(side='right')
        
        # Bouton STOP D'URGENCE
        stop_btn = tk.Canvas(buttons_container, width=220, height=50,
                            bg=self.current_theme['bg_secondary'],
                            highlightthickness=0)
        stop_btn.pack(side='right', padx=(10, 0))
        
        def draw_stop_button(hover=False):
            stop_btn.delete('all')
            w, h = 220, 50
            r = 12
            
            bg_color = "#cc0000" if hover else self.current_theme['danger']
            
            stop_btn.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            stop_btn.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            stop_btn.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            stop_btn.create_text(w//2, h//2, text="🚨 EMERGENCY STOP",
                               fill='white',
                               font=('SF Pro Display', 12, 'bold'))
        
        def emergency_stop():
            self.send_motor_off_command()
        
        stop_btn.bind('<Configure>', lambda e: draw_stop_button())
        stop_btn.bind('<Button-1>', lambda e: emergency_stop())
        stop_btn.bind('<Enter>', lambda e: [stop_btn.config(cursor='hand2'), draw_stop_button(True)])
        stop_btn.bind('<Leave>', lambda e: [stop_btn.config(cursor=''), draw_stop_button(False)])
        
        # Bouton TEST MODE (toggle)
        if not hasattr(self, 'test_mode_active'):
            self.test_mode_active = False
        
        test_mode_btn = tk.Canvas(buttons_container, width=200, height=50,
                                 bg=self.current_theme['bg_secondary'],
                                 highlightthickness=0)
        test_mode_btn.pack(side='right', padx=(0, 10))
        
        def draw_test_mode_button(hover=False):
            test_mode_btn.delete('all')
            w, h = 200, 50
            r = 12
            
            if self.test_mode_active:
                bg_color = "#00d84a" if hover else self.current_theme['success']
                text = "✓ ACTIVE TEST"
            else:
                bg_color = "#ff8c00" if hover else "#ffaa00"
                text = "🔧 ACTIVATE TEST"
            
            test_mode_btn.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            test_mode_btn.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            test_mode_btn.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            test_mode_btn.create_text(w//2, h//2, text=text,
                                     fill='white',
                                     font=('SF Pro Display', 12, 'bold'))
        
        def toggle_test_mode():
            self.test_mode_active = not self.test_mode_active
            if ser:
                if self.test_mode_active:
                    ser.write(b"TEST\n")
                    self.add_log("🔧TEST mode activated on Arduino")
                else:
                    ser.write(b"EXIT\n")
                    self.add_log("🔧 TEST mode desactivated on Arduino")
            else:
                self.add_log("❌ No Serial connexion")
            draw_test_mode_button()
        
        test_mode_btn.bind('<Configure>', lambda e: draw_test_mode_button())
        test_mode_btn.bind('<Button-1>', lambda e: toggle_test_mode())
        test_mode_btn.bind('<Enter>', lambda e: [test_mode_btn.config(cursor='hand2'), draw_test_mode_button(True)])
        test_mode_btn.bind('<Leave>', lambda e: [test_mode_btn.config(cursor=''), draw_test_mode_button(False)])
        
        
        # === GRILLE DES MOTEURS ===
        motors_grid = tk.Frame(testing_container, bg=self.current_theme['bg_secondary'])
        motors_grid.pack(fill='both', expand=True)
        
        # Configuration de la grille - 2 colonnes, 2 lignes
        motors_grid.grid_rowconfigure(0, weight=1)
        motors_grid.grid_rowconfigure(1, weight=1)
        motors_grid.grid_columnconfigure(0, weight=1)
        motors_grid.grid_columnconfigure(1, weight=1)
        
        # Motor 1: Lucas (Servo avec vitesse 0-180) - position 0,0
        self.create_continuous_motor_card(motors_grid, 1, "Servo continuous lifter", 0, 0)
        
        # Motor 2: Continu2 (Continu) - position 0,1
        self.create_continuous_motor_card(motors_grid, 2, "Servo Continuous conveyor", 0, 1)
        
        # Motor 3: Burak (Servo) - position 1,0
        self.create_servo_motor_card(motors_grid, 3, "Servo bins", 1, 0)
        
        # Motor 4: Nouveau Servo - position 1,1
        self.create_servo_motor_card(motors_grid, 4, "Servo slope", 1, 1)

    def create_stop_all_card(self, parent, row, col):
        """Carte STOP d'urgence qui envoie la commande STOP à l'Arduino"""
        stop_all_frame = tk.Frame(parent, 
                                 bg=self.current_theme['bg_card'],
                                 relief='solid',
                                 bd=1,
                                 highlightbackground=self.current_theme['border'],
                                 highlightthickness=1)
        stop_all_frame.grid(row=row, column=col, padx=8, pady=8, sticky='nsew')
        
        stop_content = tk.Frame(stop_all_frame, bg=self.current_theme['bg_card'])
        stop_content.pack(fill='both', expand=True, padx=20, pady=15)
        
        tk.Label(stop_content,
                 text="🚨",
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['danger'],
                 font=('SF Pro Display', 48)).pack(pady=(20, 10))
        
        tk.Label(stop_content,
                 text="Emergency STOP",
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 18, 'bold')).pack(pady=(0, 5))
        
        tk.Label(stop_content,
                 text="Send the STOP command to all motors",
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['text_secondary'],
                 font=('SF Pro Display', 10),
                 justify='center').pack(pady=(0, 30))
        
        emergency_btn = tk.Canvas(stop_content, height=60, bg=self.current_theme['bg_card'],
                                 highlightthickness=0)
        emergency_btn.pack(fill='x')
        
        def draw_emergency_button(hover=False):
            emergency_btn.delete('all')
            w, h = emergency_btn.winfo_width(), 60
            if w < 10:
                w = 300
            r = 15
            
            bg_color = "#cc0000" if hover else self.current_theme['danger']
            
            emergency_btn.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            emergency_btn.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            emergency_btn.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            emergency_btn.create_text(w//2, h//2, text="⏹ EMERGENCY STOP",
                                     fill='white',
                                     font=('SF Pro Display', 14, 'bold'))
        
        def emergency_stop():
            self.send_motor_command(0, "stop", "0", "0")
        
        emergency_btn.bind('<Configure>', lambda e: draw_emergency_button())
        emergency_btn.bind('<Button-1>', lambda e: emergency_stop())
        emergency_btn.bind('<Enter>', lambda e: [emergency_btn.config(cursor='hand2'), draw_emergency_button(True)])
        emergency_btn.bind('<Leave>', lambda e: [emergency_btn.config(cursor=''), draw_emergency_button(False)])


    def create_continuous_motor_card(self, parent, motor_id, title, row, col):
        """Carte de contrôle pour moteur continu avec vitesse 0-180 et boutons côte à côte"""
        card = tk.Frame(parent, 
                       bg=self.current_theme['bg_card'],
                       relief='solid',
                       bd=1,
                       highlightbackground=self.current_theme['border'],
                       highlightthickness=1)
        card.grid(row=row, column=col, padx=8, pady=8, sticky='nsew')
        
        content = tk.Frame(card, bg=self.current_theme['bg_card'])
        content.pack(fill='both', expand=True, padx=20, pady=15)
        
        
        # En-tête
        header = tk.Frame(content, bg=self.current_theme['bg_card'])
        header.pack(fill='x', pady=(0, 12))
        
        left_header = tk.Frame(header, bg=self.current_theme['bg_card'])
        left_header.pack(side='left', fill='x', expand=True)
        
        icon_label = tk.Label(left_header,
                             text="🔄",
                             bg=self.current_theme['bg_card'],
                             fg=self.current_theme['button_primary'],
                             font=('SF Pro Display', 24))
        icon_label.pack(side='left', padx=(0, 10))
        
        title_frame = tk.Frame(left_header, bg=self.current_theme['bg_card'])
        title_frame.pack(side='left', fill='x', expand=True)
        
        tk.Label(title_frame,
                 text=title,
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 16, 'bold')).pack(anchor='w')
        

        
        # Séparateur
        separator = tk.Frame(content, bg=self.current_theme['border'], height=1)
        separator.pack(fill='x', pady=(0, 12))
        
        # Contrôle de valeur
        speed_frame = tk.Frame(content, bg=self.current_theme['bg_card'])
        speed_frame.pack(fill='x', pady=(0, 15))
        
        tk.Label(speed_frame,
                 text="⚡ Speed (0-180)",
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 11, 'bold')).pack(anchor='w', pady=(0, 5))
        
        speed_var = tk.StringVar(value="170")
        speed_entry = tk.Entry(speed_frame,
                              textvariable=speed_var,
                              bg=self.current_theme['bg_accent'],
                              fg=self.current_theme['text_primary'],
                              font=('SF Pro Display', 12),
                              relief='flat',
                              bd=0)
        speed_entry.pack(fill='x', ipady=8, padx=5)
        
        # Slider
        speed_slider = tk.Scale(speed_frame,
                               from_=0,
                               to=180,
                               orient='horizontal',
                               variable=speed_var,
                               bg=self.current_theme['bg_card'],
                               fg=self.current_theme['text_primary'],
                               troughcolor=self.current_theme['bg_accent'],
                               highlightthickness=0,
                               font=('SF Pro Display', 8),
                               showvalue=False)
        speed_slider.pack(fill='x', pady=(5, 0))
        
        # Boutons ON/OFF côte à côte
        buttons_frame = tk.Frame(content, bg=self.current_theme['bg_card'])
        buttons_frame.pack(fill='x', pady=(0, 0))
        
        # Bouton ON
        on_btn = tk.Canvas(buttons_frame, height=50, bg=self.current_theme['bg_card'],
                          highlightthickness=0)
        on_btn.pack(side='left', fill='x', expand=True, padx=(0, 5))
        
        def draw_on_button(hover=False):
            on_btn.delete('all')
            w, h = on_btn.winfo_width(), 50
            if w < 10:
                w = 150
            r = 10
            
            bg_color = "#00d84a" if hover else self.current_theme['success']
            
            on_btn.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            on_btn.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            on_btn.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            on_btn.create_text(w//2, h//2, text="▶ ON",
                              fill='white',
                              font=('SF Pro Display', 14, 'bold'))
        
        def turn_on():
            speed = speed_var.get()
            self.send_motor_on_command(motor_id, speed)
        
        on_btn.bind('<Configure>', lambda e: draw_on_button())
        on_btn.bind('<Button-1>', lambda e: turn_on())
        on_btn.bind('<Enter>', lambda e: [on_btn.config(cursor='hand2'), draw_on_button(True)])
        on_btn.bind('<Leave>', lambda e: [on_btn.config(cursor=''), draw_on_button(False)])
        
        # Bouton OFF
        off_btn = tk.Canvas(buttons_frame, height=50, bg=self.current_theme['bg_card'],
                           highlightthickness=0)
        off_btn.pack(side='left', fill='x', expand=True, padx=(5, 0))
        
        def draw_off_button(hover=False):
            off_btn.delete('all')
            w, h = off_btn.winfo_width(), 50
            if w < 10:
                w = 150
            r = 10
            
            bg_color = "#ff6b5f" if hover else self.current_theme['danger']
            
            off_btn.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            off_btn.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            off_btn.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            off_btn.create_text(w//2, h//2, text="⏹ OFF",
                               fill='white',
                               font=('SF Pro Display', 14, 'bold'))
        
        def turn_off():
            self.send_motor_off_command()
        
        off_btn.bind('<Configure>', lambda e: draw_off_button())
        off_btn.bind('<Button-1>', lambda e: turn_off())
        off_btn.bind('<Enter>', lambda e: [off_btn.config(cursor='hand2'), draw_off_button(True)])
        off_btn.bind('<Leave>', lambda e: [off_btn.config(cursor=''), draw_off_button(False)])

    def create_servo_motor_card(self, parent, motor_id, title, row, col):
        """Carte de contrôle pour servo avec boutons ON/OFF côte à côte"""
        card = tk.Frame(parent,
                       bg=self.current_theme['bg_card'],
                       relief='solid',
                       bd=1,
                       highlightbackground=self.current_theme['border'],
                       highlightthickness=1)
        card.grid(row=row, column=col, padx=8, pady=8, sticky='nsew')
        
        content = tk.Frame(card, bg=self.current_theme['bg_card'])
        content.pack(fill='both', expand=True, padx=20, pady=15)
        
        # En-tête
        header = tk.Frame(content, bg=self.current_theme['bg_card'])
        header.pack(fill='x', pady=(0, 12))
        
        left_header = tk.Frame(header, bg=self.current_theme['bg_card'])
        left_header.pack(side='left', fill='x', expand=True)
        
        icon_label = tk.Label(left_header,
                             text="🎯",
                             bg=self.current_theme['bg_card'],
                             fg=self.current_theme['warning'],
                             font=('SF Pro Display', 24))
        icon_label.pack(side='left', padx=(0, 10))
        
        title_frame = tk.Frame(left_header, bg=self.current_theme['bg_card'])
        title_frame.pack(side='left', fill='x', expand=True)
        
        tk.Label(title_frame,
                 text=title,
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 16, 'bold')).pack(anchor='w')
        
        
        # Séparateur
        separator = tk.Frame(content, bg=self.current_theme['border'], height=1)
        separator.pack(fill='x', pady=(0, 12))
        
        # Contrôle de position
        position_frame = tk.Frame(content, bg=self.current_theme['bg_card'])
        position_frame.pack(fill='x', pady=(0, 15))
        
        tk.Label(position_frame,
                 text="📐 Position (degrees)",
                 bg=self.current_theme['bg_card'],
                 fg=self.current_theme['text_primary'],
                 font=('SF Pro Display', 11, 'bold')).pack(anchor='w', pady=(0, 5))
        
        position_var = tk.StringVar(value="90")
        position_entry = tk.Entry(position_frame,
                                 textvariable=position_var,
                                 bg=self.current_theme['bg_accent'],
                                 fg=self.current_theme['text_primary'],
                                 font=('SF Pro Display', 12),
                                 relief='flat',
                                 bd=0)
        position_entry.pack(fill='x', ipady=8, padx=5)
        
        position_slider = tk.Scale(position_frame,
                                   from_=0,
                                   to=180,
                                   orient='horizontal',
                                   variable=position_var,
                                   bg=self.current_theme['bg_card'],
                                   fg=self.current_theme['text_primary'],
                                   troughcolor=self.current_theme['bg_accent'],
                                   highlightthickness=0,
                                   font=('SF Pro Display', 8),
                                   showvalue=False)
        position_slider.pack(fill='x', pady=(5, 0))

        # 🚨 Limite uniquement pour le servo D
        if motor_id == "D" or motor_id == 4:  # selon comment tu appelles la fonction
            position_slider.config(from_=45, to=80)

        
        # Boutons ON/OFF côte à côte
        buttons_frame = tk.Frame(content, bg=self.current_theme['bg_card'])
        buttons_frame.pack(fill='x', pady=(0, 0))
        
        # Bouton ON
        on_btn = tk.Canvas(buttons_frame, height=50, bg=self.current_theme['bg_card'],
                          highlightthickness=0)
        on_btn.pack(side='left', fill='x', expand=True, padx=(0, 5))
        
        def draw_on_button(hover=False):
            on_btn.delete('all')
            w, h = on_btn.winfo_width(), 50
            if w < 10:
                w = 150
            r = 10
            
            bg_color = "#00d84a" if hover else self.current_theme['success']
            
            on_btn.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            on_btn.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            on_btn.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            on_btn.create_text(w//2, h//2, text="▶ ON",
                              fill='white',
                              font=('SF Pro Display', 14, 'bold'))
        
        def turn_on():
            position = position_var.get()
            self.send_motor_on_command(motor_id, position)
        
        on_btn.bind('<Configure>', lambda e: draw_on_button())
        on_btn.bind('<Button-1>', lambda e: turn_on())
        on_btn.bind('<Enter>', lambda e: [on_btn.config(cursor='hand2'), draw_on_button(True)])
        on_btn.bind('<Leave>', lambda e: [on_btn.config(cursor=''), draw_on_button(False)])
        
        # Bouton OFF
        off_btn = tk.Canvas(buttons_frame, height=50, bg=self.current_theme['bg_card'],
                           highlightthickness=0)
        off_btn.pack(side='left', fill='x', expand=True, padx=(5, 0))
        
        def draw_off_button(hover=False):
            off_btn.delete('all')
            w, h = off_btn.winfo_width(), 50
            if w < 10:
                w = 150
            r = 10
            
            bg_color = "#ff6b5f" if hover else self.current_theme['danger']
            
            off_btn.create_oval(0, 0, r*2, h, fill=bg_color, outline='')
            off_btn.create_oval(w-r*2, 0, w, h, fill=bg_color, outline='')
            off_btn.create_rectangle(r, 0, w-r, h, fill=bg_color, outline='')
            
            off_btn.create_text(w//2, h//2, text="⏹ OFF",
                               fill='white',
                               font=('SF Pro Display', 14, 'bold'))
        
        def turn_off():
            self.send_motor_off_command()
        
        off_btn.bind('<Configure>', lambda e: draw_off_button())
        off_btn.bind('<Button-1>', lambda e: turn_off())
        off_btn.bind('<Enter>', lambda e: [off_btn.config(cursor='hand2'), draw_off_button(True)])
        off_btn.bind('<Leave>', lambda e: [off_btn.config(cursor=''), draw_off_button(False)])

    def send_motor_on_command(self, motor_id, value):
        """Envoie la commande ON (lettre correspondante) avec la valeur au moteur"""
        if ser is None:
            self.add_log(f"❌ Error: No serial connexion")
            return
        
        try:
            # Mapping des moteurs selon le code Arduino:
            # Motor 1 (Lucas) = Servo pin 18 → commande L= (vitesse 0-180)
            # Motor 2 (Continu2) = Moteur continu pin 5 → commande C= (vitesse 0-180)
            # Motor 3 (Burak) = Servo pin 15 → commande B= (position 0-180)
            # Motor 4 = Nouveau servo → commande D= (position 0-180)
            
            if motor_id == 1:
                message = f"L={value}\n"
                ser.write(message.encode())
                self.add_log(f"✅ Motor 1 (Lucas) ON - Speed: {value}")
                
            elif motor_id == 2:
                message = f"C={value}\n"
                ser.write(message.encode())
                self.add_log(f"✅ Motor 2 (Continu2) ON - Speed: {value}")
                
            elif motor_id == 3:
                message = f"B={value}\n"
                ser.write(message.encode())
                self.add_log(f"✅ Motor 3 (Burak) ON - Position: {value}°")
                
            elif motor_id == 4:
                message = f"D={value}\n"
                ser.write(message.encode())
                self.add_log(f"✅ Motor 4 (Servo D) ON - Position: {value}°")
            else:
                self.add_log(f"⚠️ Motor ID {motor_id} invalide")
                
        except Exception as e:
            self.add_log(f"❌ Send error: {e}")

    def send_motor_off_command(self):
        """Envoie la commande STOP à tous les moteurs"""
        if ser is None:
            self.add_log(f"❌ Error: No Serial connexion")
            return
        
        try:
            message = "STOP\n"
            ser.write(message.encode())
            self.add_log(f"🛑 STOP command sent – All motors stopped")
                
        except Exception as e:
            self.add_log(f"❌ Send error: {e}")


    def create_modern_speed_graph(self, parent):
        """Graphique de vitesse"""
        # Récupérer le frame card
        if isinstance(parent, tk.Frame):
            card = parent
        else:
            card = parent.winfo_children()[0]
            
        graph_container = tk.Frame(card, bg=self.current_theme['bg_card'])
        graph_container.pack(fill='both', expand=True, padx=30, pady=20)
        
        self.fig_speed = Figure(figsize=(6, 4), facecolor=self.current_theme['bg_card'])
        self.ax_speed = self.fig_speed.add_subplot(111)
        
        # Style du graphique adapté au thème
        self.ax_speed.set_facecolor(self.current_theme['bg_card'])
        self.ax_speed.set_title('Speed (RPM)', 
                              color=self.current_theme['text_primary'],
                              fontsize=14, fontweight='bold', pad=15)
        self.ax_speed.set_xlabel('Time', color=self.current_theme['text_secondary'], fontsize=10)
        self.ax_speed.set_ylabel('RPM', color=self.current_theme['text_secondary'], fontsize=10)
        
        # Grille et style
        self.ax_speed.grid(True, alpha=0.15, color=self.current_theme['text_accent'], 
                          linestyle='-', linewidth=0.5)
        self.ax_speed.tick_params(colors=self.current_theme['text_secondary'], labelsize=9)
        
        # Supprime les bordures supérieure et droite
        self.ax_speed.spines['top'].set_visible(False)
        self.ax_speed.spines['right'].set_visible(False)
        self.ax_speed.spines['left'].set_color(self.current_theme['text_accent'])
        self.ax_speed.spines['bottom'].set_color(self.current_theme['text_accent'])
        
        # Ligne de données
        self.line_speed, = self.ax_speed.plot([], [], 
                                            color=self.current_theme['button_primary'],
                                            linewidth=2.5,
                                            alpha=0.9)
        
        self.canvas_speed = FigureCanvasTkAgg(self.fig_speed, master=graph_container)
        self.canvas_speed.get_tk_widget().configure(bg=self.current_theme['bg_card'])
        self.canvas_speed.get_tk_widget().pack(fill='both', expand=True)
        
        self.fig_speed.tight_layout()
        
    def add_log(self, message):
        """Ajoute au log"""
        timestamp = datetime.now().strftime("%H:%M:%S")
        if hasattr(self, 'log_text'):
            self.log_text.insert(tk.END, f"[{timestamp}] {message}\n")
            self.log_text.see(tk.END)
            
    def update_dashboard_data(self):
        """Met à jour les compteurs, labels des bacs et TOUS les graphes"""
        # Labels des bins (compteurs)
        if hasattr(self, 'bin_labels'):
            for bin_id, label in self.bin_labels.items():
                try:
                    if label.winfo_exists():
                        label.configure(text=str(self.counts[bin_id]))
                except:
                    pass

        # Labels des combinaisons (utilise la méthode sécurisée)
        self.update_bin_labels()

        # Graphique vitesse dashboard
        if self.speed_values and hasattr(self, 'line_speed'):
            try:
                if hasattr(self, 'canvas_speed') and self.canvas_speed.get_tk_widget().winfo_exists():
                    times = list(range(len(self.speed_values)))
                    self.line_speed.set_data(times, self.speed_values)
                    self.ax_speed.set_xlim(0, max(len(self.speed_values), 10))
                    y_min, y_max = min(self.speed_values), max(self.speed_values)
                    margin = (y_max - y_min) * 0.1 if y_max != y_min else 50
                    self.ax_speed.set_ylim(y_min - margin, y_max + margin)
                    self.canvas_speed.draw()
            except:
                pass
        
        # Mise à jour des graphes analytics
        try:
            self.update_analytics_graphs()
        except:
            pass
                
    def start_serial_polling(self):
        def poll():
            if USE_SERIAL and ser:
                try:
                    while ser.in_waiting:
                        line = ser.readline().decode(errors="ignore").strip()
                        if not line:
                            continue
                        self.add_log(line)
                        
                        if line.startswith("BIN:"):
                            try:
                                bin_id = int(line.split(":")[1])
                                if bin_id in self.counts:
                                    self.counts[bin_id] += 1
                            except:
                                pass
                        
                        elif line.startswith("SPD:"):
                            try:
                                speed = int(line.split(":")[1])
                                self.speed_values.append(speed)
                                if len(self.speed_values) > self.MAX_SPEED_POINTS:
                                    self.speed_values = self.speed_values[-self.MAX_SPEED_POINTS:]
                            except:
                                pass
                        
                        # ✅ NOUVEAU : Capturer la vitesse en m/s
                        elif line.startswith("SPD_MS:"):
                            try:
                                speed_ms = float(line.split(":")[1])
                                self.conveyor_speed_ms_values.append(speed_ms)
                                if len(self.conveyor_speed_ms_values) > self.MAX_SPEED_POINTS:
                                    self.conveyor_speed_ms_values = self.conveyor_speed_ms_values[-self.MAX_SPEED_POINTS:]
                            except:
                                pass
                        
                        elif line.startswith("MOTOR:"):
                            try:
                                parts = line.split(":")
                                motor_name = parts[1]
                                motor_state = float(parts[2])
                                if motor_name in self.arduino_state:
                                    self.arduino_state[motor_name] = motor_state
                            except:
                                pass
                        
                        elif line.startswith("TORQUE:"):
                            try:
                                torque = float(line.split(":")[1])
                                self.torque_values.append(torque)
                                if len(self.torque_values) > self.MAX_SPEED_POINTS:
                                    self.torque_values = self.torque_values[-self.MAX_SPEED_POINTS:]
                            except:
                                pass
                        
                        elif line.startswith("LUCAS_SPD:"):
                            try:
                                lucas_speed = float(line.split(":")[1])
                                self.motor2_speed_values.append(lucas_speed)
                                if len(self.motor2_speed_values) > self.MAX_SPEED_POINTS:
                                    self.motor2_speed_values = self.motor2_speed_values[-self.MAX_SPEED_POINTS:]
                            except:
                                pass
                        
                        elif line.startswith("M2_SPD:"):
                            try:
                                m2_speed = float(line.split(":")[1])
                                self.motor2_speed_values.append(m2_speed)
                                if len(self.motor2_speed_values) > self.MAX_SPEED_POINTS:
                                    self.motor2_speed_values = self.motor2_speed_values[-self.MAX_SPEED_POINTS:]
                            except:
                                pass
                    
                    # ✅ Calculer l'énergie UNIQUEMENT si connecté
                    self.calculate_energy()
                    self.update_dashboard_data()
                    
                except Exception as e:
                    self.add_log(f"Erreur série: {e}")
            
            self.root.after(100, poll)
        
        poll()

        
    def run(self):
        """Lance l'application"""
        def on_closing():
            if ser and ser.is_open:
                ser.close()
            self.root.destroy()
            
        self.root.protocol("WM_DELETE_WINDOW", on_closing)
        self.root.mainloop()

if __name__ == "__main__":
    print("🚀 Lancement de ScrewSorter Pro...")
    app = ModernScrewSorterApp()
    app.run()
