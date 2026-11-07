"""ArtifacialOS: a tiny desktop operating-system simulator made with Tkinter."""

from __future__ import annotations

import ast
from collections.abc import Callable
from html.parser import HTMLParser
import http.client
import json
import operator
import platform
import queue
import re
import ssl
import threading
import tkinter as tk
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from tkinter import messagebox
from urllib.error import URLError
from urllib.parse import quote, urljoin, urlsplit
from urllib.request import Request, urlopen
from uuid import uuid4
import webbrowser


BG = "#10131c"
PANEL = "#191e2b"
PANEL_LIGHT = "#2d498e"
ACCENT = "#8b7bff"
TEXT = "#f4f3ff"
MUTED = "#c5cbda"
GREEN = "#6ee7b7"
STARTPAGE_URL = "https://www.startpage.com/"


@dataclass
class BrowserTab:
    frame: tk.Frame
    address: tk.Entry
    page: tk.Text
    page_title: tk.Label
    status: tk.Label
    tab_button: tk.Label
    external_button: tk.Label
    back_button: tk.Label
    forward_button: tk.Label
    history: list[str] = field(default_factory=list)
    history_index: int = -1
    request_id: int = 0


def _create_browser_ssl_context() -> ssl.SSLContext:
    context = ssl.create_default_context()
    verify_paths = ssl.get_default_verify_paths()
    if (
        platform.system() == "Darwin"
        and not verify_paths.cafile
        and not verify_paths.capath
    ):
        system_ca_bundle = Path("/etc/ssl/cert.pem")
        if system_ca_bundle.is_file():
            context.load_verify_locations(cafile=str(system_ca_bundle))
    return context


def _normalize_browser_address(value: str) -> str:
    value = value.strip()
    if not value:
        raise ValueError("Type a website address or a search phrase.")
    is_local_host = value == "localhost" or value.startswith(
        ("localhost:", "127.0.0.1", "[::1]")
    )
    if "://" not in value and (
        any(character.isspace() for character in value)
        or ("." not in value and not is_local_host)
    ):
        return STARTPAGE_URL + "sp/search?query=" + quote(value, safe="")
    if "://" not in value:
        value = "https://" + value
    parsed = urlsplit(value)
    if parsed.scheme not in ("http", "https") or not parsed.hostname:
        raise ValueError("Only valid HTTP and HTTPS web addresses are supported.")
    return value


def _open_in_system_browser(url: str) -> bool:
    return webbrowser.open_new_tab(url)


class PageTextParser(HTMLParser):
    """Extract safe-to-display text and links without executing page content."""

    BLOCK_TAGS = {
        "address", "article", "blockquote", "br", "dd", "div", "dl", "dt",
        "fieldset", "figcaption", "figure", "footer", "form", "h1", "h2",
        "h3", "h4", "h5", "h6", "header", "hr", "li", "main", "nav",
        "ol", "p", "pre", "section", "table", "td", "th", "tr", "ul",
    }

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.title_parts: list[str] = []
        self.parts: list[tuple[str, str | None]] = []
        self.hidden_depth = 0
        self.in_title = False
        self.in_head = False

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attributes = dict(attrs)
        if tag in {"script", "style", "noscript", "svg"}:
            self.hidden_depth += 1
            return
        if self.hidden_depth:
            return
        if tag == "title":
            self.in_title = True
        if tag == "head":
            self.in_head = True
        if self.in_head and tag != "title":
            return
        if tag in self.BLOCK_TAGS:
            self._append("\n\n")
        if tag == "a" and attributes.get("href"):
            href = attributes["href"]
            if href is not None:
                self.parts.append(("", href))

    def handle_endtag(self, tag: str) -> None:
        if tag in {"script", "style", "noscript", "svg"}:
            self.hidden_depth = max(0, self.hidden_depth - 1)
            return
        if self.hidden_depth:
            return
        if tag == "title":
            self.in_title = False
        if tag == "head":
            self.in_head = False
        if self.in_head and tag != "title":
            return
        if tag in self.BLOCK_TAGS:
            self._append("\n\n")
        if tag == "a":
            self.parts.append(("", None))

    def handle_data(self, data: str) -> None:
        if self.in_title:
            self.title_parts.append(data)
            return
        if self.hidden_depth or (self.in_head and not self.in_title):
            return
        self._append(re.sub(r"\s+", " ", data))

    def _append(self, text: str) -> None:
        if self.parts:
            content, href = self.parts[-1]
            self.parts[-1] = (content + text, href)
        else:
            self.parts.append((text, None))

    def result(self) -> tuple[str, str, list[tuple[str, str]]]:
        title = " ".join(" ".join(self.title_parts).split())
        text = "".join(content for content, _href in self.parts)
        text = re.sub(r"[ \t]+", " ", text)
        text = "\n".join(line.strip() for line in text.splitlines())
        text = "\n".join(line for line in text.splitlines() if line)
        links: list[tuple[str, str]] = []
        active_href: str | None = None
        active_text = ""
        for content, href in self.parts:
            if href is not None:
                if active_href != href and active_text:
                    links.append((active_text, active_href or ""))
                    active_text = ""
                active_href = href
                active_text += content
            elif active_href is not None:
                links.append((active_text, active_href))
                active_href = None
                active_text = ""
        if active_href is not None:
            links.append((active_text, active_href))
        return title, text, links


class ArtifacialOS:
    """A self-contained desktop shell with a handful of useful simulated apps."""

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("ArtifacialOS")
        self.root.geometry("1100x720")
        self.root.minsize(760, 520)
        self.root.configure(bg=BG)
        self.root.option_add("*Font", ("Arial", 12))
        self.open_windows: dict[str, tk.Toplevel] = {}
        self.window_close_handlers: dict[str, Callable[[], None]] = {}
        self.notes_path = Path.home() / ".artifacialos" / "notes.json"
        self.filesystem: dict[str, str] = {
            "Welcome.txt": "Welcome to ArtifacialOS!\n\nA little desktop made entirely with Python's standard library.",
            "Ideas.txt": "Things to build:\n- A tiny game\n- A personal website\n- Something wonderful",
        }
        self.launcher: tk.Toplevel | None = None
        self._build_desktop()
        self._tick_clock()

    def _build_desktop(self) -> None:
        self.desktop = tk.Frame(self.root, bg=BG)
        self.desktop.pack(fill="both", expand=True)

        wallpaper = tk.Canvas(self.desktop, bg=BG, highlightthickness=0)
        wallpaper.place(relwidth=1, relheight=1)
        wallpaper.create_oval(620, -280, 1250, 360, fill="#211e47", outline="")
        wallpaper.create_oval(-280, 390, 320, 990, fill="#172c3c", outline="")
        wallpaper.create_text(
            38, 34, anchor="nw", text="ARTIFACIAL", fill="#ffffff",
            font=("Arial", 12, "bold"),
        )

        self._build_dock()

    def _build_dock(self) -> None:
        dock = tk.Frame(self.desktop, bg="#171b27", height=62)
        dock.pack(side="bottom", fill="x")
        dock.pack_propagate(False)
        left = tk.Frame(dock, bg="#171b27")
        left.pack(side="left", padx=12, fill="y")
        self._styled_button(
            left, "◈", self.toggle_launcher, bg=ACCENT, fg="white",
            hover_bg="#7868e7", font=("Arial", 17, "bold"), width=3,
        ).pack(side="left", padx=(0, 8), pady=9)
        for label, icon, callback in (
            ("Browser", "◎", self.open_browser),
            ("Files", "▣", self.open_files),
            ("Notes", "▤", self.open_notes),
            ("Calculator", "＋", self.open_calculator),
            ("Terminal", ">_", self.open_terminal),
        ):
            button = self._styled_button(
                left, f"{icon}  {label}", callback, bg="#222838", fg=TEXT,
                hover_bg="#303950", padx=12,
            )
            button.pack(side="left", padx=3, pady=12)

        right = tk.Frame(dock, bg="#171b27")
        right.pack(side="right", padx=18, fill="y")
        self.clock_label = tk.Label(
            right, bg="#171b27", fg=TEXT, font=("Arial", 12),
            justify="right",
        )
        self.clock_label.pack(side="right", pady=10)
        self._styled_button(
            right, "⚙", self.open_settings, bg="#171b27", fg=MUTED,
            hover_bg="#303950", hover_fg=TEXT, font=("Arial", 15),
        ).pack(side="right", padx=10, pady=8)

    def _tick_clock(self) -> None:
        if self.root.winfo_exists():
            self.clock_label.configure(text=datetime.now().strftime("%a, %b %d\n%I:%M %p"))
            self.root.after(1000, self._tick_clock)

    def _window(self, key: str, title: str, size: str = "680x460") -> tk.Frame | None:
        existing = self.open_windows.get(key)
        if existing is not None and existing.winfo_exists():
            existing.deiconify()
            existing.lift()
            return None

        window = tk.Toplevel(self.root)
        window.title(title)
        window.geometry(size)
        window.minsize(420, 300)
        window.configure(bg=BG)
        window.transient(self.root)
        self.open_windows[key] = window

        def close_window() -> None:
            handler = self.window_close_handlers.get(key)
            if handler is not None:
                handler()
            else:
                window.destroy()

        window.protocol("WM_DELETE_WINDOW", close_window)
        window.bind("<Destroy>", lambda event, k=key: self._forget_window(k, event))

        header = tk.Frame(window, bg=PANEL, height=42)
        header.pack(fill="x")
        header.pack_propagate(False)
        tk.Label(
            header, text=f"  {title}", bg=PANEL, fg=TEXT,
            font=("Arial", 12, "bold"),
        ).pack(side="left", padx=8)
        self._styled_button(
            header, "×", close_window, bg=PANEL, fg=MUTED,
            hover_bg="#4a3042", hover_fg="white",
            font=("Arial", 16), width=3, pady=0,
        ).pack(side="right", fill="y")

        drag = {"x": 0, "y": 0}

        def start_drag(event: tk.Event) -> None:
            drag["x"], drag["y"] = event.x_root - window.winfo_x(), event.y_root - window.winfo_y()

        def move_drag(event: tk.Event) -> None:
            window.geometry(f"+{event.x_root - drag['x']}+{event.y_root - drag['y']}")

        header.bind("<ButtonPress-1>", start_drag)
        header.bind("<B1-Motion>", move_drag)
        body = tk.Frame(window, bg=BG)
        body.pack(fill="both", expand=True)
        return body

    def _forget_window(self, key: str, event: tk.Event) -> None:
        if event.widget is self.open_windows.get(key):
            self.open_windows.pop(key, None)
            self.window_close_handlers.pop(key, None)

    @staticmethod
    def _label(parent: tk.Misc, text: str, **kwargs: object) -> tk.Label:
        kwargs.setdefault("bg", BG)
        kwargs.setdefault("fg", TEXT)
        return tk.Label(parent, text=text, **kwargs)

    @staticmethod
    def _styled_button(
        parent: tk.Misc,
        text: str,
        command: Callable[[], None],
        *,
        bg: str,
        fg: str,
        hover_bg: str,
        hover_fg: str | None = None,
        font: tuple[str, int] | tuple[str, int, str] | None = None,
        width: int | None = None,
        anchor: str = "center",
        padx: int = 12,
        pady: int = 8,
    ) -> tk.Label:
        button = tk.Label(
            parent,
            text=text,
            bg=bg,
            fg=fg,
            font=font,
            width=width,
            anchor=anchor,
            padx=padx,
            pady=pady,
            cursor="hand2",
            takefocus=True,
        )
        button.bind("<Enter>", lambda _event: button.configure(
            bg=hover_bg, fg=hover_fg or fg
        ))
        button.bind("<Leave>", lambda _event: button.configure(bg=bg, fg=fg))
        button.bind("<Button-1>", lambda _event: command())
        button.bind("<Return>", lambda _event: command())
        button.bind("<space>", lambda _event: command())
        return button

    def _button(
        self, parent: tk.Misc, text: str, command: Callable[[], None]
    ) -> tk.Label:
        return self._styled_button(
            parent, text, command, bg=PANEL_LIGHT, fg=TEXT,
            hover_bg="#343d54",
        )

    def open_welcome(self) -> None:
        body = self._window("welcome", "Welcome to ArtifacialOS", "560x400")
        if body is None:
            return
        self._label(body, "Welcome home.", font=("Arial", 24, "bold")).pack(
            anchor="w", padx=28, pady=(28, 8)
        )
        self._label(
            body,
            "This is a desktop simulator built using only Python's standard library.\n"
            "It can't replace the operating system installed on your computer, but\n"
            "you can open apps, save notes, browse sample files, and try the shell.",
            fg=MUTED, justify="left",
        ).pack(anchor="w", padx=28, pady=(0, 22))
        for text, action in (
            ("Open Files", self.open_files),
            ("Write a note", self.open_notes),
            ("Try the Terminal", self.open_terminal),
        ):
            self._button(body, text, action).pack(anchor="w", padx=28, pady=5)

    def open_files(self) -> None:
        body = self._window("files", "Files", "700x460")
        if body is None:
            return
        sidebar = tk.Frame(body, bg=PANEL, width=155)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)
        for name in ("Home", "Documents", "Desktop", "About this computer"):
            self._button(sidebar, name, lambda item=name: self._show_file_location(item, listing)).pack(
                fill="x", padx=8, pady=(10, 0)
            )

        content = tk.Frame(body, bg=BG)
        content.pack(side="left", fill="both", expand=True, padx=18, pady=18)
        heading = self._label(content, "Home", font=("Arial", 18, "bold"))
        heading.pack(anchor="w", pady=(0, 12))
        listing = tk.Listbox(
            content, bg=PANEL, fg=TEXT, selectbackground=ACCENT,
            selectforeground="#ffffff", relief="flat", borderwidth=0,
            font=("Arial", 13),
            activestyle="none",
        )
        listing.pack(fill="both", expand=True)
        listing.bind("<Double-Button-1>", lambda _event: self._open_selected_file(listing))
        self._show_file_location("Home", listing, heading)
        self._button(content, "Open selected file", lambda: self._open_selected_file(listing)).pack(
            anchor="e", pady=(12, 0)
        )

    def open_browser(self) -> None:
        body = self._window("browser", "Browser", "900x620")
        if body is None:
            return

        results: queue.Queue[tuple[BrowserTab, int, str, object]] = queue.Queue()
        ssl_context = _create_browser_ssl_context()
        tabs: list[BrowserTab] = []
        active_tab: BrowserTab | None = None

        tab_bar = tk.Frame(body, bg=PANEL)
        tab_bar.pack(fill="x", padx=12, pady=(12, 0))
        add_tab_button = self._button(tab_bar, "+", lambda: create_tab())
        add_tab_button.pack(side="right", padx=4, pady=4)
        content = tk.Frame(body, bg=BG)
        content.pack(fill="both", expand=True, padx=12, pady=8)

        def update_history_buttons(tab: BrowserTab) -> None:
            tab.back_button.configure(fg=TEXT if tab.history_index > 0 else MUTED)
            tab.forward_button.configure(
                fg=TEXT if tab.history_index + 1 < len(tab.history) else MUTED
            )

        def open_in_system_browser(tab: BrowserTab, url: str) -> None:
            try:
                opened = _open_in_system_browser(url)
            except OSError as error:
                tab.status.configure(
                    text=f"Could not open system browser: {error}", fg="#ff8585"
                )
                return
            tab.status.configure(
                text=(
                    "Opened in your default browser"
                    if opened else "Could not open system browser"
                ),
                fg=GREEN if opened else "#ff8585",
            )

        def select_tab(tab: BrowserTab) -> None:
            nonlocal active_tab
            if active_tab is tab:
                return
            if active_tab is not None and active_tab in tabs:
                active_tab.frame.pack_forget()
                active_tab.tab_button.configure(bg=PANEL, fg=MUTED)
            active_tab = tab
            tab.frame.pack(fill="both", expand=True)
            tab.tab_button.configure(bg=PANEL_LIGHT, fg=TEXT)
            update_history_buttons(tab)

        def fetch_page(
            tab: BrowserTab, url: str, current_request: int, mode: str
        ) -> None:
            try:
                request = Request(
                    url,
                    headers={
                        "User-Agent": (
                            "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                            "AppleWebKit/537.36 (KHTML, like Gecko) "
                            "Chrome/131.0.0.0 Safari/537.36"
                        ),
                        "Accept": "text/html,application/xhtml+xml",
                    },
                )
                with urlopen(request, timeout=12, context=ssl_context) as response:
                    content_type = response.headers.get_content_type()
                    charset = response.headers.get_content_charset() or "utf-8"
                    content = response.read(2_000_001)
                    if len(content) > 2_000_000:
                        raise ValueError("This page is too large to display (over 2 MB).")
                    document = content.decode(charset, errors="replace")
                    final_url = response.geturl()
                if content_type in ("text/html", "application/xhtml+xml"):
                    parser = PageTextParser()
                    parser.feed(document)
                    title, text, links = parser.result()
                    if not text:
                        text = "This page contains no readable text."
                elif content_type.startswith("text/") or content_type == "application/json":
                    title = final_url
                    text = document
                    links = []
                else:
                    raise ValueError(f"This browser cannot display {content_type} files.")
                results.put(
                    (tab, current_request, "page", (mode, final_url, title, text, links))
                )
            except (
                OSError, URLError, TimeoutError, UnicodeError, ValueError,
                LookupError, http.client.HTTPException,
            ) as error:
                results.put((tab, current_request, "error", str(error)))

        def navigate(tab: BrowserTab, value: str, mode: str = "new") -> None:
            try:
                url = _normalize_browser_address(value)
            except ValueError as error:
                tab.status.configure(text=str(error), fg="#ff8585")
                return
            tab.request_id += 1
            current_request = tab.request_id
            tab.address.delete(0, "end")
            tab.address.insert(0, url)
            tab.status.configure(text="Loading…", fg=MUTED)
            tab.external_button.pack_forget()
            threading.Thread(
                target=fetch_page,
                args=(tab, url, current_request, mode),
                daemon=True,
            ).start()

        def render_page(
            tab: BrowserTab, url: str, title: str, text: str,
            links: list[tuple[str, str]],
        ) -> None:
            tab.page.configure(state="normal")
            tab.page.delete("1.0", "end")
            tab.page.insert("end", title or url, "page_title")
            tab.page.insert("end", "\n\n")
            tab.page.insert("end", text)
            search_from = "3.0"
            for index, (label, href) in enumerate(links):
                if not label.strip():
                    continue
                start = tab.page.search(label, search_from, stopindex="end")
                if not start:
                    continue
                end = f"{start}+{len(label)}c"
                tag = f"link_{index}"
                tab.page.tag_add(tag, start, end)
                tab.page.tag_configure(tag, foreground="#3459bd", underline=True)
                tab.page.tag_bind(
                    tag, "<Button-1>",
                    lambda _event, target=urljoin(url, href), current_tab=tab:
                        navigate(current_tab, target),
                )
                tab.page.tag_bind(
                    tag, "<Enter>",
                    lambda _event, current_page=tab.page:
                        current_page.configure(cursor="hand2"),
                )
                tab.page.tag_bind(
                    tag, "<Leave>",
                    lambda _event, current_page=tab.page:
                        current_page.configure(cursor="arrow"),
                )
                search_from = end
            tab.page.yview_moveto(0)
            tab.page_title.configure(text=title or url, fg=TEXT)
            tab.tab_button.configure(text=(title or "New Tab")[:24])
            if (
                urlsplit(url).hostname in ("www.startpage.com", "startpage.com")
                and (
                    title.lower().startswith("access denied")
                    or "could not load its javascript" in text.lower()
                    or "verifying your request" in text.lower()
                )
            ):
                tab.page.insert(
                    "end",
                    "\n\nStartpage blocked this text-only browser. "
                    "Open the page in your system browser to continue.",
                )
                tab.external_button.pack(side="right", padx=8)

        def poll_results() -> None:
            if not body.winfo_exists():
                return
            while True:
                try:
                    tab, result_id, result_type, data = results.get_nowait()
                except queue.Empty:
                    break
                if tab not in tabs or result_id != tab.request_id:
                    continue
                if result_type == "error":
                    tab.status.configure(text=f"Could not load page: {data}", fg="#ff8585")
                    if urlsplit(tab.address.get()).hostname == "www.startpage.com":
                        tab.external_button.pack(side="right", padx=8)
                    continue
                mode, url, title, text, links = data
                if mode == "new":
                    del tab.history[tab.history_index + 1:]
                    tab.history.append(url)
                    tab.history_index = len(tab.history) - 1
                elif mode == "back":
                    tab.history_index = max(0, tab.history_index - 1)
                elif mode == "forward":
                    tab.history_index = min(len(tab.history) - 1, tab.history_index + 1)
                tab.address.delete(0, "end")
                tab.address.insert(0, url)
                render_page(tab, url, title, text, links)
                tab.status.configure(text=url, fg=MUTED)
                update_history_buttons(tab)
            body.after(100, poll_results)

        def create_tab(url: str = STARTPAGE_URL) -> None:
            tab_frame = tk.Frame(content, bg=BG)
            tab_header = tk.Frame(tab_bar, bg=PANEL)
            tab_header.pack(side="left", padx=3, pady=4)
            tab_button = self._styled_button(
                tab_header, "New Tab", lambda: None, bg=PANEL, fg=MUTED,
                hover_bg=PANEL_LIGHT, padx=10, pady=6,
            )
            tab_button.pack(side="left")
            close_button = self._styled_button(
                tab_header, "×", lambda: None, bg=PANEL, fg=MUTED,
                hover_bg="#4a3042", width=2, padx=4, pady=6,
            )
            close_button.pack(side="left")

            toolbar = tk.Frame(tab_frame, bg=PANEL)
            toolbar.pack(fill="x", pady=(0, 8))
            navigation = tk.Frame(toolbar, bg=PANEL)
            navigation.pack(fill="x", padx=8, pady=8)
            back_button = self._styled_button(
                navigation, "←", lambda: None, bg=PANEL, fg=MUTED,
                hover_bg=PANEL_LIGHT, font=("Arial", 16, "bold"), width=3,
            )
            back_button.pack(side="left", padx=(4, 0))
            forward_button = self._styled_button(
                navigation, "→", lambda: None, bg=PANEL, fg=MUTED,
                hover_bg=PANEL_LIGHT, font=("Arial", 16, "bold"), width=3,
            )
            forward_button.pack(side="left")
            refresh_button = self._styled_button(
                navigation, "↻", lambda: None, bg=PANEL, fg=TEXT,
                hover_bg=PANEL_LIGHT, font=("Arial", 16), width=3,
            )
            refresh_button.pack(side="left")
            go_button = self._button(navigation, "Go", lambda: None)
            go_button.pack(side="right", padx=(4, 8))
            address = tk.Entry(
                navigation, bg="#10131c", fg=TEXT, insertbackground=TEXT,
                relief="flat", font=("Arial", 12),
            )
            address.pack(side="left", fill="x", expand=True, padx=8, ipady=9)

            controls = tk.Frame(toolbar, bg=PANEL)
            controls.pack(fill="x", padx=8, pady=(0, 8))
            page_title = self._label(controls, "Startpage", fg=MUTED)
            page_title.pack(side="left", padx=8)
            status = self._label(controls, "Loading Startpage…", fg=MUTED)
            status.pack(side="right", padx=8)
            external_button = self._button(
                controls, "Open in system browser",
                lambda: open_in_system_browser(tab, address.get()),
            )

            reader_frame = tk.Frame(tab_frame, bg=BG)
            reader_frame.pack(fill="both", expand=True)
            scrollbar = tk.Scrollbar(reader_frame)
            scrollbar.pack(side="right", fill="y")
            page = tk.Text(
                reader_frame, bg="#faf9f6", fg="#20212a",
                insertbackground="#20212a", relief="flat", wrap="word",
                padx=30, pady=24, font=("Arial", 14),
                yscrollcommand=scrollbar.set, cursor="arrow",
            )
            page.pack(side="left", fill="both", expand=True)
            scrollbar.configure(command=page.yview)
            page.tag_configure("page_title", font=("Arial", 24, "bold"), spacing3=18)
            page.insert("1.0", "Loading Startpage…", "page_title")
            page.bind("<Key>", lambda _event: "break")

            tab = BrowserTab(
                frame=tab_frame,
                address=address,
                page=page,
                page_title=page_title,
                status=status,
                tab_button=tab_button,
                external_button=external_button,
                back_button=back_button,
                forward_button=forward_button,
            )
            tabs.append(tab)
            tab_button.bind("<Button-1>", lambda _event: select_tab(tab))
            close_button.bind("<Button-1>", lambda _event: close_tab(tab))
            back_button.bind(
                "<Button-1>",
                lambda _event: navigate(tab, tab.history[tab.history_index - 1], "back")
                if tab.history_index > 0 else None,
            )
            forward_button.bind(
                "<Button-1>",
                lambda _event: navigate(tab, tab.history[tab.history_index + 1], "forward")
                if tab.history_index + 1 < len(tab.history) else None,
            )
            refresh_button.bind(
                "<Button-1>",
                lambda _event: navigate(tab, tab.history[tab.history_index], "refresh")
                if tab.history_index >= 0 else navigate(tab, tab.address.get()),
            )
            go_button.bind("<Button-1>", lambda _event: navigate(tab, address.get()))
            address.bind("<Return>", lambda _event: navigate(tab, address.get()))
            select_tab(tab)
            navigate(tab, url)

        def close_tab(tab: BrowserTab) -> None:
            if tab not in tabs:
                return
            index = tabs.index(tab)
            tab.request_id += 1
            tabs.remove(tab)
            tab.frame.destroy()
            tab.tab_button.master.destroy()
            if active_tab is tab:
                if tabs:
                    select_tab(tabs[min(index, len(tabs) - 1)])
                else:
                    create_tab()

        create_tab()
        poll_results()

    def _show_file_location(
        self, location: str, listing: tk.Listbox, heading: tk.Label | None = None
    ) -> None:
        if heading is not None:
            heading.configure(text=location)
        listing.delete(0, "end")
        if location == "About this computer":
            listing.insert("end", f"ArtifacialOS 1.0  ·  Python {platform.python_version()}")
            listing.insert("end", f"Host: {platform.system()} {platform.release()}")
            return
        files = self.filesystem if location in ("Home", "Documents") else {
            "Readme.txt": "Your desktop is looking good."
        }
        for name in files:
            listing.insert("end", f"▤   {name}")

    def _open_selected_file(self, listing: tk.Listbox) -> None:
        selected = listing.curselection()
        if not selected:
            return
        entry = listing.get(selected[0])
        filename = entry.split("   ", 1)[-1]
        content = self.filesystem.get(filename)
        if content is None:
            return
        body = self._window(f"file:{filename}", filename, "560x400")
        if body is None:
            return
        text = tk.Text(
            body, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="flat",
            wrap="word", padx=14, pady=14,
        )
        text.pack(fill="both", expand=True, padx=16, pady=16)
        text.insert("1.0", content)
        text.configure(state="disabled")

    def open_notes(self) -> None:
        body = self._window("notes", "Notes", "820x560")
        if body is None:
            return

        notes: list[dict[str, str]] = []
        current_id: str | None = None
        save_job: str | None = None
        loading = False

        try:
            if self.notes_path.exists():
                stored = self.notes_path.read_text(encoding="utf-8")
                if stored.strip().startswith("{"):
                    data = json.loads(stored)
                    if not isinstance(data, dict) or not isinstance(data.get("notes"), list):
                        raise ValueError("The notes file has an invalid format.")
                    for item in data["notes"]:
                        if (
                            isinstance(item, dict)
                            and isinstance(item.get("id"), str)
                            and isinstance(item.get("title"), str)
                            and isinstance(item.get("body"), str)
                        ):
                            notes.append({
                                "id": item["id"],
                                "title": item["title"],
                                "body": item["body"],
                                "updated": str(item.get("updated", "")),
                            })
                elif stored:
                    notes.append({
                        "id": uuid4().hex,
                        "title": "My first note",
                        "body": stored,
                        "updated": datetime.now().isoformat(timespec="seconds"),
                    })
        except (OSError, json.JSONDecodeError, ValueError) as error:
            messagebox.showerror("Could not load notes", str(error), parent=self.root)

        toolbar = tk.Frame(body, bg=BG)
        toolbar.pack(fill="x", padx=16, pady=(14, 10))
        self._label(toolbar, "My notes", font=("Arial", 21, "bold")).pack(side="left")
        self._button(toolbar, "＋  New note", lambda: create_note()).pack(side="right")

        footer = tk.Frame(body, bg=BG)
        footer.pack(fill="x", padx=16, pady=(0, 12))
        status = self._label(footer, "", fg=MUTED)
        status.pack(side="left")
        delete_button = self._button(footer, "Delete note", lambda: delete_note())
        delete_button.pack(side="right", padx=(8, 0))
        self._button(footer, "Save now", lambda: save_note()).pack(side="right")

        workspace = tk.Frame(body, bg=BG)
        workspace.pack(fill="both", expand=True, padx=16, pady=(0, 10))
        sidebar = tk.Frame(workspace, bg=PANEL, width=235)
        sidebar.pack(side="left", fill="y", padx=(0, 14))
        sidebar.pack_propagate(False)

        search = tk.Entry(
            sidebar, bg="#111520", fg=TEXT, insertbackground=TEXT,
            relief="flat", font=("Arial", 12),
        )
        search.pack(fill="x", padx=10, pady=10, ipady=8)
        search.insert(0, "Search notes...")

        note_list = tk.Listbox(
            sidebar, bg=PANEL, fg=TEXT, selectbackground=ACCENT,
            selectforeground="#ffffff", relief="flat", borderwidth=0,
            font=("Arial", 12), activestyle="none", exportselection=False,
        )
        note_list.pack(fill="both", expand=True, padx=6, pady=(0, 8))

        editor_area = tk.Frame(workspace, bg=BG)
        editor_area.pack(side="left", fill="both", expand=True)
        title = tk.Entry(
            editor_area, bg=BG, fg=TEXT, insertbackground=TEXT,
            relief="flat", font=("Arial", 20, "bold"),
        )
        title.pack(fill="x", pady=(4, 12), ipady=5)
        editor = tk.Text(
            editor_area, bg=PANEL, fg=TEXT, insertbackground=TEXT,
            relief="flat", wrap="word", padx=16, pady=14, undo=True,
            font=("Arial", 13), spacing1=2, spacing3=4,
        )
        editor.pack(fill="both", expand=True)

        def refresh_list() -> None:
            note_list.delete(0, "end")
            query = search.get().strip().lower()
            if query == "search notes...":
                query = ""
            for note in sorted(notes, key=lambda item: item["updated"], reverse=True):
                if query and query not in note["title"].lower() and query not in note["body"].lower():
                    continue
                note_list.insert("end", note["title"] or "Untitled note")
                if note["id"] == current_id:
                    note_list.selection_set("end")
                    note_list.activate("end")

        def update_status(message: str = "All changes saved") -> None:
            words = len(editor.get("1.0", "end-1c").split()) if current_id else 0
            word_label = f"{words} word" if words == 1 else f"{words} words"
            status.configure(
                text=f"{message}  ·  {word_label}",
                fg=GREEN if message.startswith("Saved") else MUTED,
            )

        def load_note(note: dict[str, str] | None) -> None:
            nonlocal current_id, loading
            current_id = note["id"] if note else None
            loading = True
            title.delete(0, "end")
            editor.delete("1.0", "end")
            if note:
                title.insert(0, note["title"])
                editor.insert("1.0", note["body"])
                title.configure(state="normal")
                editor.configure(state="normal")
                editor.focus_set()
            else:
                title.configure(state="disabled")
                editor.configure(state="disabled")
            loading = False
            refresh_list()
            update_status("Ready" if note else "Create a note to get started")

        def persist_notes() -> bool:
            try:
                self.notes_path.parent.mkdir(parents=True, exist_ok=True)
                temporary_path = self.notes_path.with_suffix(".tmp")
                temporary_path.write_text(
                    json.dumps({"version": 1, "notes": notes}, ensure_ascii=False, indent=2),
                    encoding="utf-8",
                )
                temporary_path.replace(self.notes_path)
            except OSError as error:
                messagebox.showerror("Could not save notes", str(error), parent=body)
                update_status("Save failed")
                return False
            return True

        def save_note() -> bool:
            nonlocal save_job
            if save_job is not None:
                body.after_cancel(save_job)
                save_job = None
            note = next((item for item in notes if item["id"] == current_id), None)
            if note is None:
                return True
            note["title"] = title.get().strip() or "Untitled note"
            note["body"] = editor.get("1.0", "end-1c")
            note["updated"] = datetime.now().isoformat(timespec="seconds")
            if not persist_notes():
                return False
            refresh_list()
            update_status(f"Saved at {datetime.now().strftime('%I:%M %p')}")
            return True

        def schedule_save(_event: tk.Event | None = None) -> None:
            nonlocal save_job
            if loading or current_id is None:
                return
            if save_job is not None:
                body.after_cancel(save_job)
            update_status("Unsaved changes")
            save_job = body.after(700, save_note)

        def create_note() -> None:
            if not save_note():
                return
            note = {
                "id": uuid4().hex,
                "title": "Untitled note",
                "body": "",
                "updated": datetime.now().isoformat(timespec="seconds"),
            }
            notes.append(note)
            load_note(note)
            title.select_range(0, "end")
            schedule_save()

        def delete_note() -> None:
            if current_id is None:
                return
            note = next((item for item in notes if item["id"] == current_id), None)
            if note is None:
                return
            if not messagebox.askyesno(
                "Delete note",
                f"Delete “{note['title'] or 'Untitled note'}”?",
                parent=body,
            ):
                return
            if not save_note():
                return
            notes.remove(note)
            if not persist_notes():
                notes.append(note)
                load_note(note)
                return
            load_note(notes[0] if notes else None)

        def select_note(_event: tk.Event | None = None) -> None:
            selection = note_list.curselection()
            if not selection:
                return
            visible = [
                note for note in sorted(notes, key=lambda item: item["updated"], reverse=True)
                if not search.get().strip()
                or search.get().strip().lower() in note["title"].lower()
                or search.get().strip().lower() in note["body"].lower()
            ]
            if search.get().strip().lower() == "search notes...":
                visible = sorted(notes, key=lambda item: item["updated"], reverse=True)
            if selection[0] >= len(visible):
                return
            selected = visible[selection[0]]
            if selected["id"] == current_id:
                return
            if save_note():
                load_note(selected)

        def close_notes() -> None:
            if save_note():
                body.winfo_toplevel().destroy()

        def clear_search(_event: tk.Event) -> None:
            if search.get() == "Search notes...":
                search.delete(0, "end")

        search.bind("<FocusIn>", clear_search)
        search.bind("<KeyRelease>", lambda _event: refresh_list())
        search.bind("<Return>", select_note)
        note_list.bind("<<ListboxSelect>>", select_note)
        title.bind("<KeyRelease>", schedule_save)
        title.bind("<FocusOut>", schedule_save)
        editor.bind("<KeyRelease>", schedule_save)
        editor.bind("<Control-s>", lambda _event: (save_note(), "break")[1])
        editor.bind("<Command-s>", lambda _event: (save_note(), "break")[1])
        title.bind("<Control-s>", lambda _event: (save_note(), "break")[1])
        title.bind("<Command-s>", lambda _event: (save_note(), "break")[1])
        body.bind("<Control-n>", lambda _event: (create_note(), "break")[1])
        body.bind("<Command-n>", lambda _event: (create_note(), "break")[1])

        self.window_close_handlers["notes"] = close_notes
        refresh_list()
        load_note(notes[0] if notes else None)

    def open_calculator(self) -> None:
        body = self._window("calculator", "Calculator", "360x430")
        if body is None:
            return
        display = tk.Entry(
            body, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="flat",
            font=("Arial", 23), justify="right",
        )
        display.pack(fill="x", padx=18, pady=18, ipady=12)
        buttons = tk.Frame(body, bg=BG)
        buttons.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        keys = ("C", "(", ")", "÷", "7", "8", "9", "×", "4", "5", "6", "−",
                "1", "2", "3", "+", "⌫", "0", ".", "=")

        def press(value: str) -> None:
            if value == "C":
                display.delete(0, "end")
            elif value == "⌫":
                display.delete(max(0, len(display.get()) - 1), "end")
            elif value == "=":
                try:
                    result = self._calculate(display.get())
                    display.delete(0, "end")
                    display.insert(0, str(result))
                except (ValueError, ZeroDivisionError, OverflowError) as error:
                    messagebox.showerror("Calculation error", str(error), parent=body)
            else:
                display.insert("end", {"÷": "/", "×": "*", "−": "-"}.get(value, value))

        for index, key in enumerate(keys):
            button = self._button(buttons, key, lambda item=key: press(item))
            button.grid(row=index // 4, column=index % 4, sticky="nsew", padx=4, pady=4)
        for row in range(5):
            buttons.rowconfigure(row, weight=1)
        for column in range(4):
            buttons.columnconfigure(column, weight=1)
        display.bind("<Return>", lambda _event: press("="))

    @staticmethod
    def _calculate(expression: str) -> int | float:
        """Evaluate basic arithmetic without executing arbitrary Python code."""
        operations: dict[type[ast.operator], object] = {
            ast.Add: operator.add,
            ast.Sub: operator.sub,
            ast.Mult: operator.mul,
            ast.Div: operator.truediv,
            ast.FloorDiv: operator.floordiv,
            ast.Mod: operator.mod,
            ast.Pow: operator.pow,
        }

        def visit(node: ast.AST) -> int | float:
            if isinstance(node, ast.Expression):
                return visit(node.body)
            if isinstance(node, ast.Constant) and type(node.value) in (int, float):
                return node.value
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
                value = visit(node.operand)
                return value if isinstance(node.op, ast.UAdd) else -value
            if isinstance(node, ast.BinOp) and type(node.op) in operations:
                left, right = visit(node.left), visit(node.right)
                if isinstance(node.op, ast.Pow) and abs(right) > 1000:
                    raise ValueError("Exponent is too large.")
                return operations[type(node.op)](left, right)  # type: ignore[operator]
            raise ValueError("Use numbers and basic arithmetic operators only.")

        try:
            return visit(ast.parse(expression, mode="eval"))
        except SyntaxError as error:
            raise ValueError("That expression is not valid.") from error

    def open_terminal(self) -> None:
        body = self._window("terminal", "Terminal", "720x470")
        if body is None:
            return
        output = tk.Text(
            body, bg="#0b0e14", fg="#f0f2f8", insertbackground=TEXT,
            relief="flat", font=("Menlo", 13), wrap="word", padx=14, pady=14,
            state="disabled",
        )
        output.pack(fill="both", expand=True, padx=14, pady=(14, 8))
        command = tk.Entry(
            body, bg=PANEL, fg=TEXT, insertbackground=TEXT, relief="flat",
            font=("Menlo", 13),
        )
        command.pack(fill="x", padx=14, pady=(0, 14), ipady=9)
        command.insert(0, "help")

        def write(text: str) -> None:
            output.configure(state="normal")
            output.insert("end", text + "\n")
            output.see("end")
            output.configure(state="disabled")

        def run_command(_event: tk.Event | None = None) -> None:
            raw = command.get().strip()
            command.delete(0, "end")
            if not raw:
                return
            write(f"you@artifacial:~$ {raw}")
            parts = raw.split(maxsplit=1)
            name, argument = parts[0].lower(), parts[1] if len(parts) == 2 else ""
            if name in ("help", "?"):
                write("Commands: help, ls, pwd, date, whoami, cat <file>, echo <text>, clear")
            elif name == "ls":
                write("  ".join(self.filesystem))
            elif name == "pwd":
                write("/home/you")
            elif name == "date":
                write(datetime.now().astimezone().strftime("%A, %B %d %Y %H:%M:%S %Z"))
            elif name == "whoami":
                write("you")
            elif name == "cat":
                if not argument:
                    write("Usage: cat <file>")
                elif argument in self.filesystem:
                    write(self.filesystem[argument])
                else:
                    write(f"cat: {argument}: no such file")
            elif name == "echo":
                write(argument)
            elif name == "clear":
                output.configure(state="normal")
                output.delete("1.0", "end")
                output.configure(state="disabled")
            else:
                write(f"{name}: command not found (try 'help')")

        command.bind("<Return>", run_command)
        run_command()
        command.focus_set()

    def open_settings(self) -> None:
        body = self._window("settings", "Settings", "520x400")
        if body is None:
            return
        self._label(body, "System settings", font=("Arial", 20, "bold")).pack(
            anchor="w", padx=24, pady=(24, 16)
        )
        self._label(body, "About this desktop", font=("Arial", 12, "bold")).pack(
            anchor="w", padx=24, pady=(4, 6)
        )
        self._label(
            body,
            f"ArtifacialOS 1.0\nPython {platform.python_version()} · {platform.system()}\n"
            "A friendly desktop simulator. No extra packages required.",
            fg=MUTED, justify="left",
        ).pack(anchor="w", padx=24, pady=(0, 20))
        self._label(body, "Built-in apps", font=("Arial", 12, "bold")).pack(
            anchor="w", padx=24, pady=(4, 6)
        )
        self._label(
            body, "Browser  ·  Files  ·  Notes  ·  Calculator  ·  Terminal",
            fg=MUTED,
        ).pack(anchor="w", padx=24)

    def toggle_launcher(self) -> None:
        if self.launcher is not None and self.launcher.winfo_exists():
            self.launcher.destroy()
            self.launcher = None
            return
        launcher = tk.Toplevel(self.root)
        self.launcher = launcher
        launcher.overrideredirect(True)
        launcher.configure(bg=PANEL)
        launcher.geometry(f"270x380+14+{max(80, self.root.winfo_height() - 455)}")
        launcher.attributes("-topmost", True)
        tk.Label(
            launcher, text="Your apps", bg=PANEL, fg=TEXT,
            font=("Arial", 15, "bold"),
        ).pack(anchor="w", padx=18, pady=(16, 10))
        for label, callback in (
            ("◎   Browser", self.open_browser),
            ("▣   Files", self.open_files),
            ("▤   Notes", self.open_notes),
            ("＋   Calculator", self.open_calculator),
            (">_   Terminal", self.open_terminal),
            ("⚙   Settings", self.open_settings),
            ("?   Welcome", self.open_welcome),
        ):
            def launch(action: Callable[[], None] = callback) -> None:
                launcher.destroy()
                self.launcher = None
                action()

            self._styled_button(
                launcher, label, launch, anchor="w", bg=PANEL, fg=TEXT,
                hover_bg=PANEL_LIGHT, padx=18,
            ).pack(fill="x", padx=6)


def main() -> None:
    root = tk.Tk()
    ArtifacialOS(root)
    root.mainloop()


if __name__ == "__main__":
    main()
