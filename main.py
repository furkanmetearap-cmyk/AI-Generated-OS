"""ArtifacialOS: a tiny desktop simulator with an embedded web browser."""

from __future__ import annotations

import ast
from collections.abc import Callable
import json
import operator
import platform
import signal
import sys
from datetime import datetime
from pathlib import Path
from urllib.parse import quote, urlsplit
from uuid import uuid4

from PySide6.QtCore import QEvent, QPoint, QRect, QRectF, QSize, Qt, QTimer, QUrl
from PySide6.QtGui import (
    QCloseEvent,
    QDesktopServices,
    QKeySequence,
    QMouseEvent,
    QPainter,
    QPaintEvent,
    QPen,
    QResizeEvent,
    QShortcut,
)
from PySide6.QtWebEngineCore import (
    QWebEngineFullScreenRequest,
    QWebEnginePage,
    QWebEnginePermission,
    QWebEngineSettings,
)
from PySide6.QtWebEngineWidgets import QWebEngineView
from PySide6.QtWidgets import (
    QApplication,
    QGridLayout,
    QHBoxLayout,
    QLabel,
    QLineEdit,
    QListWidget,
    QMainWindow,
    QMdiArea,
    QMdiSubWindow,
    QMessageBox,
    QPushButton,
    QPlainTextEdit,
    QSplitter,
    QTabWidget,
    QTextEdit,
    QVBoxLayout,
    QWidget,
)


BG = "#10131c"
PANEL = "#191e2b"
PANEL_LIGHT = "#2d498e"
ACCENT = "#8b7bff"
TEXT = "#f4f3ff"
MUTED = "#c5cbda"
GREEN = "#6ee7b7"
STARTPAGE_URL = "https://www.startpage.com/"


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


def _stylesheet() -> str:
    return f"""
        QWidget {{ background: {BG}; color: {TEXT}; font: 12pt Arial; }}
        QMainWindow {{ background: {BG}; }}
        QLabel#desktopTitle {{ background: transparent; font-size: 13pt; font-weight: bold; }}
        QWidget#dock {{ background: #171b27; }}
        QPushButton {{
            background: #222838; color: {TEXT}; border: 0; border-radius: 8px;
            padding: 8px 12px;
        }}
        QPushButton:hover {{ background: #303950; }}
        QPushButton#launcherButton {{ background: {ACCENT}; font-size: 16pt; font-weight: bold; }}
        QLineEdit, QPlainTextEdit, QTextEdit, QListWidget {{
            background: {PANEL}; color: {TEXT}; border: 1px solid #303747;
            border-radius: 5px; padding: 7px; selection-background-color: {ACCENT};
        }}
        QTabWidget::pane {{ border: 1px solid #303747; }}
        QTabBar::tab {{ background: {PANEL}; padding: 7px 12px; }}
        QTabBar::tab:selected {{ background: #303950; }}
        QToolBar {{ background: {PANEL}; border: 0; spacing: 5px; padding: 4px; }}
        QToolButton {{ color: {TEXT}; padding: 6px; }}
        QStatusBar {{ background: {PANEL}; color: {MUTED}; }}
        QMdiArea {{ border: 0; }}
        QMdiSubWindow {{ background: {BG}; border: 0; border-radius: 0; }}
        QScrollArea {{ border: 0; }}
    """


class BrowserTab(QWebEngineView):
    def __init__(self, create_tab: Callable[[], QWebEngineView]) -> None:
        super().__init__()
        self.create_tab = create_tab
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)

    def createWindow(
        self, window_type: QWebEnginePage.WebWindowType
    ) -> QWebEngineView:
        return self.create_tab()

    def mousePressEvent(self, event: QMouseEvent) -> None:
        self.setFocus(Qt.FocusReason.MouseFocusReason)
        super().mousePressEvent(event)


class BrowserWidget(QWidget):
    """Tabbed Qt WebEngine browser hosted inside an ArtifacialOS app window."""

    def __init__(self) -> None:
        super().__init__()
        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(7)

        self.navigation = QWidget()
        navigation = QHBoxLayout(self.navigation)
        navigation.setContentsMargins(0, 0, 0, 0)
        for label, callback in (
            ("Back", lambda: self.current_view().back()),
            ("Forward", lambda: self.current_view().forward()),
            ("Reload", lambda: self.current_view().reload()),
        ):
            button = QPushButton(label)
            button.clicked.connect(callback)
            navigation.addWidget(button)

        self.address = QLineEdit()
        self.address.setPlaceholderText("Enter a website or search")
        self.address.returnPressed.connect(self.navigate)
        navigation.addWidget(self.address, 1)
        new_tab = QPushButton("New Tab")
        new_tab.clicked.connect(self.add_tab)
        navigation.addWidget(new_tab)
        fullscreen = QPushButton("Fullscreen")
        fullscreen.setToolTip("Click to toggle fullscreen. Press F11 to exit; Esc goes to the game.")
        fullscreen.clicked.connect(self.toggle_fullscreen)
        navigation.addWidget(fullscreen)
        open_external = QPushButton("Play in Browser")
        open_external.setToolTip("Open this page in your Mac's default web browser")
        open_external.clicked.connect(self.open_in_system_browser)
        navigation.addWidget(open_external)
        layout.addWidget(self.navigation)

        self.tabs = QTabWidget()
        self.tabs.setTabsClosable(True)
        self.tabs.setMovable(True)
        self.tabs.currentChanged.connect(self.update_address)
        self.tabs.tabCloseRequested.connect(self.close_tab)
        layout.addWidget(self.tabs, 1)

        self._fullscreen_view: QWebEngineView | None = None
        self._fullscreen_subwindow: QMdiSubWindow | None = None
        self._fullscreen_host: ArtifacialOS | None = None
        self._fullscreen_host_was_maximized = False
        self._fullscreen_host_was_fullscreen = False
        self._fullscreen_subwindow_was_maximized = False

        self.status = QLabel("Ready")
        self.status.setStyleSheet(f"color: {MUTED};")
        layout.addWidget(self.status)

        QShortcut(QKeySequence("Ctrl+L"), self, self.focus_address)
        QShortcut(QKeySequence("Ctrl+T"), self, self.add_tab)
        QShortcut(QKeySequence("Ctrl+W"), self, self.close_current_tab)
        QShortcut(QKeySequence("F11"), self, self.toggle_fullscreen)
        self.add_tab()

    def current_view(self) -> QWebEngineView:
        view = self.tabs.currentWidget()
        if not isinstance(view, QWebEngineView):
            raise RuntimeError("The active browser tab is unavailable.")
        return view

    def focus_address(self) -> None:
        self.address.setFocus()
        self.address.selectAll()

    def open_in_system_browser(self) -> None:
        url = self.current_view().url()
        if not url.isValid() or url.scheme() not in ("http", "https"):
            self.status.setText("Only HTTP and HTTPS pages can be opened externally.")
            return
        if not QDesktopServices.openUrl(url):
            self.status.setText("Could not open the page in your default browser.")

    def update_load_status(self, success: bool) -> None:
        self.status.setText("" if success else "Could not load page")

    def add_tab(self, *, load_start_page: bool = True) -> QWebEngineView:
        view = BrowserTab(lambda: self.add_tab(load_start_page=False))
        view.settings().setAttribute(
            QWebEngineSettings.WebAttribute.FullScreenSupportEnabled, True
        )
        view.settings().setAttribute(QWebEngineSettings.WebAttribute.WebGLEnabled, True)
        page = view.page()
        page.permissionRequested.connect(
            lambda permission, current_view=view: self.handle_permission_request(
                current_view, permission
            )
        )
        page.featurePermissionRequested.connect(
            lambda origin, feature, current_page=page: self.handle_feature_permission(
                current_page, origin, feature
            )
        )
        index = self.tabs.addTab(view, "New Tab")
        self.tabs.setCurrentIndex(index)
        page.fullScreenRequested.connect(
            lambda request, current_view=view: self.handle_fullscreen_request(
                current_view, request
            )
        )
        page.renderProcessTerminated.connect(
            lambda status, exit_code, current_view=view: self.handle_render_process_terminated(
                current_view, status, exit_code
            )
        )
        view.titleChanged.connect(
            lambda title, current_view=view: self.update_tab_title(current_view, title)
        )
        view.urlChanged.connect(
            lambda url, current_view=view: self.update_view_address(current_view, url)
        )
        view.loadStarted.connect(lambda: self.status.setText("Loading…"))
        view.loadFinished.connect(self.update_load_status)
        if load_start_page:
            view.setUrl(QUrl(STARTPAGE_URL))
        return view

    def handle_render_process_terminated(
        self,
        view: QWebEngineView,
        status: QWebEnginePage.RenderProcessTerminationStatus,
        exit_code: int,
    ) -> None:
        if (
            status
            == QWebEnginePage.RenderProcessTerminationStatus.CrashedTerminationStatus
            and not view.property("rendererRecoveryAttempted")
        ):
            view.setProperty("rendererRecoveryAttempted", True)
            self.status.setText("Page renderer crashed. Retrying once…")
            view.reload()
            return

        self.status.setText(
            f"Page renderer stopped ({status.name}, exit code {exit_code})."
        )
        if view is not self.tabs.currentWidget():
            return

        dialog = QMessageBox(self)
        dialog.setIcon(QMessageBox.Icon.Critical)
        dialog.setWindowTitle("Game stopped")
        dialog.setText(
            "The embedded browser stopped while running this page. "
            "Play in Browser opens it in your system browser, where graphics "
            "acceleration is available."
        )
        reload_button = dialog.addButton(
            "Reload Game", QMessageBox.ButtonRole.AcceptRole
        )
        browser_button = dialog.addButton(
            "Play in Browser", QMessageBox.ButtonRole.ActionRole
        )
        dialog.addButton(QMessageBox.StandardButton.Close)
        dialog.setDefaultButton(browser_button)
        dialog.exec()

        if dialog.clickedButton() is reload_button:
            view.reload()
        elif dialog.clickedButton() is browser_button:
            url = view.url()
            if url.isValid() and url.scheme() in ("http", "https"):
                if not QDesktopServices.openUrl(url):
                    self.status.setText("Could not open the page in your default browser.")
            else:
                self.status.setText(
                    "Only HTTP and HTTPS pages can be opened externally."
                )

    def handle_permission_request(
        self, view: QWebEngineView, permission: QWebEnginePermission
    ) -> None:
        origin = permission.origin()
        if (
            permission.permissionType() == QWebEnginePermission.PermissionType.MouseLock
            and origin.scheme() in ("http", "https")
            and origin.host()
        ):
            permission.grant()
            if view is self.tabs.currentWidget():
                self.status.setText("Mouse capture enabled — press Esc to release.")

    @staticmethod
    def handle_feature_permission(
        page: QWebEnginePage, origin: QUrl, feature: QWebEnginePage.Feature
    ) -> None:
        if (
            feature == QWebEnginePage.Feature.MouseLock
            and origin.scheme() in ("http", "https")
            and origin.host()
        ):
            page.setFeaturePermission(
                origin,
                feature,
                QWebEnginePage.PermissionPolicy.PermissionGrantedByUser,
            )

    def handle_fullscreen_request(
        self, view: QWebEngineView, request: QWebEngineFullScreenRequest
    ) -> None:
        if not request.toggleOn():
            if view is self._fullscreen_view:
                request.accept()
            else:
                request.reject()
            return

        if view is self._fullscreen_view:
            request.accept()
            return

        if not self._can_enter_fullscreen(view):
            request.reject()
            return

        request.accept()
        self._enter_fullscreen(view)

    def toggle_fullscreen(self) -> None:
        if self._fullscreen_view is not None:
            self._restore_fullscreen()
        else:
            self._enter_fullscreen(self.current_view())

    def _can_enter_fullscreen(self, view: QWebEngineView) -> bool:
        if (
            self.tabs.indexOf(view) < 0
            or view is not self.tabs.currentWidget()
            or self._fullscreen_view is not None
        ):
            return False

        subwindow: QWidget | None = self
        while subwindow is not None and not isinstance(subwindow, QMdiSubWindow):
            subwindow = subwindow.parentWidget()
        return isinstance(subwindow, QMdiSubWindow) and isinstance(
            self.window(), ArtifacialOS
        )

    def _enter_fullscreen(self, view: QWebEngineView) -> None:
        if not self._can_enter_fullscreen(view):
            return

        subwindow = self
        while not isinstance(subwindow, QMdiSubWindow):
            parent = subwindow.parentWidget()
            if parent is None:
                raise RuntimeError("The browser window is unavailable.")
            subwindow = parent
        host = self.window()
        if not isinstance(host, ArtifacialOS):
            raise RuntimeError("The desktop window is unavailable.")

        self._fullscreen_view = view
        self._fullscreen_subwindow = subwindow
        self._fullscreen_host = host
        self._fullscreen_host_was_maximized = host.isMaximized()
        self._fullscreen_host_was_fullscreen = host.isFullScreen()
        self._fullscreen_subwindow_was_maximized = subwindow.isMaximized()
        host.showFullScreen()
        QTimer.singleShot(350, lambda: self._finish_fullscreen_transition(view))

    def _finish_fullscreen_transition(self, view: QWebEngineView) -> None:
        if view is not self._fullscreen_view:
            return
        subwindow = self._fullscreen_subwindow
        if subwindow is not None:
            subwindow.showMaximized()
        view.update()

    def _restore_fullscreen(self) -> None:
        subwindow = self._fullscreen_subwindow
        host = self._fullscreen_host
        view = self._fullscreen_view
        if subwindow is None or host is None or view is None:
            return

        self._fullscreen_view = None
        self._fullscreen_subwindow = None
        self._fullscreen_host = None
        if self._fullscreen_subwindow_was_maximized:
            subwindow.showMaximized()
        else:
            subwindow.showNormal()
        self.tabs.setCurrentWidget(view)
        if self._fullscreen_host_was_fullscreen:
            host.showFullScreen()
        elif self._fullscreen_host_was_maximized:
            host.showMaximized()
        else:
            host.showNormal()

    def close_tab(self, index: int) -> None:
        view = self.tabs.widget(index)
        if view is self._fullscreen_view:
            self._restore_fullscreen()
        self.tabs.removeTab(index)
        if view is not None:
            view.deleteLater()
        if self.tabs.count() == 0:
            self.add_tab()

    def close_current_tab(self) -> None:
        index = self.tabs.currentIndex()
        if index >= 0:
            self.close_tab(index)

    def navigate(self) -> None:
        try:
            url = _normalize_browser_address(self.address.text())
        except ValueError as error:
            self.status.setText(str(error))
            return
        self.current_view().setUrl(QUrl(url))

    def update_tab_title(self, view: QWebEngineView, title: str) -> None:
        index = self.tabs.indexOf(view)
        if index >= 0:
            self.tabs.setTabText(index, (title or "New Tab")[:24])
        if view is self.tabs.currentWidget():
            window = self.window()
            if isinstance(window, QMdiSubWindow):
                window.setWindowTitle(f"{title or 'New Tab'} - Browser")

    def update_address(self, index: int) -> None:
        if index >= 0:
            self.update_view_address(self.current_view(), self.current_view().url())

    def update_view_address(self, view: QWebEngineView, url: QUrl) -> None:
        if view is self.tabs.currentWidget():
            self.address.setText(url.toString())


class WindowResizeHandle(QWidget):
    def __init__(self, window: InternalWindow, edges: Qt.Edges) -> None:
        super().__init__(window)
        self.window = window
        self.edges = edges
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground)
        self.setToolTip("Drag to resize")
        self._drag_origin: QPoint | None = None
        self._initial_geometry: QRect | None = None
        if edges in (Qt.Edge.LeftEdge, Qt.Edge.RightEdge):
            cursor = Qt.CursorShape.SizeHorCursor
        elif edges in (Qt.Edge.TopEdge, Qt.Edge.BottomEdge):
            cursor = Qt.CursorShape.SizeVerCursor
        elif edges in (
            Qt.Edge.TopEdge | Qt.Edge.LeftEdge,
            Qt.Edge.BottomEdge | Qt.Edge.RightEdge,
        ):
            cursor = Qt.CursorShape.SizeFDiagCursor
        else:
            cursor = Qt.CursorShape.SizeBDiagCursor
        self.setCursor(cursor)

    def mousePressEvent(self, event: QMouseEvent) -> None:
        if event.button() == Qt.MouseButton.LeftButton:
            self._drag_origin = event.globalPosition().toPoint()
            self._initial_geometry = self.window.geometry()
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event: QMouseEvent) -> None:
        if self._drag_origin is not None and self._initial_geometry is not None:
            delta = event.globalPosition().toPoint() - self._drag_origin
            geometry = QRect(self._initial_geometry)
            if self.edges & Qt.Edge.LeftEdge:
                geometry.setLeft(
                    min(
                        geometry.right() - self.window.minimumWidth() + 1,
                        geometry.left() + delta.x(),
                    )
                )
            if self.edges & Qt.Edge.RightEdge:
                geometry.setRight(
                    max(
                        geometry.left() + self.window.minimumWidth() - 1,
                        geometry.right() + delta.x(),
                    )
                )
            if self.edges & Qt.Edge.TopEdge:
                geometry.setTop(
                    min(
                        geometry.bottom() - self.window.minimumHeight() + 1,
                        geometry.top() + delta.y(),
                    )
                )
            if self.edges & Qt.Edge.BottomEdge:
                geometry.setBottom(
                    max(
                        geometry.top() + self.window.minimumHeight() - 1,
                        geometry.bottom() + delta.y(),
                    )
                )
            self.window.setGeometry(geometry)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event: QMouseEvent) -> None:
        if event.button() == Qt.MouseButton.LeftButton:
            self._drag_origin = None
            self._initial_geometry = None
            event.accept()
            return
        super().mouseReleaseEvent(event)


class WindowMoveHandle(QWidget):
    def __init__(self, window: InternalWindow, parent: QWidget | None = None) -> None:
        super().__init__(parent if parent is not None else window)
        self.window = window
        self._drag_origin: QPoint | None = None
        self._window_origin: QPoint | None = None
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground)
        self.setCursor(Qt.CursorShape.SizeAllCursor)
        self.setToolTip("Drag here to move this window")

    def mousePressEvent(self, event: QMouseEvent) -> None:
        if event.button() == Qt.MouseButton.LeftButton:
            self._drag_origin = event.globalPosition().toPoint()
            self._window_origin = self.window.pos()
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event: QMouseEvent) -> None:
        if (
            self._drag_origin is not None
            and self._window_origin is not None
            and not self.window.isMaximized()
        ):
            delta = event.globalPosition().toPoint() - self._drag_origin
            self.window.move(self._window_origin + delta)
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event: QMouseEvent) -> None:
        if event.button() == Qt.MouseButton.LeftButton:
            self._drag_origin = None
            self._window_origin = None
            event.accept()
            return
        super().mouseReleaseEvent(event)


class WindowTitleBar(QWidget):
    def __init__(self, window: InternalWindow) -> None:
        super().__init__()
        self.window = window
        self.setFixedHeight(32)
        self.setStyleSheet(f"background: {PANEL};")
        layout = QHBoxLayout(self)
        layout.setContentsMargins(10, 0, 10, 0)
        layout.setSpacing(6)

        self.window_buttons: list[QPushButton] = []
        for label, color, callback in (
            ("Close", "#ff5f57", window.close),
            ("Minimize", "#febc2e", window.showMinimized),
            ("Maximize", "#28c840", window.toggle_maximized),
        ):
            button = QPushButton(self)
            button.setAccessibleName(label)
            button.setToolTip(label)
            button.setFixedSize(13, 13)
            button.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            button.setCursor(Qt.CursorShape.PointingHandCursor)
            button.setStyleSheet(
                f"QPushButton {{ background: {color}; border: 0; "
                "border-radius: 6px; padding: 0; }"
                f"QPushButton:hover {{ background: {color}; }}"
            )
            button.clicked.connect(callback)
            layout.addWidget(button)
            self.window_buttons.append(button)

        self.title_label = QLabel(window.windowTitle())
        self.title_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(self.title_label, 1)
        self.move_handle = WindowMoveHandle(window, self)
        self.update_move_handle()

    def resizeEvent(self, event: QResizeEvent) -> None:
        super().resizeEvent(event)
        self.update_move_handle()

    def update_move_handle(self) -> None:
        self.move_handle.setGeometry(
            78, 0, max(0, self.width() - 78), self.height()
        )
        self.move_handle.raise_()
        for button in self.window_buttons:
            button.raise_()


class WindowOutline(QWidget):
    def __init__(self, parent: QWidget) -> None:
        super().__init__(parent)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)

    def paintEvent(self, event: QPaintEvent) -> None:
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(QPen(Qt.GlobalColor.white, 1))
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawRect(QRectF(self.rect()).adjusted(2.5, 2.5, -2.5, -2.5))


class InternalWindow(QMdiSubWindow):
    _resize_edges = (Qt.Edge.BottomEdge | Qt.Edge.RightEdge,)

    def __init__(self, key: str, parent: QWidget | None = None) -> None:
        super().__init__(parent)
        self.key = key
        self.setWindowFlags(
            Qt.WindowType.SubWindow | Qt.WindowType.FramelessWindowHint
        )
        self.setObjectName("appWindow")
        self.before_close: Callable[[], bool] | None = None
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setMinimumSize(380, 260)
        self.title_bar = WindowTitleBar(self)
        self.outline = WindowOutline(self)
        self.resize_handles = tuple(
            WindowResizeHandle(self, edges) for edges in self._resize_edges
        )

    def toggle_maximized(self) -> None:
        if self.isMaximized():
            self.showNormal()
        else:
            self.showMaximized()

    def resizeEvent(self, event: QResizeEvent) -> None:
        super().resizeEvent(event)
        self.update_resize_handles()

    def update_resize_handles(self) -> None:
        width, height = self.width(), self.height()
        corner = 36
        for handle in self.resize_handles:
            geometry = QRect(width - corner, height - corner, corner, corner)
            handle.setGeometry(geometry)
            handle.raise_()
        self.outline.setGeometry(self.rect())
        self.outline.raise_()

    def closeEvent(self, event: QCloseEvent) -> None:
        if self.before_close is not None and not self.before_close():
            event.ignore()
            return
        event.accept()


class DesktopArea(QMdiArea):
    def viewportEvent(self, event: QEvent) -> bool:
        handled = super().viewportEvent(event)
        if event.type() == QEvent.Type.Paint:
            painter = QPainter(self.viewport())
            painter.fillRect(self.viewport().rect(), BG)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush("#211e47")
            painter.drawEllipse(QRectF(620, -280, 630, 640))
            painter.setBrush("#172c3c")
            painter.drawEllipse(QRectF(-280, 390, 600, 600))
        return handled


class ArtifacialOS(QMainWindow):
    """Desktop shell and app windows, all hosted in one Qt application window."""

    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle("ArtifacialOS")
        self.resize(1100, 720)
        self.setMinimumSize(760, 520)
        self.open_windows: dict[str, InternalWindow] = {}
        self.notes_path = Path.home() / ".artifacialos" / "notes.json"
        self.filesystem: dict[str, str] = {
            "Welcome.txt": (
                "Welcome to ArtifacialOS!\n\n"
                "A little desktop made with Python and Qt."
            ),
            "Ideas.txt": (
                "Things to build:\n- A tiny game\n- A personal website\n"
                "- Something wonderful"
            ),
        }
        self.setStyleSheet(_stylesheet())
        self._build_desktop()

    def _build_desktop(self) -> None:
        desktop = QWidget()
        layout = QVBoxLayout(desktop)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        self.desktop_heading = QLabel("ARTIFACIAL")
        self.desktop_heading.setObjectName("desktopTitle")
        self.desktop_heading.setContentsMargins(22, 14, 0, 10)
        layout.addWidget(self.desktop_heading)

        self.mdi = DesktopArea()
        self.mdi.setViewMode(QMdiArea.ViewMode.SubWindowView)
        self.mdi.setOption(QMdiArea.AreaOption.DontMaximizeSubWindowOnActivation, True)
        layout.addWidget(self.mdi, 1)

        self.dock = QWidget()
        self.dock.setObjectName("dock")
        dock_layout = QHBoxLayout(self.dock)
        dock_layout.setContentsMargins(12, 6, 14, 6)
        dock_layout.setSpacing(6)
        launcher = QPushButton("◈")
        launcher.setObjectName("launcherButton")
        launcher.clicked.connect(self.toggle_launcher)
        dock_layout.addWidget(launcher)
        for key, label, icon, callback in (
            ("browser", "Browser", "◎", self.open_browser),
            ("files", "Files", "▣", self.open_files),
            ("notes", "Notes", "▤", self.open_notes),
            ("calculator", "Calculator", "＋", self.open_calculator),
            ("terminal", "Terminal", ">_", self.open_terminal),
        ):
            button = QPushButton(f"{icon}  {label}")
            button.clicked.connect(
                lambda _checked=False, app_key=key, launch=callback: (
                    self._toggle_dock_app(app_key, launch)
                )
            )
            dock_layout.addWidget(button)
        dock_layout.addStretch(1)
        settings = QPushButton("⚙")
        settings.clicked.connect(
            lambda _checked=False: self._toggle_dock_app(
                "settings", self.open_settings
            )
        )
        dock_layout.addWidget(settings)
        self.clock_label = QLabel()
        self.clock_label.setAlignment(Qt.AlignmentFlag.AlignRight)
        dock_layout.addWidget(self.clock_label)
        layout.addWidget(self.dock)

        self.setCentralWidget(desktop)
        self.clock_timer = QTimer(self)
        self.clock_timer.timeout.connect(self._tick_clock)
        self.clock_timer.start(1000)
        self._tick_clock()

    def closeEvent(self, event: QCloseEvent) -> None:
        for window in tuple(self.open_windows.values()):
            if window.before_close is not None and not window.before_close():
                event.ignore()
                return
        event.accept()

    def _tick_clock(self) -> None:
        self.clock_label.setText(datetime.now().strftime("%a, %b %d\n%I:%M %p"))

    def _toggle_dock_app(self, key: str, launch: Callable[[], None]) -> None:
        existing = self.open_windows.get(key)
        if existing is not None:
            if existing.isMinimized() or not existing.isVisible():
                existing.showNormal()
                existing.raise_()
                self.mdi.setActiveSubWindow(existing)
                return
            existing.close()
            return
        launch()

    def _window(
        self, key: str, title: str, size: QSize = QSize(680, 460)
    ) -> QWidget | None:
        existing = self.open_windows.get(key)
        if existing is not None:
            existing.showNormal()
            existing.raise_()
            self.mdi.setActiveSubWindow(existing)
            return None

        window = InternalWindow(key)
        window.setWindowTitle(title)
        window.resize(size)
        container = QWidget()
        container_layout = QVBoxLayout(container)
        container_layout.setContentsMargins(0, 0, 0, 0)
        container_layout.setSpacing(0)
        container_layout.addWidget(window.title_bar)
        body = QWidget()
        container_layout.addWidget(body, 1)
        window.setWidget(container)
        window.title_bar.title_label.setText(title)
        window.update_resize_handles()
        self.mdi.addSubWindow(window)
        self.open_windows[key] = window
        window.destroyed.connect(
            lambda _object=None, app_key=key, item=window: self._forget_window(
                app_key, item
            )
        )
        window.show()
        return body

    def _forget_window(self, key: str, window: InternalWindow) -> None:
        if self.open_windows.get(key) is window:
            self.open_windows.pop(key, None)

    @staticmethod
    def _layout(widget: QWidget, *, margins: int = 16) -> QVBoxLayout:
        layout = QVBoxLayout(widget)
        layout.setContentsMargins(margins, margins, margins, margins)
        layout.setSpacing(10)
        return layout

    @staticmethod
    def _label(text: str, *, muted: bool = False, size: int | None = None) -> QLabel:
        label = QLabel(text)
        if muted:
            label.setStyleSheet(f"color: {MUTED};")
        if size is not None:
            label.setStyleSheet(f"font-size: {size}pt; font-weight: bold;")
        return label

    @staticmethod
    def _button(text: str, callback: Callable[[], None]) -> QPushButton:
        button = QPushButton(text)
        button.clicked.connect(callback)
        return button

    def toggle_launcher(self) -> None:
        existing = self.open_windows.get("launcher")
        if existing is not None:
            existing.close()
            return
        body = self._window("launcher", "Your apps", QSize(300, 410))
        if body is None:
            return
        layout = self._layout(body, margins=14)
        layout.addWidget(self._label("Your apps", size=16))
        for label, callback in (
            ("◎   Browser", self.open_browser),
            ("▣   Files", self.open_files),
            ("▤   Notes", self.open_notes),
            ("＋   Calculator", self.open_calculator),
            (">_   Terminal", self.open_terminal),
            ("⚙   Settings", self.open_settings),
            ("?   Welcome", self.open_welcome),
        ):
            layout.addWidget(self._button(label, callback))
        layout.addStretch(1)

    def open_welcome(self) -> None:
        body = self._window("welcome", "Welcome to ArtifacialOS", QSize(560, 400))
        if body is None:
            return
        layout = self._layout(body, margins=24)
        layout.addWidget(self._label("Welcome home.", size=24))
        layout.addWidget(
            self._label(
                "This is a desktop simulator built with Python and Qt.\n"
                "It can't replace the operating system installed on your computer, "
                "but\nyou can open apps, save notes, browse sample files, and try "
                "the shell.",
                muted=True,
            )
        )
        for text, action in (
            ("Open Files", self.open_files),
            ("Write a note", self.open_notes),
            ("Try the Terminal", self.open_terminal),
        ):
            layout.addWidget(self._button(text, action))
        layout.addStretch(1)

    def open_browser(self) -> None:
        body = self._window("browser", "Browser", QSize(760, 500))
        if body is None:
            return
        layout = QVBoxLayout(body)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.addWidget(BrowserWidget())

    def open_files(self) -> None:
        body = self._window("files", "Files", QSize(700, 460))
        if body is None:
            return
        layout = QHBoxLayout(body)
        layout.setContentsMargins(0, 0, 0, 0)
        sidebar = QWidget()
        sidebar.setFixedWidth(170)
        sidebar_layout = QVBoxLayout(sidebar)
        sidebar_layout.setContentsMargins(10, 12, 10, 12)
        listing = QListWidget()
        content = QWidget()
        content_layout = QVBoxLayout(content)
        heading = self._label("Home", size=18)
        content_layout.addWidget(heading)
        content_layout.addWidget(listing, 1)
        open_button = self._button(
            "Open selected file",
            lambda: self._open_selected_file(listing),
        )
        content_layout.addWidget(open_button, alignment=Qt.AlignmentFlag.AlignRight)
        for location in ("Home", "Documents", "Desktop", "About this computer"):
            sidebar_layout.addWidget(
                self._button(
                    location,
                    lambda item=location: self._show_file_location(
                        item, listing, heading
                    ),
                )
            )
        sidebar_layout.addStretch(1)
        layout.addWidget(sidebar)
        layout.addWidget(content, 1)
        listing.itemDoubleClicked.connect(lambda _item: self._open_selected_file(listing))
        self._show_file_location("Home", listing, heading)

    def _show_file_location(
        self, location: str, listing: QListWidget, heading: QLabel
    ) -> None:
        heading.setText(location)
        listing.clear()
        if location == "About this computer":
            listing.addItems(
                [
                    f"ArtifacialOS 1.0  ·  Python {platform.python_version()}",
                    f"Host: {platform.system()} {platform.release()}",
                ]
            )
            return
        files = (
            self.filesystem
            if location in ("Home", "Documents")
            else {"Readme.txt": "Your desktop is looking good."}
        )
        listing.addItems(f"▤   {name}" for name in files)

    def _open_selected_file(self, listing: QListWidget) -> None:
        selected = listing.currentItem()
        if selected is None:
            return
        filename = selected.text().split("   ", 1)[-1]
        content = self.filesystem.get(filename)
        if content is None:
            return
        body = self._window(f"file:{filename}", filename, QSize(560, 400))
        if body is None:
            return
        layout = self._layout(body)
        text = QPlainTextEdit()
        text.setPlainText(content)
        text.setReadOnly(True)
        layout.addWidget(text)

    def open_notes(self) -> None:
        body = self._window("notes", "Notes", QSize(820, 560))
        if body is None:
            return
        notes: list[dict[str, str]] = []
        current_id: str | None = None
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
                            notes.append(
                                {
                                    "id": item["id"],
                                    "title": item["title"],
                                    "body": item["body"],
                                    "updated": str(item.get("updated", "")),
                                }
                            )
                elif stored:
                    notes.append(
                        {
                            "id": uuid4().hex,
                            "title": "My first note",
                            "body": stored,
                            "updated": datetime.now().isoformat(timespec="seconds"),
                        }
                    )
        except (OSError, json.JSONDecodeError, ValueError) as error:
            QMessageBox.critical(body, "Could not load notes", str(error))

        root = self._layout(body, margins=14)
        top = QHBoxLayout()
        top.addWidget(self._label("My notes", size=21))
        top.addStretch(1)
        new_button = self._button("＋  New note", lambda: create_note())
        top.addWidget(new_button)
        root.addLayout(top)
        split = QSplitter()
        sidebar = QWidget()
        sidebar.setMinimumWidth(210)
        side_layout = QVBoxLayout(sidebar)
        search = QLineEdit()
        search.setPlaceholderText("Search notes...")
        side_layout.addWidget(search)
        note_list = QListWidget()
        side_layout.addWidget(note_list, 1)
        split.addWidget(sidebar)
        editor_area = QWidget()
        editor_layout = QVBoxLayout(editor_area)
        title = QLineEdit()
        title.setPlaceholderText("Untitled note")
        title.setStyleSheet("font-size: 20pt; font-weight: bold;")
        editor = QTextEdit()
        editor.setPlaceholderText("Start writing...")
        editor_layout.addWidget(title)
        editor_layout.addWidget(editor, 1)
        split.addWidget(editor_area)
        split.setStretchFactor(1, 1)
        root.addWidget(split, 1)
        footer = QHBoxLayout()
        status = self._label("", muted=True)
        footer.addWidget(status)
        footer.addStretch(1)
        delete_button = self._button("Delete note", lambda: delete_note())
        save_button = self._button("Save now", lambda: save_note())
        footer.addWidget(delete_button)
        footer.addWidget(save_button)
        root.addLayout(footer)

        save_timer = QTimer(body)
        save_timer.setSingleShot(True)
        save_timer.setInterval(700)

        def refresh_list() -> None:
            query = search.text().strip().lower()
            ordered = sorted(notes, key=lambda item: item["updated"], reverse=True)
            visible = [
                note
                for note in ordered
                if not query
                or query in note["title"].lower()
                or query in note["body"].lower()
            ]
            note_list.clear()
            for note in visible:
                from PySide6.QtWidgets import QListWidgetItem

                item = QListWidgetItem(note["title"] or "Untitled note")
                item.setData(Qt.ItemDataRole.UserRole, note["id"])
                note_list.addItem(item)
                if note["id"] == current_id:
                    note_list.setCurrentItem(item)

        def update_status(message: str = "All changes saved") -> None:
            words = len(editor.toPlainText().split()) if current_id else 0
            word_label = "word" if words == 1 else "words"
            status.setText(f"{message}  ·  {words} {word_label}")
            status.setStyleSheet(
                f"color: {GREEN if message.startswith('Saved') else MUTED};"
            )

        def load_note(note: dict[str, str] | None) -> None:
            nonlocal current_id, loading
            current_id = note["id"] if note else None
            loading = True
            title.setText(note["title"] if note else "")
            editor.setPlainText(note["body"] if note else "")
            title.setEnabled(note is not None)
            editor.setEnabled(note is not None)
            loading = False
            refresh_list()
            update_status("Ready" if note else "Create a note to get started")

        def persist_notes() -> bool:
            try:
                self.notes_path.parent.mkdir(parents=True, exist_ok=True)
                temporary_path = self.notes_path.with_suffix(".tmp")
                temporary_path.write_text(
                    json.dumps(
                        {"version": 1, "notes": notes},
                        ensure_ascii=False,
                        indent=2,
                    ),
                    encoding="utf-8",
                )
                temporary_path.replace(self.notes_path)
            except OSError as error:
                QMessageBox.critical(body, "Could not save notes", str(error))
                update_status("Save failed")
                return False
            return True

        def save_note() -> bool:
            save_timer.stop()
            note = next((item for item in notes if item["id"] == current_id), None)
            if note is None:
                return True
            note["title"] = title.text().strip() or "Untitled note"
            note["body"] = editor.toPlainText()
            note["updated"] = datetime.now().isoformat(timespec="seconds")
            if not persist_notes():
                return False
            refresh_list()
            update_status(f"Saved at {datetime.now().strftime('%I:%M %p')}")
            return True

        def schedule_save() -> None:
            if loading or current_id is None:
                return
            update_status("Unsaved changes")
            save_timer.start()

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
            title.selectAll()
            schedule_save()

        def delete_note() -> None:
            if current_id is None:
                return
            note = next((item for item in notes if item["id"] == current_id), None)
            if note is None:
                return
            answer = QMessageBox.question(
                body,
                "Delete note",
                f"Delete “{note['title'] or 'Untitled note'}”?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No,
            )
            if answer != QMessageBox.StandardButton.Yes or not save_note():
                return
            notes.remove(note)
            if not persist_notes():
                notes.append(note)
                load_note(note)
                return
            load_note(notes[0] if notes else None)

        def select_note() -> None:
            selected = note_list.currentItem()
            if selected is None:
                return
            selected_id = selected.data(Qt.ItemDataRole.UserRole)
            note = next((item for item in notes if item["id"] == selected_id), None)
            if note is not None and note["id"] != current_id and save_note():
                load_note(note)

        search.textChanged.connect(refresh_list)
        note_list.itemSelectionChanged.connect(select_note)
        title.textChanged.connect(schedule_save)
        editor.textChanged.connect(schedule_save)
        save_timer.timeout.connect(save_note)
        delete_button.clicked.connect(delete_note)
        save_button.clicked.connect(save_note)
        subwindow = self.open_windows["notes"]
        subwindow.before_close = save_note
        refresh_list()
        load_note(notes[0] if notes else None)

    def open_calculator(self) -> None:
        body = self._window("calculator", "Calculator", QSize(360, 430))
        if body is None:
            return
        layout = self._layout(body, margins=14)
        display = QLineEdit()
        display.setAlignment(Qt.AlignmentFlag.AlignRight)
        display.setStyleSheet("font-size: 23pt;")
        layout.addWidget(display)
        grid = QGridLayout()
        grid.setSpacing(6)
        keys = (
            "C", "(", ")", "÷", "7", "8", "9", "×", "4", "5", "6", "−",
            "1", "2", "3", "+", "⌫", "0", ".", "=",
        )

        def press(value: str) -> None:
            if value == "C":
                display.clear()
            elif value == "⌫":
                display.setText(display.text()[:-1])
            elif value == "=":
                try:
                    display.setText(str(self._calculate(display.text())))
                except (ValueError, ZeroDivisionError, OverflowError) as error:
                    QMessageBox.critical(body, "Calculation error", str(error))
            else:
                display.setText(
                    display.text() + {"÷": "/", "×": "*", "−": "-"}.get(value, value)
                )

        for index, key in enumerate(keys):
            button = self._button(key, lambda item=key: press(item))
            grid.addWidget(button, index // 4, index % 4)
        layout.addLayout(grid, 1)
        display.returnPressed.connect(lambda: press("="))

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
        body = self._window("terminal", "Terminal", QSize(720, 470))
        if body is None:
            return
        layout = self._layout(body, margins=14)
        output = QPlainTextEdit()
        output.setReadOnly(True)
        output.setStyleSheet(
            "background: #0b0e14; color: #f0f2f8; font: 13pt Menlo;"
        )
        command = QLineEdit()
        command.setStyleSheet("font: 13pt Menlo;")
        command.setText("help")
        layout.addWidget(output, 1)
        layout.addWidget(command)

        def write(text: str) -> None:
            output.appendPlainText(text)

        def run_command() -> None:
            raw = command.text().strip()
            command.clear()
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
                output.clear()
            else:
                write(f"{name}: command not found (try 'help')")

        command.returnPressed.connect(run_command)
        run_command()
        command.setFocus()

    def open_settings(self) -> None:
        body = self._window("settings", "Settings", QSize(520, 400))
        if body is None:
            return
        layout = self._layout(body, margins=24)
        layout.addWidget(self._label("System settings", size=20))
        layout.addWidget(self._label("About this desktop", size=12))
        layout.addWidget(
            self._label(
                f"ArtifacialOS 1.0\nPython {platform.python_version()} · "
                f"{platform.system()}\nA friendly desktop simulator.",
                muted=True,
            )
        )
        layout.addWidget(self._label("Built-in apps", size=12))
        layout.addWidget(
            self._label(
                "Browser  ·  Files  ·  Notes  ·  Calculator  ·  Terminal",
                muted=True,
            )
        )
        layout.addStretch(1)


def main() -> None:
    app = QApplication(sys.argv)
    app.setApplicationName("ArtifacialOS")
    window = ArtifacialOS()
    window.show()
    previous_sigint_handler = signal.signal(signal.SIGINT, lambda *_: app.quit())
    try:
        exit_code = app.exec()
    except KeyboardInterrupt:
        exit_code = 0
    finally:
        signal.signal(signal.SIGINT, previous_sigint_handler)
    raise SystemExit(exit_code)


if __name__ == "__main__":
    main()
