"""
NovaMut - Sistema de Gestion Mutual
Version 4.0

Desarrollado por Diego Alejandro Fernandez y Joshua Giuliano Venticinque.
Prohibida su copia o distribucion sin autorizacion de los autores.

Historial:
  4.0  Nuevo nombre (NovaMut, antes SIGEMUT). Liquidacion mensual, control
       de credito, exportacion de reportes, busqueda por DNI/CUIL, roles
       aplicados, backup automatico, auditoria completa, configuracion de
       la entidad, fechas en formato ISO en la base.
  3.3  Terminos y condiciones y apartado Programadores.
  3.2  Numeracion automatica de socios desde 1001.
  3.1  Credenciales de socio en PDF.

Requiere:
    Python 3.9+
    pip install customtkinter pillow reportlab

Usuario por defecto en una base nueva: admin / admin
"""

import os
import sys
import sqlite3
import hashlib
import secrets
import socket
import platform
import calendar
import csv
import shutil
from datetime import datetime, timedelta
from contextlib import contextmanager
from decimal import Decimal, InvalidOperation
from tkinter import messagebox, filedialog

try:
    import customtkinter as ctk
except ImportError:
    print("ERROR: falta instalar customtkinter.")
    print("Ejecuta:  pip install customtkinter pillow")
    sys.exit(1)


# =====================================================================
#  CONFIGURACION VISUAL
# =====================================================================
ctk.set_appearance_mode("light")
ctk.set_default_color_theme("blue")

# --- Paleta corporativa (look Windows moderno) ---
COLOR_SIDEBAR       = "#1e293b"
COLOR_SIDEBAR_HOVER = "#334155"
COLOR_SIDEBAR_TEXT  = "#cbd5e1"
COLOR_SIDEBAR_SEL   = "#2563eb"
COLOR_BG            = "#f9fafb"
COLOR_CARD          = "#ffffff"
COLOR_BORDER        = "#e5e7eb"
COLOR_BORDER_STRONG = "#d1d5db"
COLOR_TEXT          = "#111827"
COLOR_TEXT_MUTED    = "#6b7280"
COLOR_TEXT_LIGHT    = "#9ca3af"
COLOR_ACCENT        = "#2563eb"
COLOR_ACCENT_HOVER  = "#1d4ed8"
COLOR_ACCENT_BG     = "#dbeafe"
COLOR_ACCENT_TXT    = "#1e40af"
COLOR_SUCCESS       = "#16a34a"
COLOR_SUCCESS_HOVER = "#15803d"
COLOR_SUCCESS_BG    = "#dcfce7"
COLOR_SUCCESS_TXT   = "#166534"
COLOR_WARNING       = "#f59e0b"
COLOR_WARNING_BG    = "#fef3c7"
COLOR_WARNING_TXT   = "#92400e"
COLOR_DANGER        = "#dc2626"
COLOR_DANGER_HOVER  = "#b91c1c"
COLOR_DANGER_BG     = "#fee2e2"
COLOR_DANGER_TXT    = "#991b1b"
COLOR_ZEBRA         = "#f9fafb"

FONT_FAMILY = "Segoe UI"
def F(size=13, weight="normal"):
    return ctk.CTkFont(family=FONT_FAMILY, size=size, weight=weight)


MESES = ["ENERO","FEBRERO","MARZO","ABRIL","MAYO","JUNIO",
         "JULIO","AGOSTO","SEPTIEMBRE","OCTUBRE","NOVIEMBRE","DICIEMBRE"]


# =====================================================================
#  RUTAS Y PERSISTENCIA
# =====================================================================
def _base_dir():
    if getattr(sys, "frozen", False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

def _recurso(nombre):
    """Ruta de un archivo que viaja dentro del .exe (icono, etc)."""
    base = getattr(sys, "_MEIPASS", None) or os.path.dirname(
        os.path.abspath(__file__))
    for d in (base, os.path.dirname(base), _base_dir()):
        p = os.path.join(d, nombre)
        if os.path.exists(p):
            return p
    return None


APP_NOMBRE = "NovaMut"
APP_VERSION = "4.0"
DB_NOMBRE = "novamut.db"
DB_PATH = os.path.join(_base_dir(), DB_NOMBRE)
DB_VIEJA = os.path.join(_base_dir(), "sigemut.db")   # nombre anterior
BACKUP_DIR = os.path.join(_base_dir(), "backups")
BACKUPS_AUTO_A_CONSERVAR = 30
SCHEMA_VERSION = 3
ICONO = "novamut.ico"


# =====================================================================
#  ROLES Y PERMISOS
# =====================================================================
ROLES = ("SUPERADMIN", "ADMIN", "OPERADOR", "CONSULTA")
ROL_NIVEL = {"SUPERADMIN": 4, "ADMIN": 3, "OPERADOR": 2, "CONSULTA": 1}

MAX_INTENTOS_LOGIN = 5

# Numeracion automatica de socios: el primero es NRO_SOCIO_INICIAL y
# cada alta toma el siguiente libre (el mayor existente + 1).
NRO_SOCIO_INICIAL = 1001


def proximo_nro_socio(con):
    """Proximo numero de socio libre (nunca menor a NRO_SOCIO_INICIAL)."""
    row = con.execute("SELECT MAX(nro_socio) AS m FROM socios").fetchone()
    return max(NRO_SOCIO_INICIAL, (row["m"] or 0) + 1)
MINUTOS_BLOQUEO = 15


def rol_nivel(rol):
    return ROL_NIVEL.get(rol, 0)


# Nivel minimo para cada tipo de accion
NIVEL_OPERAR = ROL_NIVEL["OPERADOR"]   # cargar, modificar, cobrar
NIVEL_ADMIN = ROL_NIVEL["ADMIN"]       # revertir cobros, configuracion


def tiene_nivel(usuario, nivel):
    return bool(usuario) and rol_nivel(usuario.get("rol")) >= nivel


def puede_gestionar_rol(rol_actor, rol_objetivo):
    if rol_actor == "SUPERADMIN":
        return True
    return rol_nivel(rol_actor) > rol_nivel(rol_objetivo)


def roles_asignables(rol_actor):
    if rol_actor == "SUPERADMIN":
        return ROLES
    return tuple(r for r in ROLES if rol_nivel(rol_actor) > rol_nivel(r))


def val_password_fuerte(pwd):
    if not pwd or len(pwd) < 8:
        return False
    return any(c.isalpha() for c in pwd) and any(c.isdigit() for c in pwd)


# =====================================================================
#  VALIDADORES Y HELPERS DE PARSEO
# =====================================================================
def parse_fecha_iso(s):
    if not s: return None
    try: return datetime.fromisoformat(s)
    except ValueError: return None


def parse_fecha(s):
    if not s: return None
    s = s.strip()
    if not s: return None
    for fmt in ("%d/%m/%Y", "%d-%m-%Y", "%Y-%m-%d"):
        try: return datetime.strptime(s, fmt)
        except ValueError: pass
    return None


def fecha_db(s):
    """Fecha ingresada en pantalla (dd/mm/aaaa) -> formato de la base
    (aaaa-mm-dd). Vacio -> ''. Invalida -> None."""
    if not s or not str(s).strip():
        return ""
    dt = parse_fecha(str(s))
    return dt.strftime("%Y-%m-%d") if dt else None


def fecha_ui(s):
    """Fecha de la base (aaaa-mm-dd, o formato viejo) -> dd/mm/aaaa."""
    if not s:
        return ""
    dt = parse_fecha(str(s)[:10])
    return dt.strftime("%d/%m/%Y") if dt else str(s)


def hoy_db():
    return datetime.now().strftime("%Y-%m-%d")


def hoy_ui():
    return datetime.now().strftime("%d/%m/%Y")


def solo_digitos(s):
    return "".join(c for c in str(s or "") if c.isdigit())


def val_fecha(s):
    if not s or not s.strip(): return True
    return parse_fecha(s) is not None


def val_cuil(s):
    if not s or not s.strip(): return True
    d = "".join(c for c in s if c.isdigit())
    return len(d) == 11


def val_mail(s):
    if not s or not s.strip(): return True
    return "@" in s and "." in s.split("@")[-1]


def fmt_inaes(fecha_str):
    dt = parse_fecha(fecha_str)
    return dt.strftime("%Y%m%d") if dt else ""


def parse_monto(s):
    if not s or not str(s).strip():
        return 0.0
    try:
        d = Decimal(str(s).strip().replace(",", "."))
    except InvalidOperation:
        return None
    return float(d.quantize(Decimal("0.01")))


def fmt_moneda(v):
    """Formato argentino: $1.234,56"""
    try: txt = f"{float(v):,.2f}"
    except (ValueError, TypeError): txt = "0.00"
    return "$" + txt.replace(",", "X").replace(".", ",").replace("X", ".")


def fmt_numero_csv(v):
    """Importe para CSV que abre bien en Excel en espanol: 1234,56"""
    try: return f"{float(v):.2f}".replace(".", ",")
    except (ValueError, TypeError): return "0,00"


def sumar_meses(fecha, meses):
    """Suma N meses a una fecha respetando fin de mes."""
    y = fecha.year + (fecha.month - 1 + meses) // 12
    m = (fecha.month - 1 + meses) % 12 + 1
    d = min(fecha.day, calendar.monthrange(y, m)[1])
    return fecha.replace(year=y, month=m, day=d)


# =====================================================================
#  BASE DE DATOS
# =====================================================================
@contextmanager
def get_conn():
    con = sqlite3.connect(DB_PATH)
    con.row_factory = sqlite3.Row
    con.execute("PRAGMA foreign_keys = ON")
    try:
        yield con
        con.commit()
    except Exception:
        con.rollback()
        raise
    finally:
        con.close()


PBKDF2_ITERS = 260_000


def hash_password(password, salt):
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"),
                              salt.encode("utf-8"), PBKDF2_ITERS)
    return f"pbkdf2${PBKDF2_ITERS}${dk.hex()}"


def _hash_password_legacy(password, salt):
    h = hashlib.sha256()
    h.update((salt + password).encode("utf-8"))
    return h.hexdigest()


def verify_password(password, salt, stored_hash):
    if stored_hash.startswith("pbkdf2$"):
        try:
            _, iters, hex_hash = stored_hash.split("$", 2)
            dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"),
                                      salt.encode("utf-8"), int(iters))
            return secrets.compare_digest(dk.hex(), hex_hash)
        except (ValueError, IndexError):
            return False
    return secrets.compare_digest(_hash_password_legacy(password, salt),
                                   stored_hash)


_MIGRACIONES = {
    2: [
        "ALTER TABLE usuarios ADD COLUMN debe_cambiar_pwd "
            "INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE usuarios ADD COLUMN intentos_fallidos "
            "INTEGER NOT NULL DEFAULT 0",
        "ALTER TABLE usuarios ADD COLUMN bloqueado_hasta TEXT",
        "ALTER TABLE usuarios ADD COLUMN creado_por TEXT",
        """CREATE TABLE IF NOT EXISTS log_auditoria (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            fecha TEXT NOT NULL,
            usuario_actor TEXT NOT NULL,
            accion TEXT NOT NULL,
            detalle TEXT
        )""",
    ],
    3: [
        "ALTER TABLE usuarios ADD COLUMN terminos_version TEXT",
        "ALTER TABLE usuarios ADD COLUMN terminos_fecha TEXT",
    ],
}

# Columnas de fecha que en la version 4.0 pasan de dd/mm/aaaa a aaaa-mm-dd
_COLUMNAS_FECHA = {
    "socios": ("nro_socio", ["fec_nac", "fec_ing", "fec_baj", "fec_egr"]),
    "desc_compras_sno": ("id", ["fec_factura", "fe_1cu_pro", "fe_1cu_soc"]),
    "cuotas_proveedor": ("id", ["fec_vencimiento", "fec_pago"]),
    "cuotas_socio": ("id", ["fec_vencimiento", "fec_cobro"]),
}


def _migrar_fechas_iso(con):
    for tabla, (pk, cols) in _COLUMNAS_FECHA.items():
        filas = con.execute(
            f"SELECT {pk}, {', '.join(cols)} FROM {tabla}").fetchall()
        for f in filas:
            nuevos = {}
            for c in cols:
                v = f[c]
                if v and not (len(v) == 10 and v[4] == "-"):
                    iso = fecha_db(v)
                    if iso:
                        nuevos[c] = iso
            if nuevos:
                sets = ", ".join(f"{c}=?" for c in nuevos)
                con.execute(f"UPDATE {tabla} SET {sets} WHERE {pk}=?",
                            list(nuevos.values()) + [f[pk]])


def _aplicar_migraciones(con):
    row = con.execute("SELECT valor FROM meta WHERE clave = 'schema_version'"
                       ).fetchone()
    version_actual = int(row["valor"]) if row else 0
    for v in range(version_actual + 1, SCHEMA_VERSION + 1):
        for stmt in _MIGRACIONES.get(v, []):
            try: con.execute(stmt)
            except sqlite3.OperationalError: pass  # columna ya existe
        if v == 3:
            _migrar_fechas_iso(con)

    sin_superadmin = con.execute(
        "SELECT COUNT(*) AS c FROM usuarios "
        "WHERE rol = 'SUPERADMIN' AND activo = 1").fetchone()["c"] == 0
    if sin_superadmin:
        con.execute("UPDATE usuarios SET rol = 'SUPERADMIN' "
                    "WHERE id = (SELECT MIN(id) FROM usuarios)")

    if row:
        con.execute("UPDATE meta SET valor = ? WHERE clave = 'schema_version'",
                    (str(SCHEMA_VERSION),))
    else:
        con.execute("INSERT INTO meta (clave, valor) VALUES "
                    "('schema_version', ?)", (str(SCHEMA_VERSION),))


def _adoptar_base_vieja():
    """Si existe la base con el nombre anterior (sigemut.db) y todavia no
    hay novamut.db, la copia con el nombre nuevo. La vieja queda intacta
    como respaldo."""
    if not os.path.exists(DB_PATH) and os.path.exists(DB_VIEJA):
        try:
            hacer_backup(DB_PATH, origen_path=DB_VIEJA)
        except Exception:
            shutil.copy2(DB_VIEJA, DB_PATH)


def init_db():
    _adoptar_base_vieja()
    with get_conn() as con:
        con.executescript("""
        CREATE TABLE IF NOT EXISTS meta (
            clave TEXT PRIMARY KEY, valor TEXT
        );
        CREATE TABLE IF NOT EXISTS usuarios (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            usuario TEXT UNIQUE NOT NULL,
            nombre TEXT NOT NULL,
            password TEXT NOT NULL,
            salt TEXT NOT NULL,
            rol TEXT NOT NULL DEFAULT 'OPERADOR',
            activo INTEGER NOT NULL DEFAULT 1,
            creado TEXT NOT NULL,
            ultimo_log TEXT
        );
        CREATE TABLE IF NOT EXISTS log_accesos (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            usuario TEXT NOT NULL, fecha TEXT NOT NULL,
            exito INTEGER NOT NULL, host TEXT
        );
        CREATE TABLE IF NOT EXISTS socios (
            nro_socio INTEGER PRIMARY KEY,
            nombre TEXT NOT NULL,
            direccion TEXT, localidad TEXT, cp TEXT,
            telefono TEXT, cbu TEXT,
            extranjero TEXT DEFAULT 'N',
            estado_civil TEXT, sexo TEXT, fec_nac TEXT,
            es_pep TEXT DEFAULT 'N', riesgo TEXT DEFAULT 'B',
            fec_ing TEXT, fec_baj TEXT, fec_egr TEXT, liq_mot TEXT,
            categoria TEXT,
            credit_max REAL DEFAULT 0,
            cre_max_mes REAL DEFAULT 0,
            tope_emp REAL DEFAULT 0,
            tipo_doc TEXT, cuil TEXT, mail TEXT,
            servicio1 TEXT, servicio2 TEXT, servicio3 TEXT,
            usr_alta TEXT, fec_alta TEXT,
            usr_mod TEXT, fec_mod TEXT
        );
        CREATE TABLE IF NOT EXISTS proveedores (
            cod_proveedor INTEGER PRIMARY KEY AUTOINCREMENT,
            razon_social TEXT NOT NULL,
            cuit TEXT,
            direccion TEXT, localidad TEXT, cp TEXT,
            telefono TEXT, mail TEXT,
            condicion_iva TEXT, cbu TEXT,
            activo INTEGER DEFAULT 1,
            usr_alta TEXT, fec_alta TEXT
        );
        CREATE TABLE IF NOT EXISTS desc_compras_sno (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            tip_compro TEXT NOT NULL,
            nro_compro INTEGER NOT NULL,
            cod_proveedor INTEGER,
            nro_socio INTEGER NOT NULL,
            concepto TEXT,
            fec_factura TEXT, nro_factura TEXT,
            importe REAL NOT NULL DEFAULT 0,
            can_cuot_pr INTEGER DEFAULT 1,
            can_cuot_so INTEGER DEFAULT 1,
            fe_1cu_pro TEXT, fe_1cu_soc TEXT,
            observacion TEXT,
            estado TEXT DEFAULT 'ACTIVO',
            usr_alta TEXT, fec_alta TEXT,
            usr_mod TEXT, fec_mod TEXT,
            UNIQUE(tip_compro, nro_compro),
            FOREIGN KEY (cod_proveedor)
              REFERENCES proveedores(cod_proveedor),
            FOREIGN KEY (nro_socio) REFERENCES socios(nro_socio)
        );
        CREATE TABLE IF NOT EXISTS cuotas_proveedor (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            desc_compra_id INTEGER NOT NULL,
            nro_cuota INTEGER NOT NULL,
            fec_vencimiento TEXT,
            importe REAL NOT NULL,
            fec_pago TEXT,
            estado TEXT DEFAULT 'PENDIENTE',
            FOREIGN KEY (desc_compra_id) REFERENCES desc_compras_sno(id)
                ON DELETE CASCADE
        );
        CREATE TABLE IF NOT EXISTS cuotas_socio (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            desc_compra_id INTEGER NOT NULL,
            nro_cuota INTEGER NOT NULL,
            fec_vencimiento TEXT,
            importe REAL NOT NULL,
            fec_cobro TEXT,
            estado TEXT DEFAULT 'PENDIENTE',
            FOREIGN KEY (desc_compra_id) REFERENCES desc_compras_sno(id)
                ON DELETE CASCADE
        );
        """)
        _aplicar_migraciones(con)

        existe_admin = con.execute(
            "SELECT COUNT(*) AS c FROM usuarios").fetchone()["c"]
        if existe_admin == 0:
            salt = secrets.token_hex(16)
            pwd = hash_password("admin", salt)
            con.execute(
                "INSERT INTO usuarios (usuario, nombre, password, salt, rol,"
                " activo, creado, debe_cambiar_pwd, creado_por) "
                "VALUES (?, ?, ?, ?, ?, 1, ?, 1, 'sistema')",
                ("admin", "Administrador", pwd, salt, "SUPERADMIN",
                 datetime.now().isoformat(timespec="seconds")))


def verificar_login(usuario, password):
    """Devuelve (user_dict_o_None, motivo).
    motivos: 'ok' | 'bad_credentials' | 'inactivo' | 'bloqueado'"""
    ok = False
    user_dict = None
    motivo = "bad_credentials"
    ahora = datetime.now()

    with get_conn() as con:
        row = con.execute(
            "SELECT id, usuario, nombre, password, salt, rol, activo, "
            "debe_cambiar_pwd, intentos_fallidos, bloqueado_hasta "
            "FROM usuarios WHERE usuario = ?",
            (usuario.strip().lower(),)).fetchone()

        if row:
            bloqueado_hasta = parse_fecha_iso(row["bloqueado_hasta"])
            if row["activo"] != 1:
                motivo = "inactivo"
            elif bloqueado_hasta and ahora < bloqueado_hasta:
                motivo = "bloqueado"
            elif verify_password(password, row["salt"], row["password"]):
                ok = True
                motivo = "ok"
                user_dict = {
                    "id": row["id"], "usuario": row["usuario"],
                    "nombre": row["nombre"], "rol": row["rol"],
                    "debe_cambiar_pwd": bool(row["debe_cambiar_pwd"])
                }
                con.execute(
                    "UPDATE usuarios SET ultimo_log=?, intentos_fallidos=0,"
                    " bloqueado_hasta=NULL WHERE id=?",
                    (ahora.isoformat(timespec="seconds"), row["id"]))
                if not row["password"].startswith("pbkdf2$"):
                    nuevo_hash = hash_password(password, row["salt"])
                    con.execute("UPDATE usuarios SET password=? WHERE id=?",
                                (nuevo_hash, row["id"]))
            else:
                intentos = row["intentos_fallidos"] + 1
                if intentos >= MAX_INTENTOS_LOGIN:
                    hasta = ahora.timestamp() + MINUTOS_BLOQUEO * 60
                    hasta_iso = datetime.fromtimestamp(hasta).isoformat(
                        timespec="seconds")
                    con.execute(
                        "UPDATE usuarios SET intentos_fallidos=0, "
                        "bloqueado_hasta=? WHERE id=?",
                        (hasta_iso, row["id"]))
                    motivo = "bloqueado"
                else:
                    con.execute(
                        "UPDATE usuarios SET intentos_fallidos=? WHERE id=?",
                        (intentos, row["id"]))

        try: host = socket.gethostname()
        except Exception: host = ""
        con.execute("INSERT INTO log_accesos (usuario, fecha, exito, host) "
                    "VALUES (?, ?, ?, ?)",
                    (usuario, ahora.isoformat(timespec="seconds"),
                     1 if ok else 0, host))
    return user_dict, motivo


def get_config(clave, defecto=""):
    try:
        with get_conn() as con:
            row = con.execute("SELECT valor FROM meta WHERE clave=?",
                              (f"cfg_{clave}",)).fetchone()
        return row["valor"] if row and row["valor"] is not None else defecto
    except sqlite3.Error:
        return defecto


def set_config(clave, valor):
    with get_conn() as con:
        con.execute("INSERT INTO meta (clave, valor) VALUES (?, ?) "
                    "ON CONFLICT(clave) DO UPDATE SET valor=excluded.valor",
                    (f"cfg_{clave}", valor))


def nombre_entidad():
    return get_config("entidad_nombre", "")


def registrar_auditoria(usuario_actor, accion, detalle=""):
    with get_conn() as con:
        con.execute(
            "INSERT INTO log_auditoria (fecha, usuario_actor, accion, "
            "detalle) VALUES (?, ?, ?, ?)",
            (datetime.now().isoformat(timespec="seconds"),
             usuario_actor, accion, detalle))


def abrir_carpeta(ruta):
    try:
        if platform.system() == "Windows":
            os.startfile(ruta)
        elif platform.system() == "Darwin":
            os.system(f'open "{ruta}"')
        else:
            os.system(f'xdg-open "{ruta}"')
    except Exception:
        pass


def hacer_backup(destino_path, origen_path=None):
    os.makedirs(os.path.dirname(os.path.abspath(destino_path)) or ".",
                exist_ok=True)
    origen = sqlite3.connect(origen_path or DB_PATH)
    try:
        destino = sqlite3.connect(destino_path)
        try:
            origen.backup(destino)
        finally:
            destino.close()
    finally:
        origen.close()
    return destino_path


def backup_automatico():
    """Copia de seguridad al cerrar el programa. Conserva las ultimas
    BACKUPS_AUTO_A_CONSERVAR y borra las mas viejas. Nunca falla hacia
    afuera: si algo sale mal, no impide cerrar."""
    try:
        if not os.path.exists(DB_PATH):
            return None
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        destino = os.path.join(BACKUP_DIR, f"novamut_auto_{stamp}.db")
        hacer_backup(destino)
        autos = sorted(f for f in os.listdir(BACKUP_DIR)
                       if f.startswith("novamut_auto_") and f.endswith(".db"))
        for viejo in autos[:-BACKUPS_AUTO_A_CONSERVAR]:
            try: os.remove(os.path.join(BACKUP_DIR, viejo))
            except OSError: pass
        return destino
    except Exception:
        return None


# =====================================================================
#  WIDGETS BASE REUTILIZABLES
# =====================================================================

class Card(ctk.CTkFrame):
    """Tarjeta blanca con titulo opcional para agrupar contenido."""
    def __init__(self, master, title=None, **kwargs):
        kwargs.setdefault("fg_color", COLOR_CARD)
        kwargs.setdefault("border_color", COLOR_BORDER)
        kwargs.setdefault("border_width", 1)
        kwargs.setdefault("corner_radius", 10)
        super().__init__(master, **kwargs)
        if title:
            ctk.CTkLabel(self, text=title.upper(),
                         font=F(11, "bold"), text_color=COLOR_TEXT_MUTED,
                         anchor="w").pack(fill="x", padx=18, pady=(14, 10))


class Toast(ctk.CTkFrame):
    """Notificacion flotante inferior que se autooculta."""
    _instance = None

    def __init__(self, master):
        super().__init__(master, corner_radius=8, border_width=1)
        self.icon = ctk.CTkLabel(self, text="", font=F(16, "bold"),
                                 width=30)
        self.icon.pack(side="left", padx=(14, 8), pady=10)
        self.msg = ctk.CTkLabel(self, text="", font=F(13),
                                anchor="w", justify="left")
        self.msg.pack(side="left", padx=(0, 14), pady=10)
        self._hide_job = None

    @classmethod
    def show(cls, master, message, kind="info"):
        if cls._instance is None or not cls._instance.winfo_exists():
            cls._instance = Toast(master)
        t = cls._instance
        colors = {
            "info":    (COLOR_ACCENT,  COLOR_ACCENT_BG,  COLOR_ACCENT_TXT, "i"),
            "success": (COLOR_SUCCESS, COLOR_SUCCESS_BG, COLOR_SUCCESS_TXT, "\u2713"),
            "warning": (COLOR_WARNING, COLOR_WARNING_BG, COLOR_WARNING_TXT, "!"),
            "error":   (COLOR_DANGER,  COLOR_DANGER_BG,  COLOR_DANGER_TXT, "\u2715"),
        }
        border, bg, txt, ico = colors.get(kind, colors["info"])
        t.configure(fg_color=bg, border_color=border)
        t.icon.configure(text=ico, text_color=txt)
        t.msg.configure(text=message, text_color=txt)
        t.place(relx=0.5, rely=0.96, anchor="s")
        t.lift()
        if t._hide_job: t.after_cancel(t._hide_job)
        t._hide_job = t.after(3800, lambda: t.place_forget())


class Field(ctk.CTkFrame):
    """Campo de formulario: label arriba + entry/combo abajo."""
    def __init__(self, master, label, name=None, width=180,
                 password=False, values=None, uppercase=False,
                 placeholder=None, **kwargs):
        super().__init__(master, fg_color="transparent", **kwargs)
        self.name = name
        self.uppercase = uppercase

        ctk.CTkLabel(self, text=label, font=F(11),
                     text_color=COLOR_TEXT_MUTED,
                     anchor="w").pack(fill="x", padx=2, pady=(0, 4))

        if values is not None:
            self.var = ctk.StringVar()
            self.widget = ctk.CTkComboBox(
                self, values=values, variable=self.var, width=width,
                font=F(13), dropdown_font=F(13),
                fg_color=COLOR_CARD, border_color=COLOR_BORDER,
                button_color=COLOR_BORDER, button_hover_color=COLOR_ACCENT,
                text_color=COLOR_TEXT, height=34, corner_radius=6,
                state="readonly")
            if values: self.var.set(values[0])
        else:
            self.widget = ctk.CTkEntry(
                self, width=width, font=F(13),
                fg_color=COLOR_CARD, border_color=COLOR_BORDER,
                text_color=COLOR_TEXT, height=34, corner_radius=6,
                show="*" if password else "",
                placeholder_text=placeholder or "")
            if uppercase:
                self.widget.bind("<KeyRelease>", self._upper)
        self.widget.pack(fill="x", padx=2)

    def _upper(self, event):
        w = event.widget
        pos = w.index("insert")
        txt = w.get().upper()
        w.delete(0, "end")
        w.insert(0, txt)
        w.icursor(pos)

    def get(self):
        if isinstance(self.widget, ctk.CTkComboBox):
            return self.var.get().strip()
        return self.widget.get().strip()

    def set(self, value):
        if isinstance(self.widget, ctk.CTkComboBox):
            self.var.set(str(value) if value is not None else "")
        else:
            state = self.widget.cget("state")
            self.widget.configure(state="normal")
            self.widget.delete(0, "end")
            if value is not None: self.widget.insert(0, str(value))
            self.widget.configure(state=state)

    def set_state(self, state):
        try: self.widget.configure(state=state)
        except Exception: pass

    def bind_key(self, key, cb):
        self.widget.bind(key, cb)

    def focus(self):
        self.widget.focus_set()


class PrimaryButton(ctk.CTkButton):
    def __init__(self, master, text, icon=None, command=None, **kwargs):
        display = f"{icon}  {text}" if icon else text
        kwargs.setdefault("height", 38)
        kwargs.setdefault("corner_radius", 6)
        super().__init__(
            master, text=display, command=command,
            fg_color=COLOR_SUCCESS, hover_color=COLOR_SUCCESS_HOVER,
            text_color="white", font=F(13, "bold"), **kwargs)


class AccentButton(ctk.CTkButton):
    def __init__(self, master, text, icon=None, command=None, **kwargs):
        display = f"{icon}  {text}" if icon else text
        kwargs.setdefault("height", 38)
        kwargs.setdefault("corner_radius", 6)
        super().__init__(
            master, text=display, command=command,
            fg_color=COLOR_ACCENT, hover_color=COLOR_ACCENT_HOVER,
            text_color="white", font=F(13, "bold"), **kwargs)


class SecondaryButton(ctk.CTkButton):
    def __init__(self, master, text, icon=None, command=None, **kwargs):
        display = f"{icon}  {text}" if icon else text
        kwargs.setdefault("height", 38)
        kwargs.setdefault("corner_radius", 6)
        super().__init__(
            master, text=display, command=command,
            fg_color=COLOR_CARD, hover_color="#f3f4f6",
            text_color=COLOR_TEXT, border_color=COLOR_BORDER_STRONG,
            border_width=1, font=F(13), **kwargs)


class DangerButton(ctk.CTkButton):
    def __init__(self, master, text, icon=None, command=None, **kwargs):
        display = f"{icon}  {text}" if icon else text
        kwargs.setdefault("height", 38)
        kwargs.setdefault("corner_radius", 6)
        super().__init__(
            master, text=display, command=command,
            fg_color=COLOR_CARD, hover_color=COLOR_DANGER_BG,
            text_color=COLOR_DANGER_TXT, border_color=COLOR_DANGER,
            border_width=1, font=F(13), **kwargs)


class Badge(ctk.CTkLabel):
    """Pequeño chip de estado con color."""
    KINDS = {
        "success": (COLOR_SUCCESS_BG, COLOR_SUCCESS_TXT),
        "warning": (COLOR_WARNING_BG, COLOR_WARNING_TXT),
        "danger":  (COLOR_DANGER_BG,  COLOR_DANGER_TXT),
        "info":    (COLOR_ACCENT_BG,  COLOR_ACCENT_TXT),
        "muted":   ("#f3f4f6",        COLOR_TEXT_MUTED),
    }
    def __init__(self, master, text, kind="info", **kwargs):
        bg, fg = self.KINDS.get(kind, self.KINDS["info"])
        super().__init__(master, text=text.upper() if text else "",
                         font=F(10, "bold"),
                         fg_color=bg, text_color=fg,
                         corner_radius=10, padx=10, pady=3, **kwargs)


class DataTable(ctk.CTkFrame):
    """Tabla scrollable con encabezado y filas clickeables."""
    def __init__(self, master, columns, on_row_click=None,
                 row_height=36, **kwargs):
        super().__init__(master, fg_color="transparent", **kwargs)
        self.columns = columns  # [(width, "titulo", "key")]
        self.on_row_click = on_row_click
        self._rows = []

        # Encabezado
        hdr = ctk.CTkFrame(self, fg_color="#f3f4f6",
                           corner_radius=6, height=38)
        hdr.pack(fill="x", pady=(0, 0))
        hdr.pack_propagate(False)
        for w, title, _ in columns:
            ctk.CTkLabel(hdr, text=title.upper(), font=F(10, "bold"),
                         text_color=COLOR_TEXT_MUTED, width=w,
                         anchor="w").pack(side="left", padx=8)

        # Contenedor de filas
        self.body = ctk.CTkScrollableFrame(self, fg_color=COLOR_CARD,
                                           corner_radius=6)
        self.body.pack(fill="both", expand=True)
        self.row_height = row_height

    def clear(self):
        for r in self._rows:
            r.destroy()
        self._rows = []

    def add_row(self, data, badges=None, key=None):
        """data: dict {col_key: valor}. badges: dict {col_key: kind}."""
        idx = len(self._rows)
        bg = COLOR_CARD if idx % 2 == 0 else COLOR_ZEBRA
        row = ctk.CTkFrame(self.body, fg_color=bg, corner_radius=0,
                           height=self.row_height)
        row.pack(fill="x")
        row.pack_propagate(False)

        for w, _, colkey in self.columns:
            val = data.get(colkey, "")
            if badges and colkey in badges:
                b = Badge(row, str(val), badges[colkey])
                b.pack(side="left", padx=8, pady=6)
            else:
                lbl = ctk.CTkLabel(row, text=str(val) if val is not None else "",
                                    font=F(12), text_color=COLOR_TEXT,
                                    width=w, anchor="w")
                lbl.pack(side="left", padx=8)

        if self.on_row_click:
            def hdlr(_=None, k=key):
                self.on_row_click(k)
            for widget in [row] + list(row.winfo_children()):
                widget.bind("<Button-1>", hdlr)
                widget.bind("<Enter>",
                            lambda e, r=row: r.configure(fg_color=COLOR_ACCENT_BG))
                widget.bind("<Leave>",
                            lambda e, r=row, b=bg: r.configure(fg_color=b))
        self._rows.append(row)


class ConfirmDialog:
    """Wrapper simple sobre messagebox para respetar el look moderno."""
    @staticmethod
    def yes_no(title, message):
        return messagebox.askyesno(title, message)

    @staticmethod
    def info(title, message):
        messagebox.showinfo(title, message)

    @staticmethod
    def error(title, message):
        messagebox.showerror(title, message)


# =====================================================================
#  APP PRINCIPAL - una sola ventana con sidebar + contenido
# =====================================================================
class NovaMutApp(ctk.CTk):

    # (label, icono, key, permiso)  permiso: None | "operar" | "admin"
    MENU_ITEMS = [
        ("Socios",          "\u25CE", "socios",        None),
        ("Proveedores",     "\u25A0", "proveedores",   None),
        ("Desc/Compras",    "\u25E6", "desc_compras",  None),
        ("Cuotas",          "\u25B6", "cuotas",        None),
        ("Liquidacion",     "\u2630", "liquidacion",   None),
        ("Estado de cuenta","\u2261", "estado_cta",    None),
        ("Cuotas vencidas", "\u2691", "cta_vencidas",  None),
        ("Padron INAES",    "\u2691", "inaes",         None),
        ("Credenciales",    "\u25A3", "credencial",    None),
        ("---",             "",        None,            None),
        ("Usuarios",        "\u265F", "usuarios",      "admin"),
        ("Auditoria",       "\u2632", "auditoria",     "admin"),
        ("Configuracion",   "\u2699", "configuracion", "admin"),
        ("Backup BD",       "\u21BA", "backup",        "operar"),
        ("Cambiar clave",   "\u2318", "pwd",           None),
        ("Programadores",   "\u2139", "programadores", None),
    ]
    NIVEL_PERMISO = {None: 0, "operar": NIVEL_OPERAR, "admin": NIVEL_ADMIN}

    def __init__(self):
        super().__init__()
        self.title(APP_NOMBRE)
        self.geometry("1280x780")
        self.minsize(1180, 720)
        self.configure(fg_color=COLOR_BG)
        self._poner_icono(self)

        self.usuario = None
        self._panel_actual = None
        self._sidebar_buttons = {}
        self._active_key = None

        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self._build_sidebar()
        self._build_content_area()
        self.actualizar_entidad()
        self.protocol("WM_DELETE_WINDOW", self._al_cerrar)

        self.show_login()

    # ---------------------------------------------------------------
    @staticmethod
    def _poner_icono(ventana):
        """Pone el icono de NovaMut. customtkinter pone el suyo a los
        ~200 ms, por eso se vuelve a aplicar despues."""
        ico = _recurso(ICONO)
        if not ico or platform.system() != "Windows":
            return
        def aplicar():
            try: ventana.iconbitmap(ico)
            except Exception: pass
        aplicar()
        try: ventana.after(300, aplicar)
        except Exception: pass

    def _al_cerrar(self):
        backup_automatico()
        self.destroy()

    def puede(self, nivel, que="hacer esto"):
        """True si el usuario actual tiene el nivel pedido; si no, avisa."""
        if tiene_nivel(self.usuario, nivel):
            return True
        rol = self.usuario["rol"] if self.usuario else "-"
        self.toast(f"Tu rol ({rol}) no permite {que}.", "error")
        return False

    def actualizar_entidad(self):
        ent = nombre_entidad()
        self.title(f"{APP_NOMBRE} - {ent}" if ent
                   else f"{APP_NOMBRE} - Sistema de Gestion Mutual")
        self.lbl_entidad.configure(text=ent or "Sistema de Gestion Mutual")

    # ---------------------------------------------------------------
    def _build_sidebar(self):
        self.sidebar = ctk.CTkFrame(self, fg_color=COLOR_SIDEBAR,
                                    corner_radius=0, width=240)
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)
        self.sidebar.grid_rowconfigure(2, weight=1)

        # Logo
        logo = ctk.CTkFrame(self.sidebar, fg_color="transparent")
        logo.grid(row=0, column=0, sticky="ew", padx=20, pady=(16, 4))
        ctk.CTkLabel(logo, text=APP_NOMBRE,
                     font=F(20, "bold"),
                     text_color="white").pack(anchor="w")
        self.lbl_entidad = ctk.CTkLabel(logo, text="", font=F(11),
                                        text_color="#94a3b8", anchor="w",
                                        justify="left", wraplength=200)
        self.lbl_entidad.pack(anchor="w")

        sep = ctk.CTkFrame(self.sidebar, fg_color=COLOR_SIDEBAR_HOVER,
                          height=1)
        sep.grid(row=1, column=0, sticky="ew", padx=20, pady=(8, 6))

        # Contenedor scrollable del menu (por si la pantalla es chica)
        self.menu_frame = ctk.CTkScrollableFrame(
            self.sidebar, fg_color="transparent",
            scrollbar_button_color=COLOR_SIDEBAR,
            scrollbar_button_hover_color="#475569")
        self.menu_frame.grid(row=2, column=0, sticky="nsew", padx=4)

        self._menu_seps = []
        for label, icon, key, _ in self.MENU_ITEMS:
            if label == "---":
                s = ctk.CTkFrame(self.menu_frame,
                                fg_color=COLOR_SIDEBAR_HOVER, height=1)
                s.pack(fill="x", padx=16, pady=6)
                self._menu_seps.append(s)
                continue
            btn = ctk.CTkButton(
                self.menu_frame, text=f"  {icon}   {label}",
                anchor="w", font=F(13),
                fg_color="transparent",
                hover_color=COLOR_SIDEBAR_HOVER,
                text_color=COLOR_SIDEBAR_TEXT,
                corner_radius=6, height=31,
                command=lambda k=key: self._on_sidebar_click(k))
            btn.pack(fill="x", padx=4, pady=0)
            self._sidebar_buttons[key] = btn

        # Zona usuario abajo (grid rows 3, 4)
        self._sep2 = ctk.CTkFrame(self.sidebar, fg_color=COLOR_SIDEBAR_HOVER,
                                  height=1)
        self.user_box = ctk.CTkFrame(self.sidebar, fg_color="transparent")

        self.user_name_lbl = ctk.CTkLabel(self.user_box, text="",
                                          font=F(13, "bold"),
                                          text_color="white", anchor="w")
        self.user_name_lbl.pack(anchor="w")
        self.user_rol_lbl = ctk.CTkLabel(self.user_box, text="",
                                         font=F(11),
                                         text_color="#94a3b8", anchor="w")
        self.user_rol_lbl.pack(anchor="w")
        ctk.CTkButton(
            self.user_box, text="\u21B6  Cerrar sesion",
            font=F(12), anchor="w",
            fg_color="transparent", hover_color=COLOR_SIDEBAR_HOVER,
            text_color="#94a3b8", corner_radius=6, height=28,
            command=self._logout).pack(fill="x", pady=(4, 0))

        self._set_sidebar_visible(False)

    def _set_sidebar_visible(self, visible):
        if visible:
            self.sidebar.grid(row=0, column=0, sticky="nsew")
            self._sep2.grid(row=3, column=0, sticky="ew", padx=20,
                            pady=(8, 6))
            self.user_box.grid(row=4, column=0, sticky="ew", padx=20,
                               pady=(0, 12))
        else:
            self.sidebar.grid_forget()
            self._sep2.grid_forget()
            self.user_box.grid_forget()

        if hasattr(self, "topbar"):
            if visible:
                self.topbar.grid(row=0, column=0, sticky="ew")
                self._topbar_sep.place(relx=0, rely=0, y=64, relwidth=1)
            else:
                self.topbar.grid_forget()
                self._topbar_sep.place_forget()

        # Mostrar solo los items que el rol permite (se re-empaquetan en
        # orden para no desordenar el menu)
        for w in list(self._sidebar_buttons.values()) + self._menu_seps:
            w.pack_forget()
        if not visible:
            return
        sep_iter = iter(self._menu_seps)
        for label, icon, key, permiso in self.MENU_ITEMS:
            if label == "---":
                next(sep_iter).pack(fill="x", padx=16, pady=6)
                continue
            if tiene_nivel(self.usuario, self.NIVEL_PERMISO[permiso]):
                self._sidebar_buttons[key].pack(fill="x", padx=4, pady=0)

    def _mark_active(self, key):
        for k, btn in self._sidebar_buttons.items():
            if k == key:
                btn.configure(fg_color=COLOR_SIDEBAR_SEL, text_color="white")
            else:
                btn.configure(fg_color="transparent",
                              text_color=COLOR_SIDEBAR_TEXT)
        self._active_key = key

    def _on_sidebar_click(self, key):
        if not self.usuario: return
        panels = {
            "socios":        (PanelCargaSocios,       "Socios"),
            "proveedores":   (PanelProveedores,       "Proveedores"),
            "desc_compras":  (PanelDescCompras,       "Desc/Compras"),
            "cuotas":        (PanelCuotas,            "Cuotas"),
            "liquidacion":   (PanelLiquidacion,       "Liquidacion"),
            "consultas":     (PanelConsultas,         "Consultas"),
            "estado_cta":    (PanelEstadoCuenta,      "Estado de cuenta"),
            "cta_vencidas":  (PanelCuotasVencidas,    "Cuotas vencidas"),
            "inaes":         (PanelInaesRes756,       "Padron INAES"),
            "credencial":    (PanelCredencialSocio,   "Credenciales"),
            "usuarios":      (PanelGestionUsuarios,   "Gestion de usuarios"),
            "auditoria":     (PanelAuditoria,         "Auditoria"),
            "configuracion": (PanelConfiguracion,     "Configuracion"),
            "backup":        (PanelBackup,            "Backup"),
            "pwd":           (PanelCambiarPassword,   "Cambiar contrasena"),
            "programadores": (PanelProgramadores,     "Programadores"),
        }
        if key not in panels: return
        permiso = next((p for _, _, k, p in self.MENU_ITEMS if k == key),
                       None)
        if not self.puede(self.NIVEL_PERMISO[permiso], "entrar ahi"):
            return
        cls, titulo = panels[key]
        self._mark_active(key)
        self.show_panel(cls, titulo=titulo)

    # ---------------------------------------------------------------
    def _build_content_area(self):
        self.content_wrapper = ctk.CTkFrame(self, fg_color=COLOR_BG,
                                            corner_radius=0)
        self.content_wrapper.grid(row=0, column=1, sticky="nsew")
        self.content_wrapper.grid_columnconfigure(0, weight=1)
        self.content_wrapper.grid_rowconfigure(1, weight=1)

        # Topbar
        self.topbar = ctk.CTkFrame(self.content_wrapper, fg_color=COLOR_CARD,
                                    corner_radius=0, height=64)
        self.topbar.grid(row=0, column=0, sticky="ew")
        self.topbar.grid_propagate(False)

        self._topbar_sep = ctk.CTkFrame(self.content_wrapper,
                                        fg_color=COLOR_BORDER,
                                        height=1, corner_radius=0)
        self._topbar_sep.place(relx=0, rely=0, y=64, relwidth=1)

        left = ctk.CTkFrame(self.topbar, fg_color="transparent")
        left.pack(side="left", padx=24, pady=10, fill="y")
        self.lbl_breadcrumb = ctk.CTkLabel(left, text="",
                                           font=F(11),
                                           text_color=COLOR_TEXT_MUTED,
                                           anchor="w")
        self.lbl_breadcrumb.pack(anchor="w")
        self.lbl_title = ctk.CTkLabel(left, text="Bienvenido",
                                      font=F(18, "bold"),
                                      text_color=COLOR_TEXT, anchor="w")
        self.lbl_title.pack(anchor="w")

        right = ctk.CTkFrame(self.topbar, fg_color="transparent")
        right.pack(side="right", padx=24, pady=10, fill="y")
        self.lbl_fecha = ctk.CTkLabel(right, text="",
                                      font=F(12),
                                      text_color=COLOR_TEXT_MUTED)
        self.lbl_fecha.pack(side="left", padx=(0, 12))
        self.lbl_estado = Badge(right, "", "info")

        # Contenido
        self.content = ctk.CTkScrollableFrame(self.content_wrapper,
                                              fg_color=COLOR_BG,
                                              corner_radius=0)
        self.content.grid(row=1, column=0, sticky="nsew")
        self.content.grid_columnconfigure(0, weight=1)

        self._tick()

    def _tick(self):
        self.lbl_fecha.configure(text=datetime.now().strftime("%d/%m/%Y  %H:%M"))
        self.after(60000, self._tick)

    def set_breadcrumb(self, crumb, titulo):
        self.lbl_breadcrumb.configure(text=crumb)
        self.lbl_title.configure(text=titulo)

    def set_badge(self, texto, kind="success"):
        if not texto:
            self.lbl_estado.pack_forget()
            return
        bg, fg = Badge.KINDS.get(kind, Badge.KINDS["info"])
        self.lbl_estado.configure(text=texto.upper(),
                                  fg_color=bg, text_color=fg)
        self.lbl_estado.pack(side="left")

    def show_panel(self, panel_cls, **kwargs):
        if self._panel_actual is not None:
            self._panel_actual.destroy()
            self._panel_actual = None
        for w in self.content.winfo_children():
            w.destroy()
        self._panel_actual = panel_cls(self.content, self, **kwargs)
        self._panel_actual.pack(fill="both", expand=True, padx=24, pady=20)

    def show_terminos(self):
        self._set_sidebar_visible(False)
        self.set_breadcrumb("", "Terminos y condiciones")
        self.set_badge("")
        self._mark_active(None)
        self.show_panel(PanelTerminos)

    def show_login(self):
        self._set_sidebar_visible(False)
        self.set_breadcrumb("", "Iniciar sesion")
        self.set_badge("")
        self._mark_active(None)
        self.show_panel(PanelLogin)

    def _logout(self):
        if ConfirmDialog.yes_no("Cerrar sesion",
                                "Estas seguro que queres cerrar sesion?"):
            self.usuario = None
            self.show_login()

    def on_login_ok(self, usuario):
        self.usuario = usuario
        # Cada usuario acepta los terminos una vez (y de nuevo si cambian)
        with get_conn() as con:
            row = con.execute("SELECT terminos_version FROM usuarios "
                              "WHERE id=?", (usuario["id"],)).fetchone()
        if not row or row["terminos_version"] != TERMINOS_VERSION:
            self.show_terminos()
            return
        self._entrar()

    def terminos_aceptados(self):
        with get_conn() as con:
            con.execute("UPDATE usuarios SET terminos_version=?, "
                        "terminos_fecha=? WHERE id=?",
                        (TERMINOS_VERSION,
                         datetime.now().isoformat(timespec="seconds"),
                         self.usuario["id"]))
        registrar_auditoria(self.usuario["usuario"], "ACEPTA_TERMINOS",
                            f"version {TERMINOS_VERSION}")
        self._entrar()

    def terminos_rechazados(self):
        if self.usuario:
            registrar_auditoria(self.usuario["usuario"], "RECHAZA_TERMINOS",
                                f"version {TERMINOS_VERSION}")
        self._al_cerrar()

    def _entrar(self):
        usuario = self.usuario
        self._set_sidebar_visible(True)
        self.user_name_lbl.configure(
            text=usuario["nombre"] or usuario["usuario"].upper())
        self.user_rol_lbl.configure(text=f"Rol: {usuario['rol']}")

        # Si tiene que cambiar clave, forzar el panel de cambio
        if usuario.get("debe_cambiar_pwd"):
            ConfirmDialog.info("Cambio de clave requerido",
                "Por seguridad debes cambiar tu contrasena.")
            self._mark_active("pwd")
            self.show_panel(PanelCambiarPassword, titulo="Cambiar contrasena",
                            forzado=True)
        else:
            self._on_sidebar_click("socios")

    def toast(self, msg, kind="info"):
        Toast.show(self.content_wrapper, msg, kind)


SigemutApp = NovaMutApp   # nombre anterior


# =====================================================================
#  PANEL: LOGIN
# =====================================================================
class PanelLogin(ctk.CTkFrame):
    def __init__(self, master, app, **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.intentos = 0

        # Espaciador arriba para empujar el contenido hacia el centro
        ctk.CTkFrame(self, fg_color="transparent", height=80).pack()

        # Contenedor centrado
        wrap = ctk.CTkFrame(self, fg_color="transparent")
        wrap.pack()

        # Tarjeta principal - crece con el contenido, ancho controlado
        # por padding interno del contenido
        card = ctk.CTkFrame(wrap, fg_color=COLOR_CARD,
                            border_color=COLOR_BORDER, border_width=1,
                            corner_radius=12)
        card.pack(padx=20, pady=20)

        # Icono/Logo
        logo_box = ctk.CTkFrame(card, fg_color=COLOR_ACCENT,
                                corner_radius=16, width=64, height=64)
        logo_box.pack(pady=(36, 12), padx=60)
        logo_box.pack_propagate(False)
        ctk.CTkLabel(logo_box, text="N", font=F(34, "bold"),
                     text_color="white").pack(expand=True)

        # Titulo y subtitulo
        ctk.CTkLabel(card, text=APP_NOMBRE, font=F(26, "bold"),
                     text_color=COLOR_TEXT).pack()
        ctk.CTkLabel(card, text=nombre_entidad() or
                     "Sistema de Gestion Mutual",
                     font=F(13), text_color=COLOR_TEXT_MUTED,
                     wraplength=340).pack(pady=(0, 24))

        # Formulario
        self.f_user = Field(card, "Usuario", width=340)
        self.f_user.pack(padx=40, pady=(0, 14))
        self.f_pass = Field(card, "Contrasena", password=True, width=340)
        self.f_pass.pack(padx=40, pady=(0, 4))

        self.f_user.bind_key("<Return>", lambda e: self.f_pass.focus())
        self.f_pass.bind_key("<Return>", lambda e: self._login())

        # Mensaje de error (arriba del boton)
        self.msg = ctk.CTkLabel(card, text="", font=F(12),
                                text_color=COLOR_DANGER, wraplength=340)
        self.msg.pack(padx=40, pady=(4, 8))

        # Boton
        self.btn = AccentButton(card, "Ingresar",
                                command=self._login,
                                width=340, height=44)
        self.btn.pack(padx=40, pady=(8, 8))

        # Footer
        ctk.CTkLabel(card, text=f"Version {APP_VERSION}",
                     font=F(10), text_color=COLOR_TEXT_LIGHT).pack(
                     pady=(4, 28))

        self.f_user.focus()

    def _login(self):
        u = self.f_user.get()
        p = self.f_pass.get()
        if not u or not p:
            self.msg.configure(text="Complete usuario y contrasena.")
            return
        user, motivo = verificar_login(u, p)
        if motivo == "ok":
            self.app.on_login_ok(user)
            self.app.toast(f"Bienvenido, {user['nombre']}", "success")
        elif motivo == "bloqueado":
            self.msg.configure(
                text=f"Cuenta bloqueada temporalmente por "
                     f"{MINUTOS_BLOQUEO} minutos.")
            self.f_pass.set("")
        elif motivo == "inactivo":
            self.msg.configure(
                text="Cuenta desactivada. Contacte al administrador.")
            self.f_pass.set("")
        else:
            self.intentos += 1
            self.msg.configure(
                text=f"Credenciales incorrectas. Intento {self.intentos}.")
            self.f_pass.set("")
            self.f_pass.focus()


# =====================================================================
#  PANEL: CARGA DE SOCIOS (ABM completo)
# =====================================================================
FECHAS_SOCIO = ("fec_nac", "fec_ing", "fec_baj", "fec_egr")


def buscar_socios_por_documento(con, digitos, exacto=False):
    """Socios cuyo CUIL contiene esos digitos (sirve para DNI y CUIL)."""
    expr = ("REPLACE(REPLACE(REPLACE(COALESCE(cuil,''),'-',''),' ',''),"
            "'.','')")
    if exacto:
        return con.execute(f"SELECT nro_socio, nombre FROM socios "
                           f"WHERE {expr} = ?", (digitos,)).fetchall()
    return con.execute(f"SELECT nro_socio, nombre FROM socios "
                       f"WHERE {expr} LIKE ? ORDER BY nro_socio",
                       (f"%{digitos}%",)).fetchall()


def describir_cambios(antes, despues, max_campos=8):
    """Texto corto con los campos que cambiaron: 'nombre: A -> B; ...'"""
    if not antes:
        return ""
    cambios = []
    for k, v in despues.items():
        a = antes.get(k)
        if str(a if a is not None else "") != str(v if v is not None else ""):
            cambios.append(f"{k}: {a if a not in (None, '') else '-'} -> "
                           f"{v if v not in (None, '') else '-'}")
    if len(cambios) > max_campos:
        cambios = cambios[:max_campos] + [f"(+{len(cambios)-max_campos})"]
    return "; ".join(cambios) or "sin cambios"


def deshabilitar_sin_nivel(app, botones, nivel=NIVEL_OPERAR):
    """Deshabilita botones de edicion si el rol no alcanza."""
    if not tiene_nivel(app.usuario, nivel):
        for b in botones:
            try: b.configure(state="disabled")
            except Exception: pass


class PanelCargaSocios(ctk.CTkFrame):
    OPCIONES_CIVIL  = ["", "SOLTERO", "CASADO", "DIVORCIADO", "VIUDO",
                       "CONCUBINATO", "SEPARADO"]
    OPCIONES_SEXO   = ["", "M", "F", "O"]
    OPCIONES_SN     = ["N", "S"]
    OPCIONES_RIESGO = ["B", "M", "A"]
    OPCIONES_CATEG  = ["", "TITULAR", "ADHERENTE", "FAMILIAR",
                       "JUBILADO", "HONORARIO"]
    OPCIONES_TDOC   = ["", "DNI", "LE", "LC", "CI", "PASAPORTE"]

    def __init__(self, master, app, titulo="Socios", nro_inicial=None,
                 **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.modo = "CONSULTA"
        self.socio_actual = None
        self.fields = {}

        app.set_breadcrumb("Actualizacion de archivos", "Carga de socios")
        self._actualizar_badge_modo()

        self._build_toolbar()
        self._build_form()
        self._build_action_bar()

        self._set_modo("CONSULTA")

        if nro_inicial:
            self.e_buscar.insert(0, str(nro_inicial))
            self.after(50, self._buscar)

    def _build_toolbar(self):
        tb = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                          border_color=COLOR_BORDER, border_width=1,
                          corner_radius=10, height=64)
        tb.pack(fill="x", pady=(0, 12))
        tb.pack_propagate(False)

        inner = ctk.CTkFrame(tb, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=12)

        ctk.CTkLabel(inner, text="Nro., DNI o CUIL", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 8))
        self.e_buscar = ctk.CTkEntry(
            inner, width=170, font=F(14, "bold"),
            fg_color=COLOR_CARD, border_color=COLOR_BORDER,
            text_color=COLOR_TEXT, height=38, corner_radius=6,
            placeholder_text="1001")
        self.e_buscar.pack(side="left", padx=(0, 8))
        self.e_buscar.bind("<Return>", lambda e: self._buscar())

        SecondaryButton(inner, "Buscar", "\u2315",
                        command=self._buscar, width=120).pack(side="left",
                                                              padx=4)
        SecondaryButton(inner, "Listar todos", "\u2261",
                        command=self._listar, width=140).pack(side="left",
                                                              padx=4)

    def _build_form(self):
        # --- Datos personales ---
        card1 = Card(self, title="Datos personales")
        card1.pack(fill="x", pady=6)
        grid1 = ctk.CTkFrame(card1, fg_color="transparent")
        grid1.pack(fill="x", padx=18, pady=(0, 16))
        grid1.grid_columnconfigure((0, 1, 2, 3), weight=1)

        self._add_field(grid1, "nro_socio",   "Nro. socio", 0, 0)
        self._add_field(grid1, "nombre",      "Nombre completo", 0, 1,
                        cspan=3, uppercase=True)
        self._add_field(grid1, "tipo_doc",    "Tipo doc.", 1, 0,
                        values=self.OPCIONES_TDOC)
        self._add_field(grid1, "cuil",        "CUIL", 1, 1)
        self._add_field(grid1, "fec_nac",     "Fecha nac. (dd/mm/aaaa)",
                        1, 2)
        self._add_field(grid1, "sexo",        "Sexo", 1, 3,
                        values=self.OPCIONES_SEXO)
        self._add_field(grid1, "estado_civil","Estado civil", 2, 0,
                        values=self.OPCIONES_CIVIL)
        self._add_field(grid1, "extranjero",  "Extranjero", 2, 1,
                        values=self.OPCIONES_SN)
        self._add_field(grid1, "es_pep",      "Es PEP", 2, 2,
                        values=self.OPCIONES_SN)
        self._add_field(grid1, "riesgo",      "Riesgo (A/M/B)", 2, 3,
                        values=self.OPCIONES_RIESGO)

        # --- Contacto ---
        card2 = Card(self, title="Contacto")
        card2.pack(fill="x", pady=6)
        g2 = ctk.CTkFrame(card2, fg_color="transparent")
        g2.pack(fill="x", padx=18, pady=(0, 16))
        g2.grid_columnconfigure((0, 1, 2, 3), weight=1)
        self._add_field(g2, "direccion", "Direccion", 0, 0, cspan=3,
                        uppercase=True)
        self._add_field(g2, "cp",        "CP", 0, 3)
        self._add_field(g2, "localidad", "Localidad", 1, 0, cspan=2,
                        uppercase=True)
        self._add_field(g2, "telefono",  "Telefono", 1, 2)
        self._add_field(g2, "mail",      "Email", 1, 3)

        # --- Datos de la mutual ---
        card3 = Card(self, title="Datos de la mutual")
        card3.pack(fill="x", pady=6)
        g3 = ctk.CTkFrame(card3, fg_color="transparent")
        g3.pack(fill="x", padx=18, pady=(0, 16))
        g3.grid_columnconfigure((0, 1, 2, 3), weight=1)
        self._add_field(g3, "fec_ing",    "Fecha ingreso", 0, 0)
        self._add_field(g3, "fec_baj",    "Fecha baja", 0, 1)
        self._add_field(g3, "fec_egr",    "Fecha egreso", 0, 2)
        self._add_field(g3, "categoria",  "Categoria", 0, 3,
                        values=self.OPCIONES_CATEG)
        self._add_field(g3, "credit_max", "Credito maximo", 1, 0)
        self._add_field(g3, "cre_max_mes","Cred. max. mensual", 1, 1)
        self._add_field(g3, "tope_emp",   "Tope empleador", 1, 2)
        self._add_field(g3, "cbu",        "CBU", 1, 3)
        self._add_field(g3, "liq_mot",    "Motivo de liquidacion",
                        2, 0, cspan=4, uppercase=True)

        # --- Servicios optativos ---
        card4 = Card(self, title="Servicios optativos")
        card4.pack(fill="x", pady=6)
        g4 = ctk.CTkFrame(card4, fg_color="transparent")
        g4.pack(fill="x", padx=18, pady=(0, 16))
        g4.grid_columnconfigure((0, 1, 2), weight=1)
        self._add_field(g4, "servicio1", "Servicio 1", 0, 0, uppercase=True)
        self._add_field(g4, "servicio2", "Servicio 2", 0, 1, uppercase=True)
        self._add_field(g4, "servicio3", "Servicio 3", 0, 2, uppercase=True)

    def _add_field(self, parent, name, label, row, col, cspan=1,
                   values=None, uppercase=False):
        f = Field(parent, label, name=name,
                  values=values, uppercase=uppercase)
        f.grid(row=row, column=col, columnspan=cspan,
               sticky="ew", padx=6, pady=6)
        self.fields[name] = f

    def _build_action_bar(self):
        bar = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                           border_color=COLOR_BORDER, border_width=1,
                           corner_radius=10, height=72)
        bar.pack(fill="x", pady=(12, 8))
        bar.pack_propagate(False)

        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=16)

        left = ctk.CTkFrame(inner, fg_color="transparent")
        left.pack(side="left")
        self._btns_edicion = [
            SecondaryButton(left, "Nuevo", "+", command=self._nuevo,
                            width=110),
            SecondaryButton(left, "Modificar", "\u270E",
                            command=self._modificar, width=130),
            DangerButton(left, "Dar de baja", "\u2715",
                         command=self._dar_baja, width=150),
        ]
        for b in self._btns_edicion:
            b.pack(side="left", padx=4)
        SecondaryButton(left, "Credencial", "\u25A3",
                        command=self._credencial,
                        width=140).pack(side="left", padx=4)
        deshabilitar_sin_nivel(self.app, self._btns_edicion)

        right = ctk.CTkFrame(inner, fg_color="transparent")
        right.pack(side="right")
        self.btn_guardar = PrimaryButton(
            right, "Guardar", "\u2713",
            command=self._guardar, width=160)
        self.btn_guardar.pack(side="right", padx=4)

    def _actualizar_badge_modo(self):
        badges = {
            "CONSULTA":     ("Consulta",     "info"),
            "ALTA":         ("Alta",         "success"),
            "MODIFICACION": ("Modificacion", "warning"),
        }
        txt, kind = badges.get(self.modo, ("", "info"))
        self.app.set_badge(txt, kind)

    def _set_modo(self, modo):
        self.modo = modo
        self._actualizar_badge_modo()
        editable = modo in ("ALTA", "MODIFICACION")
        for name, f in self.fields.items():
            if name == "nro_socio":
                # el numero lo asigna el sistema, nunca se escribe a mano
                f.set_state("disabled")
                continue
            f.set_state("normal" if editable else "disabled")
        self.btn_guardar.configure(
            state="normal" if editable else "disabled",
            fg_color=COLOR_SUCCESS if editable else "#94a3b8")

    def _limpiar(self, keep_nro=False):
        for name, f in self.fields.items():
            if keep_nro and name == "nro_socio": continue
            f.set("")
        self.fields["extranjero"].set("N")
        self.fields["es_pep"].set("N")
        self.fields["riesgo"].set("B")

    def _get(self, name):
        return self.fields[name].get()

    def _buscar(self):
        txt = self.e_buscar.get().strip() or self._get("nro_socio")
        dig = solo_digitos(txt)
        if not dig:
            # texto: buscar por nombre en el listado
            if txt:
                VentanaListaSocios(self.app, callback=self._cargar_socio,
                                   consulta=txt)
            else:
                self.app.toast("Ingresa un numero, DNI o CUIL.", "error")
            return
        if len(dig) >= 7:
            # Parece DNI o CUIL
            with get_conn() as con:
                rows = buscar_socios_por_documento(con, dig)
            if len(rows) == 1:
                self._cargar_socio(rows[0]["nro_socio"]); return
            if len(rows) > 1:
                VentanaListaSocios(self.app, callback=self._cargar_socio,
                                   consulta=dig)
                return
            if len(dig) > 7:
                self.app.toast(f"No hay socios con DNI/CUIL {txt}.",
                               "warning")
                return
        nro = dig
        with get_conn() as con:
            row = con.execute("SELECT * FROM socios WHERE nro_socio=?",
                              (int(nro),)).fetchone()
        if row:
            self.socio_actual = dict(row)
            self.fields["nro_socio"].set(nro)
            for k, v in self.socio_actual.items():
                if k in self.fields:
                    self.fields[k].set(fecha_ui(v) if k in FECHAS_SOCIO
                                       else v)
            self._set_modo("CONSULTA")
            self.app.toast(f"Socio {nro} encontrado.", "success")
        else:
            self._limpiar()
            self.socio_actual = None
            self._set_modo("CONSULTA")
            self.app.toast(f"Socio {nro} no existe. Para cargar uno nuevo "
                           f"usa Nuevo (el numero es automatico).",
                           "warning")

    def _nuevo(self):
        if not self.app.puede(NIVEL_OPERAR, "dar de alta socios"): return
        self._limpiar()
        self.socio_actual = None
        self._set_modo("ALTA")
        with get_conn() as con:
            prox = proximo_nro_socio(con)
        self.fields["nro_socio"].set(prox)
        self.e_buscar.delete(0, "end")
        self.fields["fec_ing"].set(hoy_ui())
        self.fields["nombre"].focus()
        self.app.toast(f"Alta del socio {prox}. Completa los datos y "
                       f"guarda.", "info")

    def _modificar(self):
        if not self.app.puede(NIVEL_OPERAR, "modificar socios"): return
        if not self.socio_actual:
            self.app.toast("Primero busca un socio existente.", "warning")
            return
        self._set_modo("MODIFICACION")
        self.fields["nombre"].focus()
        self.app.toast("Modo modificacion.", "info")

    def _dar_baja(self):
        if not self.app.puede(NIVEL_OPERAR, "dar de baja socios"): return
        if not self.socio_actual:
            self.app.toast("Primero busca un socio.", "warning"); return
        if self.socio_actual.get("fec_baj"):
            self.app.toast("El socio ya esta dado de baja.", "warning")
            return
        if not ConfirmDialog.yes_no("Dar de baja",
                f"Confirmas dar de baja al socio "
                f"{self.socio_actual['nro_socio']}?"):
            return
        hoy = hoy_db()
        with get_conn() as con:
            con.execute("UPDATE socios SET fec_baj=?, usr_mod=?, fec_mod=? "
                        "WHERE nro_socio=?",
                        (hoy, self.app.usuario["usuario"],
                         datetime.now().isoformat(timespec="seconds"),
                         self.socio_actual["nro_socio"]))
        registrar_auditoria(self.app.usuario["usuario"], "BAJA_SOCIO",
                            f"socio={self.socio_actual['nro_socio']} "
                            f"{self.socio_actual.get('nombre', '')}")
        self.fields["fec_baj"].set(fecha_ui(hoy))
        self.socio_actual["fec_baj"] = hoy
        self.app.toast("Socio dado de baja.", "warning")

    def _guardar(self):
        if self.modo not in ("ALTA", "MODIFICACION"):
            self.app.toast("No estas en modo edicion.", "warning"); return
        nro = self._get("nro_socio")
        if self.modo == "MODIFICACION" and not nro.isdigit():
            self.app.toast("Nro. socio invalido.", "error"); return
        if not self._get("nombre"):
            self.app.toast("Falta el nombre.", "error"); return
        nombres_fecha = {"fec_nac": "Fecha de nacimiento",
                         "fec_ing": "Fecha de ingreso",
                         "fec_baj": "Fecha de baja",
                         "fec_egr": "Fecha de egreso"}
        for f, nom in nombres_fecha.items():
            if not val_fecha(self._get(f)):
                self.app.toast(f"{nom} invalida (dd/mm/aaaa).", "error")
                return
        if not val_cuil(self._get("cuil")):
            self.app.toast("CUIL invalido (11 digitos).", "error"); return
        if not val_mail(self._get("mail")):
            self.app.toast("Email invalido.", "error"); return

        cmax = parse_monto(self._get("credit_max"))
        cmes = parse_monto(self._get("cre_max_mes"))
        tope = parse_monto(self._get("tope_emp"))
        if None in (cmax, cmes, tope):
            self.app.toast("Valores numericos invalidos.", "error"); return

        datos = {n: self._get(n) for n in self.fields
                 if n not in ("credit_max", "cre_max_mes", "tope_emp")}
        datos["nro_socio"] = int(nro) if nro.isdigit() else 0
        for f in FECHAS_SOCIO:
            datos[f] = fecha_db(datos[f])
        datos["credit_max"] = cmax
        datos["cre_max_mes"] = cmes
        datos["tope_emp"] = tope
        now_iso = datetime.now().isoformat(timespec="seconds")
        usr = self.app.usuario["usuario"]

        # CUIL repetido
        cuil_dig = solo_digitos(datos.get("cuil"))
        if cuil_dig:
            with get_conn() as con:
                otro = [r for r in buscar_socios_por_documento(con, cuil_dig,
                                                               exacto=True)
                        if self.modo == "ALTA"
                        or r["nro_socio"] != datos["nro_socio"]]
            if otro:
                o = otro[0]
                self.app.toast(f"El CUIL ya esta cargado en el socio "
                               f"{o['nro_socio']} ({o['nombre']}).", "error")
                return

        try:
            with get_conn() as con:
                if self.modo == "ALTA":
                    # El numero se calcula recien al guardar y con la base
                    # bloqueada, por si otra PC dio de alta un socio
                    # mientras se completaba el formulario.
                    con.execute("BEGIN IMMEDIATE")
                    propuesto = datos["nro_socio"]
                    datos["nro_socio"] = proximo_nro_socio(con)
                    self.fields["nro_socio"].set(datos["nro_socio"])
                    campos = list(datos.keys()) + ["usr_alta", "fec_alta"]
                    vals = list(datos.values()) + [usr, now_iso]
                    ph = ",".join("?" * len(campos))
                    con.execute(
                        f"INSERT INTO socios ({','.join(campos)}) "
                        f"VALUES ({ph})", vals)
                    msg = f"Socio {datos['nro_socio']} dado de alta."
                    if propuesto and propuesto != datos["nro_socio"]:
                        msg += (f" (el {propuesto} lo tomo otra carga "
                                f"mientras tanto)")
                else:
                    sets = ", ".join(f"{k}=?" for k in datos
                                     if k != "nro_socio")
                    vals = [v for k, v in datos.items() if k != "nro_socio"]
                    vals += [usr, now_iso, datos["nro_socio"]]
                    con.execute(f"UPDATE socios SET {sets}, usr_mod=?, "
                                f"fec_mod=? WHERE nro_socio=?", vals)
                    msg = f"Socio {datos['nro_socio']} actualizado."
        except sqlite3.Error as e:
            self.app.toast(f"Error de BD: {e}", "error"); return

        if self.modo == "ALTA":
            registrar_auditoria(usr, "ALTA_SOCIO",
                                f"socio={datos['nro_socio']} "
                                f"{datos['nombre']}")
        else:
            cambios = describir_cambios(self.socio_actual, datos)
            registrar_auditoria(usr, "MODIFICA_SOCIO",
                                f"socio={datos['nro_socio']} {cambios}")
        self.socio_actual = datos
        self._set_modo("CONSULTA")
        self.app.toast(msg, "success")

    def _listar(self):
        VentanaListaSocios(self.app, callback=self._cargar_socio)

    def _credencial(self):
        if not self.socio_actual:
            self.app.toast("Primero busca un socio.", "warning"); return
        nro = self.socio_actual["nro_socio"]
        self.app._mark_active("credencial")
        self.app.show_panel(PanelCredencialSocio, titulo="Credenciales",
                            nro_inicial=nro)

    def _cargar_socio(self, nro):
        self.e_buscar.delete(0, "end")
        self.e_buscar.insert(0, str(nro))
        self._buscar()


# =====================================================================
#  VENTANA MODAL: Listado de socios
# =====================================================================
class VentanaListaSocios(ctk.CTkToplevel):
    def __init__(self, app, callback, consulta=""):
        super().__init__(app)
        NovaMutApp._poner_icono(self)
        self.app = app
        self.callback = callback
        self.title("Listado de socios")
        self.geometry("820x560")
        self.configure(fg_color=COLOR_BG)
        self.transient(app)
        self.grab_set()

        top = ctk.CTkFrame(self, fg_color="transparent")
        top.pack(fill="x", padx=18, pady=(18, 8))
        ctk.CTkLabel(top, text="Buscar:", font=F(12),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 8))
        self.e_q = ctk.CTkEntry(top, width=440, font=F(13),
                                fg_color=COLOR_CARD,
                                border_color=COLOR_BORDER,
                                text_color=COLOR_TEXT,
                                height=36, corner_radius=6,
                                placeholder_text="Nombre, numero, DNI o CUIL...")
        self.e_q.pack(side="left")
        if consulta:
            self.e_q.insert(0, consulta)
        self.e_q.bind("<KeyRelease>", lambda e: self._refresh())
        self.lbl_total = ctk.CTkLabel(top, text="", font=F(12),
                                       text_color=COLOR_TEXT_MUTED)
        self.lbl_total.pack(side="right")

        self.tabla = DataTable(self, columns=[
            (80,  "Nro",       "nro"),
            (70,  "Estado",    "estado"),
            (280, "Nombre",    "nombre"),
            (160, "Localidad", "localidad"),
            (140, "CUIL",      "cuil"),
        ], on_row_click=self._elegir)
        self.tabla.pack(fill="both", expand=True, padx=18, pady=(4, 12))

        foot = ctk.CTkFrame(self, fg_color="transparent")
        foot.pack(fill="x", padx=18, pady=(0, 18))
        SecondaryButton(foot, "Cerrar", command=self.destroy,
                        width=100).pack(side="right")

        self._refresh()
        self.e_q.focus()

    def _refresh(self):
        self.tabla.clear()
        txt = self.e_q.get().strip().upper()
        q = f"%{txt}%"
        dig = solo_digitos(txt)
        qd = f"%{dig}%" if len(dig) >= 3 else "\x00"
        with get_conn() as con:
            rows = con.execute(
                "SELECT nro_socio, nombre, localidad, fec_baj, cuil "
                "FROM socios "
                "WHERE UPPER(COALESCE(nombre,'')) LIKE ? "
                "   OR CAST(nro_socio AS TEXT) LIKE ? "
                "   OR REPLACE(REPLACE(REPLACE(COALESCE(cuil,''),'-',''),"
                "      ' ',''),'.','') LIKE ? "
                "ORDER BY nro_socio LIMIT 500",
                (q, q, qd)).fetchall()

        for r in rows:
            estado = "BAJA" if r["fec_baj"] else "ACTIVO"
            self.tabla.add_row({
                "nro": r["nro_socio"],
                "estado": estado,
                "nombre": r["nombre"] or "",
                "localidad": r["localidad"] or "",
                "cuil": r["cuil"] or "",
            }, badges={"estado": "danger" if r["fec_baj"] else "success"},
                key=r["nro_socio"])
        self.lbl_total.configure(text=f"Total: {len(rows)}")

    def _elegir(self, nro):
        self.callback(nro)
        self.destroy()


# =====================================================================
#  PANEL: PROVEEDORES (ABM)
# =====================================================================
class PanelProveedores(ctk.CTkFrame):
    OPCIONES_IVA = ["", "RESPONSABLE INSCRIPTO", "MONOTRIBUTO", "EXENTO",
                    "CONSUMIDOR FINAL", "NO CATEGORIZADO"]

    def __init__(self, master, app, titulo="Proveedores", cod_inicial=None,
                 **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.modo = "CONSULTA"
        self.proveedor_actual = None
        self.fields = {}

        app.set_breadcrumb("Actualizacion de archivos", "Proveedores")
        self._actualizar_badge_modo()

        self._build_toolbar()
        self._build_form()
        self._build_action_bar()
        self._set_modo("CONSULTA")

        if cod_inicial:
            self.e_buscar.insert(0, str(cod_inicial))
            self.after(50, self._buscar)

    def _build_toolbar(self):
        tb = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                          border_color=COLOR_BORDER, border_width=1,
                          corner_radius=10, height=64)
        tb.pack(fill="x", pady=(0, 12))
        tb.pack_propagate(False)
        inner = ctk.CTkFrame(tb, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=12)

        ctk.CTkLabel(inner, text="Codigo", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 8))
        self.e_buscar = ctk.CTkEntry(
            inner, width=120, font=F(14, "bold"),
            fg_color=COLOR_CARD, border_color=COLOR_BORDER,
            text_color=COLOR_TEXT, height=38, corner_radius=6,
            placeholder_text="1")
        self.e_buscar.pack(side="left", padx=(0, 8))
        self.e_buscar.bind("<Return>", lambda e: self._buscar())

        SecondaryButton(inner, "Buscar", "\u2315",
                        command=self._buscar, width=120).pack(side="left",
                                                              padx=4)
        SecondaryButton(inner, "Listar todos", "\u2261",
                        command=self._listar, width=140).pack(side="left",
                                                              padx=4)

    def _build_form(self):
        # Datos generales
        card1 = Card(self, title="Datos generales")
        card1.pack(fill="x", pady=6)
        g = ctk.CTkFrame(card1, fg_color="transparent")
        g.pack(fill="x", padx=18, pady=(0, 16))
        g.grid_columnconfigure((0, 1, 2, 3), weight=1)

        self._add_field(g, "cod_proveedor", "Codigo", 0, 0)
        self._add_field(g, "razon_social",  "Razon social", 0, 1, cspan=3,
                        uppercase=True)
        self._add_field(g, "cuit",          "CUIT", 1, 0)
        self._add_field(g, "condicion_iva", "Cond. IVA", 1, 1, cspan=2,
                        values=self.OPCIONES_IVA)
        self._estado_badge = Badge(g, "", "muted")
        self._estado_badge.grid(row=1, column=3, sticky="w", padx=6, pady=6)

        # Contacto
        card2 = Card(self, title="Contacto")
        card2.pack(fill="x", pady=6)
        g2 = ctk.CTkFrame(card2, fg_color="transparent")
        g2.pack(fill="x", padx=18, pady=(0, 16))
        g2.grid_columnconfigure((0, 1, 2, 3), weight=1)
        self._add_field(g2, "direccion", "Direccion", 0, 0, cspan=3,
                        uppercase=True)
        self._add_field(g2, "cp",        "CP", 0, 3)
        self._add_field(g2, "localidad", "Localidad", 1, 0, cspan=2,
                        uppercase=True)
        self._add_field(g2, "telefono",  "Telefono", 1, 2)
        self._add_field(g2, "mail",      "Email", 1, 3)

        # Datos bancarios
        card3 = Card(self, title="Datos bancarios")
        card3.pack(fill="x", pady=6)
        g3 = ctk.CTkFrame(card3, fg_color="transparent")
        g3.pack(fill="x", padx=18, pady=(0, 16))
        g3.grid_columnconfigure(0, weight=1)
        self._add_field(g3, "cbu", "CBU", 0, 0)

    def _add_field(self, parent, name, label, row, col, cspan=1,
                   values=None, uppercase=False):
        f = Field(parent, label, name=name, values=values,
                  uppercase=uppercase)
        f.grid(row=row, column=col, columnspan=cspan,
               sticky="ew", padx=6, pady=6)
        self.fields[name] = f

    def _build_action_bar(self):
        bar = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                           border_color=COLOR_BORDER, border_width=1,
                           corner_radius=10, height=72)
        bar.pack(fill="x", pady=(12, 8))
        bar.pack_propagate(False)
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=16)

        left = ctk.CTkFrame(inner, fg_color="transparent")
        left.pack(side="left")
        btns = [
            SecondaryButton(left, "Nuevo", "+", command=self._nuevo,
                            width=110),
            SecondaryButton(left, "Modificar", "\u270E",
                            command=self._modificar, width=130),
            DangerButton(left, "Activar/Baja", "\u21C6",
                         command=self._toggle_activo, width=150),
        ]
        for b in btns:
            b.pack(side="left", padx=4)
        deshabilitar_sin_nivel(self.app, btns)

        right = ctk.CTkFrame(inner, fg_color="transparent")
        right.pack(side="right")
        self.btn_guardar = PrimaryButton(
            right, "Guardar", "\u2713",
            command=self._guardar, width=160)
        self.btn_guardar.pack(side="right", padx=4)

    def _actualizar_badge_modo(self):
        badges = {
            "CONSULTA":     ("Consulta",     "info"),
            "ALTA":         ("Alta",         "success"),
            "MODIFICACION": ("Modificacion", "warning"),
        }
        txt, kind = badges.get(self.modo, ("", "info"))
        self.app.set_badge(txt, kind)

    def _set_modo(self, modo):
        self.modo = modo
        self._actualizar_badge_modo()
        editable = modo in ("ALTA", "MODIFICACION")
        for name, f in self.fields.items():
            if name == "cod_proveedor":
                # solo en ALTA se ve como (automatico), nunca editable
                f.set_state("disabled")
                continue
            f.set_state("normal" if editable else "disabled")
        self.btn_guardar.configure(
            state="normal" if editable else "disabled",
            fg_color=COLOR_SUCCESS if editable else "#94a3b8")

    def _limpiar(self):
        for f in self.fields.values():
            f.set("")
        self._estado_badge.configure(text="")

    def _get(self, name):
        return self.fields[name].get()

    def _buscar(self):
        cod = self.e_buscar.get().strip() or self._get("cod_proveedor")
        if not cod.isdigit():
            self.app.toast("Codigo invalido.", "error"); return
        with get_conn() as con:
            row = con.execute("SELECT * FROM proveedores "
                              "WHERE cod_proveedor=?",
                              (int(cod),)).fetchone()
        if row:
            self.proveedor_actual = dict(row)
            for k, v in self.proveedor_actual.items():
                if k in self.fields:
                    self.fields[k].set(v)
            estado_txt = "Activo" if row["activo"] else "Baja"
            kind = "success" if row["activo"] else "danger"
            bg, fg = Badge.KINDS[kind]
            self._estado_badge.configure(text=estado_txt.upper(),
                                          fg_color=bg, text_color=fg)
            self._set_modo("CONSULTA")
            self.app.toast(f"Proveedor {cod} encontrado.", "success")
        else:
            self._limpiar()
            self.fields["cod_proveedor"].set(cod)
            self.proveedor_actual = None
            self.app.toast(f"Proveedor {cod} no existe. Podes darlo de alta.",
                           "warning")

    def _nuevo(self):
        if not self.app.puede(NIVEL_OPERAR, "dar de alta proveedores"):
            return
        self._limpiar()
        self.proveedor_actual = None
        self._set_modo("ALTA")
        self.fields["cod_proveedor"].set("(automatico)")
        self.fields["razon_social"].focus()
        self.app.toast("Modo alta.", "info")

    def _modificar(self):
        if not self.app.puede(NIVEL_OPERAR, "modificar proveedores"): return
        if not self.proveedor_actual:
            self.app.toast("Primero busca un proveedor.", "warning"); return
        self._set_modo("MODIFICACION")
        self.fields["razon_social"].focus()
        self.app.toast("Modo modificacion.", "info")

    def _toggle_activo(self):
        if not self.app.puede(NIVEL_OPERAR, "dar de baja proveedores"):
            return
        if not self.proveedor_actual:
            self.app.toast("Primero busca un proveedor.", "warning"); return
        activar = not self.proveedor_actual["activo"]
        verbo = "activar" if activar else "dar de baja"
        if not ConfirmDialog.yes_no("Confirmar",
                f"Confirmas {verbo} al proveedor "
                f"{self.proveedor_actual['cod_proveedor']}?"):
            return
        with get_conn() as con:
            con.execute("UPDATE proveedores SET activo=? "
                        "WHERE cod_proveedor=?",
                        (1 if activar else 0,
                         self.proveedor_actual["cod_proveedor"]))
        self.proveedor_actual["activo"] = 1 if activar else 0
        estado_txt = "Activo" if activar else "Baja"
        kind = "success" if activar else "danger"
        bg, fg = Badge.KINDS[kind]
        self._estado_badge.configure(text=estado_txt.upper(),
                                      fg_color=bg, text_color=fg)
        registrar_auditoria(
            self.app.usuario["usuario"],
            "ACTIVA_PROVEEDOR" if activar else "BAJA_PROVEEDOR",
            f"proveedor={self.proveedor_actual['cod_proveedor']} "
            f"{self.proveedor_actual.get('razon_social', '')}")
        self.app.toast(f"Proveedor {verbo}.",
                       "success" if activar else "warning")

    def _guardar(self):
        if self.modo not in ("ALTA", "MODIFICACION"):
            self.app.toast("No estas en modo edicion.", "warning"); return
        razon = self._get("razon_social")
        if not razon:
            self.app.toast("Falta razon social.", "error"); return
        cuit = self._get("cuit")
        if cuit and not val_cuil(cuit):
            self.app.toast("CUIT invalido.", "error"); return
        mail = self._get("mail")
        if not val_mail(mail):
            self.app.toast("Email invalido.", "error"); return

        datos = {
            "razon_social":  razon,
            "cuit":          cuit,
            "direccion":     self._get("direccion"),
            "localidad":     self._get("localidad"),
            "cp":            self._get("cp"),
            "telefono":      self._get("telefono"),
            "mail":          mail,
            "condicion_iva": self._get("condicion_iva"),
            "cbu":           self._get("cbu"),
        }
        now_iso = datetime.now().isoformat(timespec="seconds")
        try:
            with get_conn() as con:
                if self.modo == "ALTA":
                    campos = list(datos.keys()) + ["activo", "usr_alta",
                                                    "fec_alta"]
                    vals = list(datos.values()) + [
                        1, self.app.usuario["usuario"], now_iso]
                    ph = ",".join("?" * len(campos))
                    cur = con.execute(
                        f"INSERT INTO proveedores ({','.join(campos)}) "
                        f"VALUES ({ph})", vals)
                    nuevo_cod = cur.lastrowid
                    msg = (f"Proveedor '{razon}' dado de alta con "
                           f"codigo {nuevo_cod}.")
                else:
                    cod = self.proveedor_actual["cod_proveedor"]
                    sets = ", ".join(f"{k}=?" for k in datos)
                    vals = list(datos.values()) + [cod]
                    con.execute(f"UPDATE proveedores SET {sets} "
                                f"WHERE cod_proveedor=?", vals)
                    nuevo_cod = cod
                    msg = f"Proveedor {cod} actualizado."
        except sqlite3.Error as e:
            self.app.toast(f"Error de BD: {e}", "error"); return

        if self.modo == "ALTA":
            registrar_auditoria(self.app.usuario["usuario"],
                                "ALTA_PROVEEDOR",
                                f"proveedor={nuevo_cod} {razon}")
        else:
            registrar_auditoria(
                self.app.usuario["usuario"], "MODIFICA_PROVEEDOR",
                f"proveedor={nuevo_cod} "
                f"{describir_cambios(self.proveedor_actual, datos)}")
        self._set_modo("CONSULTA")
        self.e_buscar.delete(0, "end")
        self.e_buscar.insert(0, str(nuevo_cod))
        self._buscar()
        self.app.toast(msg, "success")

    def _listar(self):
        VentanaListaProveedores(self.app, callback=self._cargar_prov)

    def _cargar_prov(self, cod):
        self.e_buscar.delete(0, "end")
        self.e_buscar.insert(0, str(cod))
        self._buscar()


class VentanaListaProveedores(ctk.CTkToplevel):
    def __init__(self, app, callback):
        super().__init__(app)
        NovaMutApp._poner_icono(self)
        self.app = app
        self.callback = callback
        self.title("Listado de proveedores")
        self.geometry("820x560")
        self.configure(fg_color=COLOR_BG)
        self.transient(app)
        self.grab_set()

        top = ctk.CTkFrame(self, fg_color="transparent")
        top.pack(fill="x", padx=18, pady=(18, 8))
        ctk.CTkLabel(top, text="Buscar:", font=F(12),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 8))
        self.e_q = ctk.CTkEntry(top, width=440, font=F(13),
                                fg_color=COLOR_CARD,
                                border_color=COLOR_BORDER,
                                text_color=COLOR_TEXT, height=36,
                                corner_radius=6,
                                placeholder_text="Razon social o CUIT...")
        self.e_q.pack(side="left")
        self.e_q.bind("<KeyRelease>", lambda e: self._refresh())
        self.lbl_total = ctk.CTkLabel(top, text="", font=F(12),
                                       text_color=COLOR_TEXT_MUTED)
        self.lbl_total.pack(side="right")

        self.tabla = DataTable(self, columns=[
            (70,  "Codigo",       "cod"),
            (70,  "Estado",       "estado"),
            (280, "Razon social", "razon"),
            (140, "CUIT",         "cuit"),
            (160, "Localidad",    "localidad"),
        ], on_row_click=self._elegir)
        self.tabla.pack(fill="both", expand=True, padx=18, pady=(4, 12))

        foot = ctk.CTkFrame(self, fg_color="transparent")
        foot.pack(fill="x", padx=18, pady=(0, 18))
        SecondaryButton(foot, "Cerrar", command=self.destroy,
                        width=100).pack(side="right")

        self._refresh()
        self.e_q.focus()

    def _refresh(self):
        self.tabla.clear()
        q = f"%{self.e_q.get().strip().upper()}%"
        with get_conn() as con:
            rows = con.execute(
                "SELECT cod_proveedor, razon_social, cuit, localidad, activo "
                "FROM proveedores WHERE UPPER(razon_social) LIKE ? "
                "OR COALESCE(cuit,'') LIKE ? "
                "ORDER BY cod_proveedor", (q, q)).fetchall()
        for r in rows:
            self.tabla.add_row({
                "cod": r["cod_proveedor"],
                "estado": "ACTIVO" if r["activo"] else "BAJA",
                "razon": (r["razon_social"] or "")[:38],
                "cuit": r["cuit"] or "",
                "localidad": r["localidad"] or "",
            }, badges={"estado": "success" if r["activo"] else "danger"},
                key=r["cod_proveedor"])
        self.lbl_total.configure(text=f"Total: {len(rows)}")

    def _elegir(self, cod):
        self.callback(cod)
        self.destroy()


# =====================================================================
#  PANEL: DESC/COMPRAS SIN ORDEN
#  La mutual paga al proveedor y le descuenta al socio en cuotas.
# =====================================================================
FECHAS_COMPRA = ("fec_factura", "fe_1cu_pro", "fe_1cu_soc")


def plan_cuotas(importe, cantidad, primera):
    """[(fecha_vencimiento, importe)] en partes iguales; la diferencia de
    centavos va en la ultima. Sin fecha de primera cuota -> []."""
    if not primera or not cantidad:
        return []
    cuota = round(importe / cantidad, 2)
    plan, acumulado = [], 0.0
    for i in range(cantidad):
        if i == cantidad - 1:
            imp = round(importe - acumulado, 2)
        else:
            imp = cuota; acumulado += cuota
        plan.append((sumar_meses(primera, i), imp))
    return plan


def cuotas_ya_canceladas(con, desc_id):
    """(cuotas pagadas al proveedor, cuotas cobradas al socio)"""
    pag = con.execute("SELECT COUNT(*) AS c FROM cuotas_proveedor "
                      "WHERE desc_compra_id=? AND estado='PAGADA'",
                      (desc_id,)).fetchone()["c"]
    cob = con.execute("SELECT COUNT(*) AS c FROM cuotas_socio "
                      "WHERE desc_compra_id=? AND estado='COBRADA'",
                      (desc_id,)).fetchone()["c"]
    return pag, cob


def deuda_pendiente_socio(con, nro_socio, excluir_desc_id=None):
    row = con.execute(
        "SELECT COALESCE(SUM(c.importe), 0) AS t FROM cuotas_socio c "
        "JOIN desc_compras_sno d ON d.id = c.desc_compra_id "
        "WHERE d.nro_socio=? AND d.estado='ACTIVO' "
        "AND c.estado='PENDIENTE' AND d.id IS NOT ?",
        (nro_socio, excluir_desc_id)).fetchone()
    return float(row["t"] or 0)


def control_credito(con, nro_socio, importe, plan, excluir_desc_id=None):
    """Lista de avisos si la compra supera el credito maximo total o el
    maximo mensual del socio (vacia si esta todo bien o no hay topes)."""
    s = con.execute("SELECT credit_max, cre_max_mes FROM socios "
                    "WHERE nro_socio=?", (nro_socio,)).fetchone()
    if not s:
        return []
    avisos = []
    cmax = float(s["credit_max"] or 0)
    cmes = float(s["cre_max_mes"] or 0)
    if cmax > 0:
        deuda = deuda_pendiente_socio(con, nro_socio, excluir_desc_id)
        if deuda + importe > cmax + 0.004:
            avisos.append(
                f"Credito maximo: {fmt_moneda(cmax)}\n"
                f"Deuda pendiente: {fmt_moneda(deuda)} + esta compra "
                f"{fmt_moneda(importe)} = {fmt_moneda(deuda + importe)}")
    if cmes > 0 and plan:
        peor = None
        for fv, imp in plan:
            mes = fv.strftime("%Y-%m")
            ya = con.execute(
                "SELECT COALESCE(SUM(c.importe), 0) AS t "
                "FROM cuotas_socio c "
                "JOIN desc_compras_sno d ON d.id = c.desc_compra_id "
                "WHERE d.nro_socio=? AND d.estado='ACTIVO' "
                "AND c.estado='PENDIENTE' AND d.id IS NOT ? "
                "AND substr(c.fec_vencimiento, 1, 7)=?",
                (nro_socio, excluir_desc_id, mes)).fetchone()["t"] or 0
            total = float(ya) + imp
            if total > cmes + 0.004 and (not peor or total > peor[1]):
                peor = (fv, total, float(ya), imp)
        if peor:
            fv, total, ya, imp = peor
            avisos.append(
                f"Credito maximo mensual: {fmt_moneda(cmes)}\n"
                f"En {MESES[fv.month - 1].capitalize()} {fv.year} pagaria "
                f"{fmt_moneda(total)} (ya tiene {fmt_moneda(ya)} + cuota "
                f"{fmt_moneda(imp)})")
    return avisos


class PanelDescCompras(ctk.CTkFrame):

    def __init__(self, master, app, titulo="Desc/Compras", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.modo = "CONSULTA"
        self.registro_actual = None
        self.fields = {}

        app.set_breadcrumb("Actualizacion de archivos",
                           "Desc/Compras sin orden")
        self._actualizar_badge_modo()

        self._build_toolbar()
        self._build_form()
        self._build_resumen()
        self._build_action_bar()

        self._set_modo("CONSULTA")
        self._proximo_numero()

    def _build_toolbar(self):
        tb = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                          border_color=COLOR_BORDER, border_width=1,
                          corner_radius=10, height=64)
        tb.pack(fill="x", pady=(0, 12))
        tb.pack_propagate(False)
        inner = ctk.CTkFrame(tb, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=12)

        ctk.CTkLabel(inner, text="Tipo", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 6))
        self.e_tipo = ctk.CTkEntry(
            inner, width=70, font=F(14, "bold"),
            fg_color=COLOR_CARD, border_color=COLOR_BORDER,
            text_color=COLOR_TEXT, height=38, corner_radius=6)
        self.e_tipo.pack(side="left", padx=(0, 8))
        self.e_tipo.insert(0, "S01")

        ctk.CTkLabel(inner, text="Nro", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 6))
        self.e_nro = ctk.CTkEntry(
            inner, width=110, font=F(14, "bold"),
            fg_color=COLOR_CARD, border_color=COLOR_BORDER,
            text_color=COLOR_TEXT, height=38, corner_radius=6)
        self.e_nro.pack(side="left", padx=(0, 8))
        self.e_nro.bind("<Return>", lambda e: self._buscar())

        SecondaryButton(inner, "Buscar", "\u2315",
                        command=self._buscar, width=120).pack(side="left",
                                                              padx=4)

        # Ultimo cierre a la derecha
        r = ctk.CTkFrame(inner, fg_color="transparent")
        r.pack(side="right")
        ctk.CTkLabel(r, text="Ultimo cierre:", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 6))
        self.lbl_cierre = ctk.CTkLabel(r, text="(sin cierres)",
                                       font=F(12, "bold"),
                                       text_color=COLOR_ACCENT)
        self.lbl_cierre.pack(side="left")

    def _build_form(self):
        # --- Partes ---
        card1 = Card(self, title="Partes")
        card1.pack(fill="x", pady=6)
        g = ctk.CTkFrame(card1, fg_color="transparent")
        g.pack(fill="x", padx=18, pady=(0, 8))
        g.grid_columnconfigure(1, weight=1)

        # Proveedor
        ctk.CTkLabel(g, text="Cod. proveedor", font=F(11),
                     text_color=COLOR_TEXT_MUTED).grid(row=0, column=0,
                                                        sticky="w", padx=6,
                                                        pady=(0, 2))
        self.e_prov = ctk.CTkEntry(g, width=100, font=F(13),
                                    fg_color=COLOR_CARD,
                                    border_color=COLOR_BORDER,
                                    text_color=COLOR_TEXT, height=34,
                                    corner_radius=6)
        self.e_prov.grid(row=1, column=0, sticky="w", padx=6)
        self.e_prov.bind("<FocusOut>", lambda e: self._mostrar_prov())
        self.e_prov.bind("<Return>", lambda e: self._mostrar_prov())
        self.fields["cod_proveedor"] = _ProxyEntry(self.e_prov)

        self.lbl_prov_nom = ctk.CTkLabel(g, text="(codigo de proveedor)",
                                          font=F(12),
                                          text_color=COLOR_TEXT_MUTED,
                                          anchor="w")
        self.lbl_prov_nom.grid(row=1, column=1, sticky="ew", padx=12)

        # Socio
        ctk.CTkLabel(g, text="Nro. socio", font=F(11),
                     text_color=COLOR_TEXT_MUTED).grid(row=2, column=0,
                                                        sticky="w", padx=6,
                                                        pady=(8, 2))
        self.e_socio = ctk.CTkEntry(g, width=100, font=F(13),
                                     fg_color=COLOR_CARD,
                                     border_color=COLOR_BORDER,
                                     text_color=COLOR_TEXT, height=34,
                                     corner_radius=6)
        self.e_socio.grid(row=3, column=0, sticky="w", padx=6)
        self.e_socio.bind("<FocusOut>", lambda e: self._mostrar_socio())
        self.e_socio.bind("<Return>", lambda e: self._mostrar_socio())
        self.fields["nro_socio"] = _ProxyEntry(self.e_socio)

        self.lbl_socio_nom = ctk.CTkLabel(g, text="(nro. de socio)",
                                          font=F(12),
                                          text_color=COLOR_TEXT_MUTED,
                                          anchor="w")
        self.lbl_socio_nom.grid(row=3, column=1, sticky="ew", padx=12,
                                pady=(0, 8))

        # --- Datos de la operacion ---
        card2 = Card(self, title="Datos de la operacion")
        card2.pack(fill="x", pady=6)
        g2 = ctk.CTkFrame(card2, fg_color="transparent")
        g2.pack(fill="x", padx=18, pady=(0, 16))
        g2.grid_columnconfigure((0, 1, 2, 3), weight=1)

        self._add_field(g2, "concepto",   "Concepto", 0, 0, cspan=4,
                        uppercase=True)
        self._add_field(g2, "fec_factura","Fecha factura", 1, 0)
        self._add_field(g2, "nro_factura","N° factura", 1, 1)
        self._add_field(g2, "importe",   "Importe", 1, 2)

        self._add_field(g2, "observacion","Observaciones", 2, 0, cspan=4,
                        uppercase=True)

        # --- Cuotas ---
        card3 = Card(self, title="Cuotas")
        card3.pack(fill="x", pady=6)
        g3 = ctk.CTkFrame(card3, fg_color="transparent")
        g3.pack(fill="x", padx=18, pady=(0, 16))
        g3.grid_columnconfigure((0, 1, 2, 3), weight=1)

        self._add_field(g3, "can_cuot_pr", "Cant. cuotas proveedor", 0, 0)
        self._add_field(g3, "fe_1cu_pro",  "Fecha 1ra cuota proveedor",
                        0, 1)
        self._add_field(g3, "can_cuot_so", "Cant. cuotas socio", 0, 2)
        self._add_field(g3, "fe_1cu_soc",  "Fecha 1ra cuota socio", 0, 3)

        # Enganches para recalcular
        for k in ("importe", "can_cuot_pr", "can_cuot_so"):
            self.fields[k].bind_key("<KeyRelease>",
                                     lambda e: self._recalcular())

    def _add_field(self, parent, name, label, row, col, cspan=1,
                   values=None, uppercase=False):
        f = Field(parent, label, name=name, values=values,
                  uppercase=uppercase)
        f.grid(row=row, column=col, columnspan=cspan,
               sticky="ew", padx=6, pady=6)
        self.fields[name] = f

    def _build_resumen(self):
        self.resumen = Card(self)
        self.resumen.pack(fill="x", pady=6)
        wrap = ctk.CTkFrame(self.resumen, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)
        wrap.grid_columnconfigure((0, 1), weight=1)

        ctk.CTkLabel(wrap, text="CUOTA A PROVEEDOR", font=F(10, "bold"),
                     text_color=COLOR_TEXT_MUTED).grid(row=0, column=0,
                                                        sticky="w")
        self.lbl_cuota_pr = ctk.CTkLabel(wrap, text="--",
                                          font=F(22, "bold"),
                                          text_color=COLOR_SUCCESS,
                                          anchor="w")
        self.lbl_cuota_pr.grid(row=1, column=0, sticky="w")

        ctk.CTkLabel(wrap, text="CUOTA A SOCIO", font=F(10, "bold"),
                     text_color=COLOR_TEXT_MUTED).grid(row=0, column=1,
                                                        sticky="w")
        self.lbl_cuota_so = ctk.CTkLabel(wrap, text="--",
                                          font=F(22, "bold"),
                                          text_color=COLOR_ACCENT,
                                          anchor="w")
        self.lbl_cuota_so.grid(row=1, column=1, sticky="w")

    def _build_action_bar(self):
        bar = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                           border_color=COLOR_BORDER, border_width=1,
                           corner_radius=10, height=72)
        bar.pack(fill="x", pady=(12, 8))
        bar.pack_propagate(False)
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=16)

        left = ctk.CTkFrame(inner, fg_color="transparent")
        left.pack(side="left")
        btns = [
            SecondaryButton(left, "Nuevo", "+", command=self._nuevo,
                            width=110),
            SecondaryButton(left, "Modificar", "\u270E",
                            command=self._modificar, width=130),
            DangerButton(left, "Anular", "\u2715",
                         command=self._anular, width=130),
        ]
        for b in btns:
            b.pack(side="left", padx=4)
        deshabilitar_sin_nivel(self.app, btns)

        right = ctk.CTkFrame(inner, fg_color="transparent")
        right.pack(side="right")
        self.btn_guardar = PrimaryButton(
            right, "Guardar", "\u2713",
            command=self._guardar, width=160)
        self.btn_guardar.pack(side="right", padx=4)

    def _actualizar_badge_modo(self):
        badges = {
            "CONSULTA":     ("Consulta",     "info"),
            "ALTA":         ("Alta",         "success"),
            "MODIFICACION": ("Modificacion", "warning"),
        }
        txt, kind = badges.get(self.modo, ("", "info"))
        self.app.set_badge(txt, kind)

    def _set_modo(self, modo):
        self.modo = modo
        self._actualizar_badge_modo()
        editable = modo in ("ALTA", "MODIFICACION")
        for name, f in self.fields.items():
            f.set_state("normal" if editable else "disabled")
        # tipo/nro: solo en alta
        for w in (self.e_tipo, self.e_nro):
            if modo == "ALTA" or modo == "CONSULTA":
                w.configure(state="normal")
            else:
                w.configure(state="disabled")
        self.btn_guardar.configure(
            state="normal" if editable else "disabled",
            fg_color=COLOR_SUCCESS if editable else "#94a3b8")

    def _limpiar(self):
        for f in self.fields.values():
            f.set("")
        self.fields["can_cuot_pr"].set("1")
        self.fields["can_cuot_so"].set("1")
        self.lbl_prov_nom.configure(text="(codigo de proveedor)",
                                     text_color=COLOR_TEXT_MUTED)
        self.lbl_socio_nom.configure(text="(nro. de socio)",
                                      text_color=COLOR_TEXT_MUTED)
        self.lbl_cuota_pr.configure(text="--")
        self.lbl_cuota_so.configure(text="--")

    def _get(self, name):
        return self.fields[name].get()

    def _proximo_numero(self):
        tip = self.e_tipo.get().strip() or "S01"
        with get_conn() as con:
            row = con.execute(
                "SELECT MAX(nro_compro) AS m FROM desc_compras_sno "
                "WHERE tip_compro=?", (tip,)).fetchone()
        prox = (row["m"] or 0) + 1
        if not self.e_nro.get().strip():
            self.e_nro.insert(0, str(prox))

    def _mostrar_prov(self):
        cod = self.e_prov.get().strip()
        if not cod.isdigit():
            self.lbl_prov_nom.configure(text="(codigo invalido)",
                                         text_color=COLOR_DANGER)
            return
        with get_conn() as con:
            row = con.execute("SELECT razon_social, cuit, activo "
                              "FROM proveedores WHERE cod_proveedor=?",
                              (int(cod),)).fetchone()
        if row:
            estado = "" if row["activo"] else "  [BAJA]"
            self.lbl_prov_nom.configure(
                text=f"{row['razon_social']}  ·  CUIT: {row['cuit'] or '-'}"
                     f"{estado}",
                text_color=COLOR_SUCCESS if row["activo"] else COLOR_WARNING)
        else:
            self.lbl_prov_nom.configure(text="Proveedor no encontrado",
                                         text_color=COLOR_DANGER)

    def _mostrar_socio(self):
        nro = self.e_socio.get().strip()
        if not nro.isdigit():
            self.lbl_socio_nom.configure(text="(numero invalido)",
                                          text_color=COLOR_DANGER)
            return
        with get_conn() as con:
            row = con.execute("SELECT nombre, fec_baj, credit_max "
                              "FROM socios WHERE nro_socio=?",
                              (int(nro),)).fetchone()
            excl = self.registro_actual["id"] if (
                self.registro_actual and self.modo != "ALTA") else None
            deuda = deuda_pendiente_socio(con, int(nro), excl) if row else 0
        if row:
            estado = "  [BAJA]" if row["fec_baj"] else ""
            tope = ""
            if row["credit_max"]:
                disp = row["credit_max"] - deuda
                tope = (f"  ·  Cred. max: {fmt_moneda(row['credit_max'])}"
                        f"  ·  Disponible: {fmt_moneda(disp)}")
            elif deuda:
                tope = f"  ·  Deuda pendiente: {fmt_moneda(deuda)}"
            self.lbl_socio_nom.configure(
                text=f"{row['nombre']}{estado}{tope}",
                text_color=COLOR_WARNING if row["fec_baj"] else COLOR_SUCCESS)
        else:
            self.lbl_socio_nom.configure(text="Socio no encontrado",
                                          text_color=COLOR_DANGER)

    def _recalcular(self):
        try:
            imp = parse_monto(self._get("importe") or "0") or 0.0
            cp = int(self._get("can_cuot_pr") or "0")
            cs = int(self._get("can_cuot_so") or "0")
        except (ValueError, TypeError):
            self.lbl_cuota_pr.configure(text="--")
            self.lbl_cuota_so.configure(text="--")
            return
        if cp > 0:
            self.lbl_cuota_pr.configure(
                text=f"{cp} x {fmt_moneda(imp/cp)}")
        else:
            self.lbl_cuota_pr.configure(text="--")
        if cs > 0:
            self.lbl_cuota_so.configure(
                text=f"{cs} x {fmt_moneda(imp/cs)}")
        else:
            self.lbl_cuota_so.configure(text="--")

    def _buscar(self):
        tip = self.e_tipo.get().strip()
        nro = self.e_nro.get().strip()
        if not tip or not nro.isdigit():
            self.app.toast("Tipo y N° invalidos.", "error"); return
        with get_conn() as con:
            row = con.execute(
                "SELECT * FROM desc_compras_sno "
                "WHERE tip_compro=? AND nro_compro=?",
                (tip, int(nro))).fetchone()
        if row:
            self.registro_actual = dict(row)
            self._set_modo("CONSULTA")
            for k, v in self.registro_actual.items():
                if k in self.fields:
                    self.fields[k].set(fecha_ui(v) if k in FECHAS_COMPRA
                                       else v)
            self._mostrar_prov(); self._mostrar_socio(); self._recalcular()
            estado = self.registro_actual.get("estado", "ACTIVO")
            kind = "success" if estado == "ACTIVO" else "warning"
            self.app.toast(f"Comprobante {tip}-{nro} encontrado ({estado}).",
                           kind)
        else:
            self._limpiar()
            self.registro_actual = None
            self.app.toast(f"Comprobante {tip}-{nro} no existe.",
                           "warning")

    def _nuevo(self):
        if not self.app.puede(NIVEL_OPERAR, "cargar compras"): return
        self._limpiar()
        self.registro_actual = None
        self._set_modo("ALTA")
        self.e_nro.delete(0, "end")
        self._proximo_numero()
        self.fields["fec_factura"].set(hoy_ui())
        self.e_prov.focus_set()
        self.app.toast("Modo alta.", "info")

    def _modificar(self):
        if not self.app.puede(NIVEL_OPERAR, "modificar compras"): return
        if not self.registro_actual:
            self.app.toast("Primero busca un comprobante.", "warning")
            return
        if self.registro_actual.get("estado") == "ANULADO":
            self.app.toast("Comprobante anulado, no se puede modificar.",
                           "error"); return
        self._set_modo("MODIFICACION")
        self.fields["concepto"].focus()
        with get_conn() as con:
            pag, cob = cuotas_ya_canceladas(con, self.registro_actual["id"])
        if pag or cob:
            self.app.toast("Ya hay cuotas pagadas o cobradas: solo se "
                           "pueden cambiar concepto, factura y "
                           "observaciones.", "warning")

    def _anular(self):
        if not self.app.puede(NIVEL_OPERAR, "anular compras"): return
        if not self.registro_actual:
            self.app.toast("Primero busca un comprobante.", "warning")
            return
        if self.registro_actual.get("estado") == "ANULADO":
            self.app.toast("Ya esta anulado.", "warning"); return
        if not ConfirmDialog.yes_no("Anular",
                f"Anular el comprobante "
                f"{self.registro_actual['tip_compro']}-"
                f"{self.registro_actual['nro_compro']}?\n"
                "Se anulan tambien las cuotas pendientes."):
            return
        with get_conn() as con:
            con.execute("UPDATE desc_compras_sno SET estado='ANULADO', "
                        "usr_mod=?, fec_mod=? WHERE id=?",
                        (self.app.usuario["usuario"],
                         datetime.now().isoformat(timespec="seconds"),
                         self.registro_actual["id"]))
            con.execute("UPDATE cuotas_proveedor SET estado='ANULADA' "
                        "WHERE desc_compra_id=? AND fec_pago IS NULL",
                        (self.registro_actual["id"],))
            con.execute("UPDATE cuotas_socio SET estado='ANULADA' "
                        "WHERE desc_compra_id=? AND fec_cobro IS NULL",
                        (self.registro_actual["id"],))
        registrar_auditoria(
            self.app.usuario["usuario"], "ANULA_COMPRA",
            f"{self.registro_actual['tip_compro']}-"
            f"{self.registro_actual['nro_compro']} "
            f"socio={self.registro_actual.get('nro_socio')} "
            f"importe={self.registro_actual.get('importe')}")
        self.registro_actual["estado"] = "ANULADO"
        self.app.toast("Comprobante anulado.", "warning")

    def _guardar(self):
        if self.modo not in ("ALTA", "MODIFICACION"):
            self.app.toast("No estas en modo edicion.", "warning"); return

        tip = self.e_tipo.get().strip()
        nro = self.e_nro.get().strip()
        cod_prov = self._get("cod_proveedor")
        nro_soc = self._get("nro_socio")
        concepto = self._get("concepto")
        fec_fac = self._get("fec_factura")
        nro_fac = self._get("nro_factura")
        imp_s = self._get("importe")
        cpr_s = self._get("can_cuot_pr")
        cso_s = self._get("can_cuot_so")
        f1pro = self._get("fe_1cu_pro")
        f1soc = self._get("fe_1cu_soc")
        obs = self._get("observacion")

        if not tip: return self.app.toast("Falta tipo.", "error")
        if not nro.isdigit(): return self.app.toast("N° invalido.", "error")
        if not nro_soc.isdigit():
            return self.app.toast("N° de socio invalido.", "error")
        if cod_prov and not cod_prov.isdigit():
            return self.app.toast("Cod. proveedor invalido.", "error")
        if not concepto:
            return self.app.toast("Falta concepto.", "error")
        for lbl_, v in [("Fecha factura", fec_fac),
                        ("1ra cuota prov.", f1pro),
                        ("1ra cuota socio", f1soc)]:
            if not val_fecha(v):
                return self.app.toast(f"{lbl_} invalida (dd/mm/aaaa).",
                                      "error")
        if not fec_fac and not (f1pro and f1soc):
            return self.app.toast("Falta la fecha de factura (o las fechas "
                                  "de primera cuota): sin fecha no se "
                                  "pueden generar las cuotas.", "error")

        imp = parse_monto(imp_s)
        if imp is None or imp <= 0:
            return self.app.toast("Importe invalido.", "error")
        try:
            cpr = int(cpr_s); cso = int(cso_s)
        except ValueError:
            return self.app.toast("Cant. de cuotas invalida.", "error")
        if cpr < 1 or cso < 1 or cpr > 120 or cso > 120:
            return self.app.toast("Cuotas fuera de rango (1-120).",
                                  "error")

        datos = {
            "tip_compro": tip, "nro_compro": int(nro),
            "cod_proveedor": int(cod_prov) if cod_prov else None,
            "nro_socio": int(nro_soc),
            "concepto": concepto, "fec_factura": fecha_db(fec_fac),
            "nro_factura": nro_fac, "importe": imp,
            "can_cuot_pr": cpr, "can_cuot_so": cso,
            "fe_1cu_pro": fecha_db(f1pro), "fe_1cu_soc": fecha_db(f1soc),
            "observacion": obs,
        }
        now_iso = datetime.now().isoformat(timespec="seconds")
        usr = self.app.usuario["usuario"]

        msg = None
        credito_excedido = ""
        try:
            with get_conn() as con:
                soc = con.execute("SELECT nombre, fec_baj FROM socios "
                                   "WHERE nro_socio=?",
                                   (int(nro_soc),)).fetchone()
                if not soc:
                    return self.app.toast(f"Socio {nro_soc} no existe.",
                                          "error")
                if soc["fec_baj"]:
                    if not ConfirmDialog.yes_no("Socio dado de baja",
                            f"El socio {nro_soc} tiene fecha de baja "
                            f"{fecha_ui(soc['fec_baj'])}. Continuar?"):
                        return

                if cod_prov:
                    p = con.execute("SELECT activo FROM proveedores "
                                    "WHERE cod_proveedor=?",
                                    (int(cod_prov),)).fetchone()
                    if not p:
                        return self.app.toast(
                            f"Proveedor {cod_prov} no existe.", "error")
                    if not p["activo"] and not ConfirmDialog.yes_no(
                            "Proveedor dado de baja",
                            f"El proveedor {cod_prov} esta dado de baja. "
                            "Continuar?"):
                        return

                # Que cambia en una modificacion
                regenerar = True
                if self.modo == "MODIFICACION":
                    pag, cob = cuotas_ya_canceladas(
                        con, self.registro_actual["id"])
                    clave = ("importe", "can_cuot_pr", "can_cuot_so",
                             "fe_1cu_pro", "fe_1cu_soc", "fec_factura",
                             "nro_socio", "cod_proveedor")
                    cambia_plan = any(
                        str(self.registro_actual.get(k) or "") !=
                        str(datos[k] or "") for k in clave
                        if k not in ("importe",)) or abs(
                        float(self.registro_actual.get("importe") or 0)
                        - imp) > 0.004
                    if (pag or cob) and cambia_plan:
                        return self.app.toast(
                            f"No se puede cambiar importe, cuotas, fechas, "
                            f"socio ni proveedor: ya hay {pag} cuota(s) "
                            f"pagada(s) y {cob} cobrada(s). Revertilas en "
                            f"Cuotas, o anula y carga de nuevo.", "error")
                    regenerar = cambia_plan

                # Control de credito del socio
                if regenerar:
                    excl = (self.registro_actual["id"]
                            if self.modo == "MODIFICACION" else None)
                    plan = plan_cuotas(imp, cso, parse_fecha(
                        datos["fe_1cu_soc"] or datos["fec_factura"]))
                    avisos = control_credito(con, int(nro_soc), imp, plan,
                                             excl)
                    if avisos:
                        if not ConfirmDialog.yes_no(
                                "Supera el credito del socio",
                                "\n\n".join(avisos) +
                                "\n\nGuardar igual?"):
                            return
                        credito_excedido = " | ".join(avisos)

                if self.modo == "ALTA":
                    ex = con.execute(
                        "SELECT 1 FROM desc_compras_sno "
                        "WHERE tip_compro=? AND nro_compro=?",
                        (tip, int(nro))).fetchone()
                    if ex:
                        return self.app.toast(f"Ya existe {tip}-{nro}.",
                                              "error")
                    campos = list(datos.keys()) + ["estado", "usr_alta",
                                                    "fec_alta"]
                    values = list(datos.values()) + ["ACTIVO", usr, now_iso]
                    ph = ",".join("?" * len(campos))
                    cur = con.execute(
                        f"INSERT INTO desc_compras_sno "
                        f"({','.join(campos)}) VALUES ({ph})", values)
                    desc_id = cur.lastrowid
                    self._generar_cuotas(con, desc_id, datos)
                    msg = (f"Comprobante {tip}-{nro} dado de alta: "
                           f"{cso} cuota(s) al socio"
                           + (f" y {cpr} al proveedor."
                              if datos["cod_proveedor"] else "."))
                else:
                    desc_id = self.registro_actual["id"]
                    sets = ", ".join(f"{k}=?" for k in datos
                                     if k not in ("tip_compro", "nro_compro"))
                    vals = [v for k, v in datos.items()
                            if k not in ("tip_compro", "nro_compro")]
                    vals += [usr, now_iso, desc_id]
                    con.execute(f"UPDATE desc_compras_sno SET {sets}, "
                                f"usr_mod=?, fec_mod=? WHERE id=?", vals)
                    pag = con.execute(
                        "SELECT COUNT(*) AS c FROM cuotas_proveedor "
                        "WHERE desc_compra_id=? AND fec_pago IS NOT NULL",
                        (desc_id,)).fetchone()["c"]
                    cob = con.execute(
                        "SELECT COUNT(*) AS c FROM cuotas_socio "
                        "WHERE desc_compra_id=? AND fec_cobro IS NOT NULL",
                        (desc_id,)).fetchone()["c"]
                    if regenerar and pag == 0 and cob == 0:
                        con.execute("DELETE FROM cuotas_proveedor "
                                    "WHERE desc_compra_id=?", (desc_id,))
                        con.execute("DELETE FROM cuotas_socio "
                                    "WHERE desc_compra_id=?", (desc_id,))
                        self._generar_cuotas(con, desc_id, datos)
                        msg = (f"Comprobante {tip}-{nro} actualizado; "
                               f"cuotas recalculadas.")
                    else:
                        msg = f"Comprobante {tip}-{nro} actualizado."

                row = con.execute(
                    "SELECT id, estado FROM desc_compras_sno "
                    "WHERE tip_compro=? AND nro_compro=?",
                    (tip, int(nro))).fetchone()
        except sqlite3.Error as e:
            return self.app.toast(f"Error de BD: {e}", "error")

        if msg is None: return
        comp = f"{tip}-{nro}"
        if self.modo == "ALTA":
            registrar_auditoria(usr, "ALTA_COMPRA",
                                f"{comp} socio={nro_soc} proveedor="
                                f"{cod_prov or '-'} importe={imp} "
                                f"cuotas={cso}")
        else:
            registrar_auditoria(usr, "MODIFICA_COMPRA",
                                f"{comp} "
                                f"{describir_cambios(self.registro_actual, datos)}")
        if credito_excedido:
            registrar_auditoria(usr, "CREDITO_EXCEDIDO",
                                f"{comp} socio={nro_soc}: {credito_excedido}")
        self.registro_actual = dict(datos)
        if row:
            self.registro_actual["id"] = row["id"]
            self.registro_actual["estado"] = row["estado"]
        self._set_modo("CONSULTA")
        self.app.toast(msg, "success")

    def _generar_cuotas(self, con, desc_id, datos):
        for tabla, n_key, f_key in (
                ("cuotas_proveedor", "can_cuot_pr", "fe_1cu_pro"),
                ("cuotas_socio", "can_cuot_so", "fe_1cu_soc")):
            if tabla == "cuotas_proveedor" and not datos["cod_proveedor"]:
                continue   # sin proveedor no hay nada que pagarle
            f1 = parse_fecha(datos[f_key] or datos["fec_factura"])
            for i, (fv, imp_c) in enumerate(
                    plan_cuotas(datos["importe"], datos[n_key], f1), start=1):
                con.execute(
                    f"INSERT INTO {tabla} (desc_compra_id, nro_cuota, "
                    f"fec_vencimiento, importe) VALUES (?, ?, ?, ?)",
                    (desc_id, i, fv.strftime("%Y-%m-%d"), imp_c))


class _ProxyEntry:
    """Wrapper para tratar un CTkEntry pelado como si fuera un Field."""
    def __init__(self, entry):
        self.entry = entry
    def get(self):
        return self.entry.get().strip()
    def set(self, value):
        state = self.entry.cget("state")
        self.entry.configure(state="normal")
        self.entry.delete(0, "end")
        if value is not None:
            self.entry.insert(0, str(value))
        self.entry.configure(state=state)
    def set_state(self, state):
        try: self.entry.configure(state=state)
        except Exception: pass
    def bind_key(self, key, cb):
        self.entry.bind(key, cb)
    def focus(self):
        self.entry.focus_set()

# =====================================================================
#  PANEL: CUOTAS (pagos a proveedor / cobros a socio)
# =====================================================================
class PanelCuotas(ctk.CTkFrame):
    ESTADOS_FILTRO = ["PENDIENTE", "TODAS", "PAGADA/COBRADA", "ANULADA"]

    def __init__(self, master, app, titulo="Cuotas", tipo="PROVEEDOR",
                 **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.tipo = tipo
        self.filas_actuales = []
        self.sel_actual = None

        app.set_breadcrumb("Movimientos", "Pagos y cobranzas")
        app.set_badge("")

        self._build_toolbar()
        self._build_tabla()
        self._build_action_bar()
        self._refrescar()

    def _build_toolbar(self):
        tb = Card(self)
        tb.pack(fill="x", pady=(0, 12))
        wrap = ctk.CTkFrame(tb, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)

        tabs = ctk.CTkFrame(wrap, fg_color="transparent")
        tabs.pack(side="left")
        self.btn_prov = ctk.CTkButton(
            tabs, text="A proveedor (egresos)",
            font=F(13, "bold"), height=36, corner_radius=6,
            fg_color=COLOR_ACCENT if self.tipo == "PROVEEDOR"
                    else COLOR_CARD,
            text_color="white" if self.tipo == "PROVEEDOR"
                       else COLOR_TEXT,
            border_color=COLOR_BORDER_STRONG, border_width=1,
            hover_color=COLOR_ACCENT_HOVER,
            command=lambda: self._cambiar_tipo("PROVEEDOR"))
        self.btn_prov.pack(side="left", padx=(0, 4))
        self.btn_soc = ctk.CTkButton(
            tabs, text="A socio (ingresos)",
            font=F(13, "bold"), height=36, corner_radius=6,
            fg_color=COLOR_ACCENT if self.tipo == "SOCIO" else COLOR_CARD,
            text_color="white" if self.tipo == "SOCIO" else COLOR_TEXT,
            border_color=COLOR_BORDER_STRONG, border_width=1,
            hover_color=COLOR_ACCENT_HOVER,
            command=lambda: self._cambiar_tipo("SOCIO"))
        self.btn_soc.pack(side="left")

        filters = ctk.CTkFrame(wrap, fg_color="transparent")
        filters.pack(side="right")
        self.e_q = ctk.CTkEntry(
            filters, width=200, font=F(13),
            fg_color=COLOR_CARD, border_color=COLOR_BORDER,
            text_color=COLOR_TEXT, height=36, corner_radius=6,
            placeholder_text="Buscar...")
        self.e_q.pack(side="left", padx=(0, 8))
        self.e_q.bind("<KeyRelease>", lambda e: self._refrescar())

        self.var_estado = ctk.StringVar(value="PENDIENTE")
        self.cb_estado = ctk.CTkComboBox(
            filters, values=self.ESTADOS_FILTRO,
            variable=self.var_estado, width=150,
            font=F(13), dropdown_font=F(13),
            fg_color=COLOR_CARD, border_color=COLOR_BORDER,
            button_color=COLOR_BORDER, button_hover_color=COLOR_ACCENT,
            text_color=COLOR_TEXT, height=36, corner_radius=6,
            command=lambda v: self._refrescar(), state="readonly")
        self.cb_estado.pack(side="left")

    def _cambiar_tipo(self, tipo):
        self.tipo = tipo
        self.btn_prov.configure(
            fg_color=COLOR_ACCENT if tipo == "PROVEEDOR" else COLOR_CARD,
            text_color="white" if tipo == "PROVEEDOR" else COLOR_TEXT)
        self.btn_soc.configure(
            fg_color=COLOR_ACCENT if tipo == "SOCIO" else COLOR_CARD,
            text_color="white" if tipo == "SOCIO" else COLOR_TEXT)
        self._refrescar()

    def _build_tabla(self):
        card = Card(self)
        card.pack(fill="both", expand=True, pady=6)
        wrap = ctk.CTkFrame(card, fg_color="transparent")
        wrap.pack(fill="both", expand=True, padx=14, pady=14)

        self.tabla = DataTable(wrap, columns=[
            (110, "Comprobante",  "comp"),
            (60,  "Cuota",        "cuota"),
            (240, "Contraparte",  "nombre"),
            (110, "Vencimiento",  "venc"),
            (120, "Importe",      "importe"),
            (100, "Estado",       "estado"),
        ], on_row_click=self._seleccionar_key)
        self.tabla.pack(fill="both", expand=True)

        self.lbl_total = ctk.CTkLabel(card, text="",
                                       font=F(12, "bold"),
                                       text_color=COLOR_TEXT_MUTED)
        self.lbl_total.pack(pady=(0, 12))

    def _build_action_bar(self):
        bar = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                           border_color=COLOR_BORDER, border_width=1,
                           corner_radius=10, height=72)
        bar.pack(fill="x", pady=(6, 8))
        bar.pack_propagate(False)
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=16)

        b_rev = DangerButton(inner, "Revertir", "\u21BA",
                             command=self._revertir, width=130)
        b_rev.pack(side="left", padx=4)
        deshabilitar_sin_nivel(self.app, [b_rev], NIVEL_ADMIN)

        self.btn_registrar = PrimaryButton(
            inner, "Registrar pago/cobro", "\u2713",
            command=self._registrar, width=220)
        self.btn_registrar.pack(side="right", padx=4)
        deshabilitar_sin_nivel(self.app, [self.btn_registrar])

    def _seleccionar_key(self, key):
        for r in self.filas_actuales:
            if r["id"] == key:
                self.sel_actual = r
                self.app.toast(
                    f"Seleccionada cuota {r['nro_cuota']} de "
                    f"{r['tip_compro']}-{r['nro_compro']}.", "info")
                return

    def _refrescar(self):
        q = f"%{self.e_q.get().strip().upper()}%"
        filtro_estado = self.var_estado.get()
        tabla = "cuotas_proveedor" if self.tipo == "PROVEEDOR" \
                else "cuotas_socio"
        campo_fecha = "fec_pago" if self.tipo == "PROVEEDOR" else "fec_cobro"
        campo_join = "cod_proveedor" if self.tipo == "PROVEEDOR" \
                    else "nro_socio"
        tabla_join = "proveedores" if self.tipo == "PROVEEDOR" else "socios"
        campo_nombre = "razon_social" if self.tipo == "PROVEEDOR" \
                       else "nombre"

        sql = (f"SELECT c.id, c.nro_cuota, c.fec_vencimiento, c.importe, "
              f"c.estado, c.{campo_fecha} AS fecha_mov, "
              f"d.tip_compro, d.nro_compro, d.estado AS estado_compro, "
              f"j.{campo_nombre} AS nombre "
              f"FROM {tabla} c "
              f"JOIN desc_compras_sno d ON d.id = c.desc_compra_id "
              f"LEFT JOIN {tabla_join} j "
              f"       ON j.{campo_join} = d.{campo_join} "
              f"WHERE (UPPER(d.tip_compro || '-' || d.nro_compro) LIKE ? "
              f"       OR UPPER(COALESCE(j.{campo_nombre},'')) LIKE ?)")
        params = [q, q]
        if filtro_estado == "PENDIENTE":
            sql += " AND c.estado = 'PENDIENTE'"
        elif filtro_estado == "PAGADA/COBRADA":
            sql += " AND c.estado IN ('PAGADA', 'COBRADA')"
        elif filtro_estado == "ANULADA":
            sql += " AND c.estado = 'ANULADA'"
        sql += (" ORDER BY c.fec_vencimiento, d.tip_compro, d.nro_compro, "
                "c.nro_cuota LIMIT 1000")

        with get_conn() as con:
            rows = con.execute(sql, params).fetchall()
        self.filas_actuales = [dict(r) for r in rows]
        self.tabla.clear()
        for r in self.filas_actuales:
            estado_kind = {
                "PENDIENTE": "warning",
                "PAGADA":    "success",
                "COBRADA":   "success",
                "ANULADA":   "danger",
            }.get(r["estado"], "info")
            self.tabla.add_row({
                "comp":    f"{r['tip_compro']}-{r['nro_compro']}",
                "cuota":   r["nro_cuota"],
                "nombre":  (r["nombre"] or "")[:36],
                "venc":    fecha_ui(r["fec_vencimiento"]),
                "importe": fmt_moneda(r["importe"]),
                "estado":  r["estado"],
            }, badges={"estado": estado_kind}, key=r["id"])

        self.lbl_total.configure(
            text=f"Total: {len(self.filas_actuales)} cuotas")
        self.sel_actual = None

    def _registrar(self):
        if not self.app.puede(NIVEL_OPERAR, "registrar pagos ni cobros"):
            return
        if not self.sel_actual:
            self.app.toast("Seleccione una cuota de la lista.", "warning")
            return
        fila = self.sel_actual
        if fila["estado_compro"] == "ANULADO":
            self.app.toast("El comprobante esta anulado.", "error"); return
        if fila["estado"] != "PENDIENTE":
            self.app.toast(f"La cuota ya esta en estado {fila['estado']}.",
                           "warning"); return
        verbo = "pago a proveedor" if self.tipo == "PROVEEDOR" \
                else "cobro a socio"
        if not ConfirmDialog.yes_no("Confirmar",
                f"Registrar el {verbo} de la cuota "
                f"{fila['nro_cuota']} ({fmt_moneda(fila['importe'])}) del "
                f"comprobante {fila['tip_compro']}-{fila['nro_compro']}?"):
            return
        hoy = hoy_db()
        tabla = "cuotas_proveedor" if self.tipo == "PROVEEDOR" \
                else "cuotas_socio"
        campo_fecha = "fec_pago" if self.tipo == "PROVEEDOR" else "fec_cobro"
        estado_nuevo = "PAGADA" if self.tipo == "PROVEEDOR" else "COBRADA"
        with get_conn() as con:
            con.execute(f"UPDATE {tabla} SET {campo_fecha}=?, estado=? "
                       f"WHERE id=?", (hoy, estado_nuevo, fila["id"]))
        registrar_auditoria(
            self.app.usuario["usuario"],
            "PAGO_CUOTA" if self.tipo == "PROVEEDOR" else "COBRO_CUOTA",
            f"{tabla} id={fila['id']} "
            f"comprobante={fila['tip_compro']}-{fila['nro_compro']} "
            f"cuota={fila['nro_cuota']} importe={fila['importe']}")
        self.app.toast(f"Cuota {fila['nro_cuota']} marcada como "
                       f"{estado_nuevo}.", "success")
        self._refrescar()

    def _revertir(self):
        if not self.app.puede(NIVEL_ADMIN, "revertir pagos ni cobros "
                              "(pedile a un ADMIN)"):
            return
        if not self.sel_actual:
            self.app.toast("Seleccione una cuota.", "warning"); return
        fila = self.sel_actual
        if fila["estado"] == "ANULADA":
            self.app.toast("Esa cuota esta anulada.", "error"); return
        if fila["estado"] == "PENDIENTE":
            self.app.toast("Esa cuota ya esta pendiente.", "warning")
            return
        if not ConfirmDialog.yes_no("Confirmar",
                f"Revertir el pago/cobro de la cuota "
                f"{fila['nro_cuota']} y dejarla pendiente?"):
            return
        tabla = "cuotas_proveedor" if self.tipo == "PROVEEDOR" \
                else "cuotas_socio"
        campo_fecha = "fec_pago" if self.tipo == "PROVEEDOR" else "fec_cobro"
        # Si la compra esta anulada, la cuota vuelve a ANULADA (no a
        # pendiente), para que no aparezca como deuda.
        nuevo = "ANULADA" if fila.get("estado_compro") == "ANULADO" \
            else "PENDIENTE"
        with get_conn() as con:
            con.execute(f"UPDATE {tabla} SET {campo_fecha}=NULL, "
                       f"estado=? WHERE id=?", (nuevo, fila["id"]))
        registrar_auditoria(
            self.app.usuario["usuario"],
            "REVERTIR_PAGO" if self.tipo == "PROVEEDOR"
            else "REVERTIR_COBRO",
            f"{tabla} id={fila['id']}")
        self.app.toast(f"Cuota {fila['nro_cuota']} vuelta a pendiente.",
                       "warning")
        self._refrescar()


# =====================================================================
#  EXPORTAR REPORTES (PDF / Excel-CSV)
# =====================================================================
# Columna: (titulo, clave, ancho_relativo, tipo)  tipo: txt|fecha|moneda|int
def _fmt_celda(valor, tipo, para_csv=False):
    if valor is None:
        return ""
    if tipo == "fecha":
        return fecha_ui(valor)
    if tipo == "moneda":
        return fmt_numero_csv(valor) if para_csv else fmt_moneda(valor)
    return str(valor)


def exportar_csv(archivo, columnas, filas, totales=None):
    """CSV separado por ';' con BOM, para que Excel en espanol lo abra
    directo con acentos y decimales con coma."""
    with open(archivo, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow([c[0] for c in columnas])
        for fila in filas:
            w.writerow([_fmt_celda(fila.get(c[1]), c[3], True)
                        for c in columnas])
        if totales:
            w.writerow([])
            for etiqueta, valor in totales:
                w.writerow([etiqueta, _fmt_celda(valor, "moneda", True)
                            if isinstance(valor, (int, float))
                            else valor])


def exportar_pdf(archivo, titulo, subtitulo, columnas, filas, totales=None):
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib.units import cm
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.platypus import (SimpleDocTemplate, Table, TableStyle,
                                    Paragraph, Spacer)

    horizontal = len(columnas) > 6
    pagina = landscape(A4) if horizontal else A4
    margen = 1.5 * cm
    doc = SimpleDocTemplate(archivo, pagesize=pagina, leftMargin=margen,
                            rightMargin=margen, topMargin=margen,
                            bottomMargin=margen, title=titulo,
                            author=APP_NOMBRE)
    estilos = getSampleStyleSheet()
    st_ent = ParagraphStyle("ent", parent=estilos["Normal"], fontSize=9,
                            textColor=colors.HexColor(COLOR_TEXT_MUTED))
    st_tit = ParagraphStyle("tit", parent=estilos["Title"], fontSize=16,
                            alignment=0, spaceAfter=2)
    st_sub = ParagraphStyle("sub", parent=estilos["Normal"], fontSize=10,
                            textColor=colors.HexColor(COLOR_TEXT_MUTED))
    st_cel = ParagraphStyle("cel", parent=estilos["Normal"], fontSize=8,
                            leading=10)

    def esc(t):
        return (str(t).replace("&", "&amp;").replace("<", "&lt;")
                .replace(">", "&gt;"))

    historia = []
    ent = nombre_entidad()
    historia.append(Paragraph(esc(ent or APP_NOMBRE), st_ent))
    historia.append(Paragraph(esc(titulo), st_tit))
    if subtitulo:
        historia.append(Paragraph(esc(subtitulo), st_sub))
    historia.append(Paragraph(
        f"Emitido el {datetime.now().strftime('%d/%m/%Y %H:%M')}", st_sub))
    historia.append(Spacer(1, 0.4 * cm))

    ancho_util = pagina[0] - 2 * margen
    total_rel = sum(c[2] for c in columnas)
    anchos = [ancho_util * c[2] / total_rel for c in columnas]
    datos = [[c[0] for c in columnas]]
    for fila in filas:
        datos.append([Paragraph(esc(_fmt_celda(fila.get(c[1]), c[3])),
                                st_cel) if c[3] == "txt"
                      else _fmt_celda(fila.get(c[1]), c[3])
                      for c in columnas])
    if not filas:
        datos.append(["(sin datos)"] + [""] * (len(columnas) - 1))
    tabla = Table(datos, colWidths=anchos, repeatRows=1)
    estilo = [
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor(COLOR_SIDEBAR)),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, -1), 8),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1),
         [colors.white, colors.HexColor("#f3f4f6")]),
        ("LINEBELOW", (0, 0), (-1, 0), 0.5, colors.HexColor(COLOR_SIDEBAR)),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
        ("TOPPADDING", (0, 0), (-1, -1), 4),
    ]
    for i, c in enumerate(columnas):
        if c[3] in ("moneda", "int"):
            estilo.append(("ALIGN", (i, 0), (i, -1), "RIGHT"))
    tabla.setStyle(TableStyle(estilo))
    historia.append(tabla)

    if totales:
        historia.append(Spacer(1, 0.4 * cm))
        tdatos = [[esc(e), _fmt_celda(v, "moneda")
                   if isinstance(v, (int, float)) else esc(v)]
                  for e, v in totales]
        tt = Table(tdatos, colWidths=[6 * cm, 4 * cm], hAlign="RIGHT")
        tt.setStyle(TableStyle([
            ("FONTNAME", (0, 0), (-1, -1), "Helvetica-Bold"),
            ("FONTSIZE", (0, 0), (-1, -1), 9),
            ("ALIGN", (1, 0), (1, -1), "RIGHT"),
            ("LINEABOVE", (0, 0), (-1, 0), 0.5, colors.grey),
        ]))
        historia.append(tt)

    def pie(canv, d):
        canv.saveState()
        canv.setFont("Helvetica", 7)
        canv.setFillColor(colors.grey)
        canv.drawString(margen, 0.8 * cm, f"{APP_NOMBRE} {APP_VERSION}")
        canv.drawRightString(pagina[0] - margen, 0.8 * cm,
                             f"Pagina {d.page}")
        canv.restoreState()

    doc.build(historia, onFirstPage=pie, onLaterPages=pie)


def exportar_reporte(app, titulo, subtitulo, columnas, filas, totales=None,
                     nombre_archivo="reporte", accion_auditoria=None):
    """Pregunta donde guardar y exporta a PDF o CSV segun la extension
    elegida."""
    if not filas:
        app.toast("No hay datos para exportar.", "warning")
        return None
    archivo = filedialog.asksaveasfilename(
        title=f"Exportar - {titulo}",
        defaultextension=".pdf",
        filetypes=[("PDF", "*.pdf"), ("Excel (CSV)", "*.csv")],
        initialfile=f"{nombre_archivo}_{datetime.now():%Y%m%d}.pdf")
    if not archivo:
        return None
    es_csv = archivo.lower().endswith(".csv")
    try:
        if es_csv:
            exportar_csv(archivo, columnas, filas, totales)
        else:
            if not _importar_reportlab():
                return None
            exportar_pdf(archivo, titulo, subtitulo, columnas, filas,
                         totales)
    except PermissionError:
        ConfirmDialog.error("Exportar", "No se pudo guardar: el archivo "
                            "esta abierto en otro programa (Excel?). "
                            "Cerralo y proba de nuevo.")
        return None
    except Exception as e:
        ConfirmDialog.error("Exportar", f"No se pudo exportar:\n{e}")
        return None
    if accion_auditoria and app.usuario:
        registrar_auditoria(app.usuario["usuario"], accion_auditoria,
                            f"{titulo} {subtitulo or ''} -> {archivo}")
    app.toast("Reporte exportado.", "success")
    if ConfirmDialog.yes_no("Exportar", f"Guardado en:\n{archivo}\n\n"
                            "Abrir el archivo?"):
        abrir_carpeta(archivo)
    return archivo


# =====================================================================
#  PANEL: LIQUIDACION MENSUAL DE DESCUENTOS
# =====================================================================
class PanelLiquidacion(ctk.CTkFrame):
    """Cuotas de socios a descontar en un mes: resumen por socio,
    exportacion para el empleador/banco y cobro de todas juntas."""

    def __init__(self, master, app, titulo="Liquidacion", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.filas = []          # cuotas incluidas (detalle)
        self.resumen = []        # una fila por socio
        app.set_breadcrumb("Movimientos", "Liquidacion mensual de descuentos")
        app.set_badge("")

        hoy = datetime.now()
        tb = Card(self)
        tb.pack(fill="x", pady=(0, 12))
        wrap = ctk.CTkFrame(tb, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)

        ctk.CTkLabel(wrap, text="Mes", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 6))
        self.meses = [m.capitalize() for m in MESES]
        self.var_mes = ctk.StringVar(value=self.meses[hoy.month - 1])
        ctk.CTkComboBox(wrap, values=self.meses, variable=self.var_mes,
                        width=140, font=F(13), dropdown_font=F(13),
                        fg_color=COLOR_CARD, border_color=COLOR_BORDER,
                        button_color=COLOR_BORDER,
                        button_hover_color=COLOR_ACCENT,
                        text_color=COLOR_TEXT, height=36, corner_radius=6,
                        command=lambda v: self._refrescar(),
                        state="readonly").pack(side="left", padx=(0, 12))
        ctk.CTkLabel(wrap, text="Año", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 6))
        anios = [str(a) for a in range(hoy.year - 3, hoy.year + 4)]
        self.var_anio = ctk.StringVar(value=str(hoy.year))
        ctk.CTkComboBox(wrap, values=anios, variable=self.var_anio,
                        width=100, font=F(13), dropdown_font=F(13),
                        fg_color=COLOR_CARD, border_color=COLOR_BORDER,
                        button_color=COLOR_BORDER,
                        button_hover_color=COLOR_ACCENT,
                        text_color=COLOR_TEXT, height=36, corner_radius=6,
                        command=lambda v: self._refrescar(),
                        state="readonly").pack(side="left", padx=(0, 16))
        self.var_atrasadas = ctk.BooleanVar(value=True)
        ctk.CTkCheckBox(wrap, text="Incluir cuotas atrasadas",
                        variable=self.var_atrasadas, font=F(12),
                        text_color=COLOR_TEXT,
                        command=self._refrescar).pack(side="left")

        # Metricas
        self.metrics = ctk.CTkFrame(self, fg_color="transparent")
        self.metrics.pack(fill="x", pady=6)
        self.metrics.grid_columnconfigure((0, 1, 2), weight=1)
        self._m_socios = self._metric(0, "Socios a descontar", COLOR_ACCENT)
        self._m_cuotas = self._metric(1, "Cuotas", COLOR_TEXT)
        self._m_total = self._metric(2, "Total a descontar", COLOR_SUCCESS)

        card = Card(self, title="Detalle por socio")
        card.pack(fill="both", expand=True, pady=6)
        w2 = ctk.CTkFrame(card, fg_color="transparent")
        w2.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        self.tabla = DataTable(w2, columns=[
            (70,  "Nro",    "nro"),
            (250, "Socio",  "nombre"),
            (120, "CUIL",   "cuil"),
            (190, "CBU",    "cbu"),
            (60,  "Cuotas", "cant"),
            (120, "Total",  "total"),
        ])
        self.tabla.pack(fill="both", expand=True)

        bar = Card(self)
        bar.pack(fill="x", pady=(12, 8))
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="x", padx=18, pady=14)
        SecondaryButton(inner, "Exportar resumen", "⤓",
                        command=self._exportar_resumen,
                        width=190).pack(side="left", padx=4)
        SecondaryButton(inner, "Exportar detalle", "⤓",
                        command=self._exportar_detalle,
                        width=180).pack(side="left", padx=4)
        self.btn_cobrar = PrimaryButton(inner, "Marcar todo como cobrado",
                                        "✓", command=self._cobrar,
                                        width=260)
        self.btn_cobrar.pack(side="right", padx=4)
        deshabilitar_sin_nivel(self.app, [self.btn_cobrar])

        self._refrescar()

    def _metric(self, col, titulo, color):
        c = ctk.CTkFrame(self.metrics, fg_color=COLOR_CARD,
                         border_color=COLOR_BORDER, border_width=1,
                         corner_radius=10)
        c.grid(row=0, column=col, sticky="ew", padx=6)
        ctk.CTkLabel(c, text=titulo.upper(), font=F(10, "bold"),
                     text_color=COLOR_TEXT_MUTED,
                     anchor="w").pack(fill="x", padx=18, pady=(14, 4))
        lbl = ctk.CTkLabel(c, text="0", font=F(24, "bold"),
                           text_color=color, anchor="w")
        lbl.pack(fill="x", padx=18, pady=(0, 14))
        return lbl

    def _periodo(self):
        mes = self.meses.index(self.var_mes.get()) + 1
        return int(self.var_anio.get()), mes

    def _periodo_txt(self):
        anio, mes = self._periodo()
        txt = f"{self.var_mes.get()} {anio}"
        if self.var_atrasadas.get():
            txt += " (incluye cuotas atrasadas)"
        return txt

    def _refrescar(self):
        anio, mes = self._periodo()
        clave = f"{anio:04d}-{mes:02d}"
        cond = ("substr(c.fec_vencimiento, 1, 7) <= ?"
                if self.var_atrasadas.get()
                else "substr(c.fec_vencimiento, 1, 7) = ?")
        with get_conn() as con:
            rows = con.execute(
                "SELECT c.id, c.nro_cuota, c.fec_vencimiento, c.importe, "
                "d.tip_compro, d.nro_compro, d.concepto, d.nro_socio, "
                "s.nombre, s.cuil, s.cbu "
                "FROM cuotas_socio c "
                "JOIN desc_compras_sno d ON d.id = c.desc_compra_id "
                "LEFT JOIN socios s ON s.nro_socio = d.nro_socio "
                "WHERE c.estado = 'PENDIENTE' AND d.estado = 'ACTIVO' "
                "AND COALESCE(c.fec_vencimiento, '') <> '' AND " + cond +
                " ORDER BY d.nro_socio, c.fec_vencimiento, c.nro_cuota",
                (clave,)).fetchall()
        self.filas = [dict(r, comp=f"{r['tip_compro']}-{r['nro_compro']}")
                      for r in rows]
        por_socio = {}
        for r in self.filas:
            s = por_socio.setdefault(r["nro_socio"], {
                "nro_socio": r["nro_socio"], "nombre": r["nombre"] or "",
                "cuil": r["cuil"] or "", "cbu": r["cbu"] or "",
                "cant": 0, "total": 0.0})
            s["cant"] += 1
            s["total"] = round(s["total"] + r["importe"], 2)
        self.resumen = list(por_socio.values())

        self.tabla.clear()
        for s in self.resumen:
            self.tabla.add_row({
                "nro": s["nro_socio"], "nombre": s["nombre"][:34],
                "cuil": s["cuil"], "cbu": s["cbu"], "cant": s["cant"],
                "total": fmt_moneda(s["total"])})
        total = sum(s["total"] for s in self.resumen)
        self._m_socios.configure(text=str(len(self.resumen)))
        self._m_cuotas.configure(text=str(len(self.filas)))
        self._m_total.configure(text=fmt_moneda(total))

    def _exportar_resumen(self):
        anio, mes = self._periodo()
        total = sum(s["total"] for s in self.resumen)
        exportar_reporte(
            self.app, "Liquidacion de descuentos", self._periodo_txt(),
            [("Nro socio", "nro_socio", 1.4, "int"),
             ("Socio", "nombre", 5, "txt"),
             ("CUIL", "cuil", 2.6, "txt"),
             ("CBU", "cbu", 4, "txt"),
             ("Cuotas", "cant", 1.2, "int"),
             ("Total", "total", 2.4, "moneda")],
            self.resumen,
            [("Socios", str(len(self.resumen))),
             ("Total a descontar", total)],
            f"liquidacion_{anio}{mes:02d}", "EXPORTA_LIQUIDACION")

    def _exportar_detalle(self):
        anio, mes = self._periodo()
        total = sum(r["importe"] for r in self.filas)
        exportar_reporte(
            self.app, "Liquidacion de descuentos - detalle",
            self._periodo_txt(),
            [("Nro socio", "nro_socio", 1.4, "int"),
             ("Socio", "nombre", 4.5, "txt"),
             ("CUIL", "cuil", 2.6, "txt"),
             ("Comprobante", "comp", 2, "txt"),
             ("Concepto", "concepto", 4, "txt"),
             ("Cuota", "nro_cuota", 1, "int"),
             ("Vencimiento", "fec_vencimiento", 2, "fecha"),
             ("Importe", "importe", 2.2, "moneda")],
            self.filas, [("Total a descontar", total)],
            f"liquidacion_detalle_{anio}{mes:02d}", "EXPORTA_LIQUIDACION")

    def _cobrar(self):
        if not self.app.puede(NIVEL_OPERAR, "registrar cobros"): return
        if not self.filas:
            self.app.toast("No hay cuotas para cobrar en ese periodo.",
                           "warning"); return
        total = sum(r["importe"] for r in self.filas)
        if not ConfirmDialog.yes_no(
                "Cobrar liquidacion",
                f"Se van a marcar como COBRADAS {len(self.filas)} cuotas "
                f"de {len(self.resumen)} socios, por un total de "
                f"{fmt_moneda(total)}.\n\nPeriodo: {self._periodo_txt()}\n\n"
                "Hacelo solo cuando el empleador o el banco ya hayan "
                "transferido el dinero. Continuar?"):
            return
        hoy = hoy_db()
        ids = [r["id"] for r in self.filas]
        with get_conn() as con:
            con.executemany(
                "UPDATE cuotas_socio SET estado='COBRADA', fec_cobro=? "
                "WHERE id=? AND estado='PENDIENTE'",
                [(hoy, i) for i in ids])
        registrar_auditoria(
            self.app.usuario["usuario"], "COBRO_LIQUIDACION",
            f"periodo={self._periodo_txt()} cuotas={len(ids)} "
            f"socios={len(self.resumen)} total={round(total, 2)}")
        self.app.toast(f"{len(ids)} cuotas marcadas como cobradas.",
                       "success")
        self._refrescar()


# =====================================================================
#  PANEL: CONFIGURACION
# =====================================================================
class PanelConfiguracion(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Configuracion", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        app.set_breadcrumb("Administracion", "Configuracion")
        app.set_badge("")

        card = Card(self, title="Datos de la entidad")
        card.pack(fill="x", pady=(0, 12))
        g = ctk.CTkFrame(card, fg_color="transparent")
        g.pack(fill="x", padx=18, pady=(0, 18))
        g.grid_columnconfigure(0, weight=1)
        self.f_nombre = Field(g, "Nombre de la mutual (aparece en el menu, "
                                 "el login, las credenciales y los reportes)",
                              width=600)
        self.f_nombre.grid(row=0, column=0, sticky="ew", padx=6, pady=6)
        self.f_nombre.set(nombre_entidad())
        PrimaryButton(g, "Guardar", "✓", command=self._guardar,
                      width=160).grid(row=1, column=0, sticky="e", padx=6,
                                      pady=(8, 0))

        card2 = Card(self, title="Informacion del sistema")
        card2.pack(fill="x", pady=6)
        info = ctk.CTkFrame(card2, fg_color="transparent")
        info.pack(fill="x", padx=18, pady=(0, 18))
        for etq, val in (("Programa:", f"{APP_NOMBRE} {APP_VERSION}"),
                         ("Base de datos:", DB_PATH),
                         ("Backups automaticos:", BACKUP_DIR)):
            row = ctk.CTkFrame(info, fg_color="transparent")
            row.pack(fill="x", pady=2)
            ctk.CTkLabel(row, text=etq, font=F(12),
                         text_color=COLOR_TEXT_MUTED, width=180,
                         anchor="w").pack(side="left")
            ctk.CTkLabel(row, text=val, font=F(12, "bold"),
                         text_color=COLOR_TEXT, anchor="w").pack(
                         side="left", fill="x", expand=True)

    def _guardar(self):
        if not self.app.puede(NIVEL_ADMIN, "cambiar la configuracion"):
            return
        nuevo = self.f_nombre.get().strip()
        anterior = nombre_entidad()
        set_config("entidad_nombre", nuevo)
        registrar_auditoria(self.app.usuario["usuario"], "CONFIGURACION",
                            f"nombre entidad: {anterior or '-'} -> "
                            f"{nuevo or '-'}")
        self.app.actualizar_entidad()
        self.app.toast("Configuracion guardada.", "success")


# =====================================================================
#  PANEL: CONSULTAS
# =====================================================================
class PanelConsultas(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Consultas", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        app.set_breadcrumb("Reportes", "Consultas")
        app.set_badge("")

        card = Card(self, title="Reportes disponibles")
        card.pack(fill="x", pady=8)
        inner = ctk.CTkFrame(card, fg_color="transparent")
        inner.pack(fill="x", padx=18, pady=(0, 18))
        inner.grid_columnconfigure((0, 1), weight=1)

        self._crear_tarjeta(inner, 0, 0, "Estado de cuenta de socio",
                            "Cuotas a cobrar a un socio: pendiente, "
                            "cobrado y anulado.",
                            "\u25CE", COLOR_ACCENT,
                            lambda: self.app._on_sidebar_click(
                                "estado_cta"))
        self._crear_tarjeta(inner, 0, 1, "Cuotas vencidas / a vencer",
                            "Vencidas y proximas a vencer, a pagar y "
                            "a cobrar.",
                            "\u2691", COLOR_WARNING,
                            lambda: self.app._on_sidebar_click(
                                "cta_vencidas"))

    def _crear_tarjeta(self, parent, row, col, titulo, subtitulo, icon,
                       icon_color, cmd):
        card = ctk.CTkFrame(parent, fg_color=COLOR_CARD,
                            border_color=COLOR_BORDER, border_width=1,
                            corner_radius=10, cursor="hand2")
        card.grid(row=row, column=col, sticky="ew", padx=6, pady=6)

        inner = ctk.CTkFrame(card, fg_color="transparent")
        inner.pack(fill="x", padx=18, pady=18)

        ctk.CTkLabel(inner, text=icon, font=F(32),
                     text_color=icon_color).pack(anchor="w")
        ctk.CTkLabel(inner, text=titulo, font=F(15, "bold"),
                     text_color=COLOR_TEXT,
                     anchor="w").pack(anchor="w", pady=(4, 2))
        ctk.CTkLabel(inner, text=subtitulo, font=F(12),
                     text_color=COLOR_TEXT_MUTED,
                     wraplength=380, anchor="w",
                     justify="left").pack(anchor="w")

        for w in (card, inner) + tuple(inner.winfo_children()):
            w.bind("<Button-1>", lambda e: cmd())
            w.bind("<Enter>", lambda e, c=card: c.configure(
                border_color=COLOR_ACCENT))
            w.bind("<Leave>", lambda e, c=card: c.configure(
                border_color=COLOR_BORDER))


# =====================================================================
#  PANEL: ESTADO DE CUENTA DE SOCIO
# =====================================================================
class PanelEstadoCuenta(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Estado de cuenta",
                 nro_inicial=None, **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        app.set_breadcrumb("Reportes", "Estado de cuenta de socio")
        app.set_badge("")

        tb = Card(self)
        tb.pack(fill="x", pady=(0, 12))
        wrap = ctk.CTkFrame(tb, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)

        ctk.CTkLabel(wrap, text="Nro. socio", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 8))
        self.e_nro = ctk.CTkEntry(wrap, width=140, font=F(14, "bold"),
                                   fg_color=COLOR_CARD,
                                   border_color=COLOR_BORDER,
                                   text_color=COLOR_TEXT, height=38,
                                   corner_radius=6,
                                   placeholder_text="1001")
        self.e_nro.pack(side="left", padx=(0, 8))
        self.e_nro.bind("<Return>", lambda e: self._buscar())
        SecondaryButton(wrap, "Buscar", "\u2315",
                        command=self._buscar,
                        width=120).pack(side="left", padx=4)
        AccentButton(wrap, "Exportar", "\u2913", command=self._exportar,
                     width=130).pack(side="right", padx=4)
        self._datos_export = None

        self.lbl_socio = ctk.CTkLabel(wrap,
                                       text="(ingresa un socio)",
                                       font=F(13),
                                       text_color=COLOR_TEXT_MUTED)
        self.lbl_socio.pack(side="left", padx=16)

        # Metricas
        self.metrics = ctk.CTkFrame(self, fg_color="transparent")
        self.metrics.pack(fill="x", pady=6)
        self.metrics.grid_columnconfigure((0, 1, 2), weight=1)
        self._m_pendiente = self._metric_card(0, "Pendiente de cobro",
                                               "$0.00", COLOR_WARNING)
        self._m_cobrado   = self._metric_card(1, "Ya cobrado",
                                               "$0.00", COLOR_SUCCESS)
        self._m_anulado   = self._metric_card(2, "Anulado",
                                               "$0.00", COLOR_TEXT_MUTED)

        # Tabla
        card = Card(self, title="Detalle de cuotas")
        card.pack(fill="both", expand=True, pady=6)
        wrap2 = ctk.CTkFrame(card, fg_color="transparent")
        wrap2.pack(fill="both", expand=True, padx=14, pady=(0, 14))

        self.tabla = DataTable(wrap2, columns=[
            (110, "Comprobante", "comp"),
            (240, "Concepto",    "concepto"),
            (60,  "Cuota",       "cuota"),
            (110, "Vencimiento", "venc"),
            (120, "Importe",     "importe"),
            (100, "Estado",      "estado"),
        ])
        self.tabla.pack(fill="both", expand=True)

        if nro_inicial:
            self.e_nro.insert(0, str(nro_inicial))
            self.after(50, self._buscar)

    def _metric_card(self, col, titulo, valor, color):
        c = ctk.CTkFrame(self.metrics, fg_color=COLOR_CARD,
                         border_color=COLOR_BORDER, border_width=1,
                         corner_radius=10)
        c.grid(row=0, column=col, sticky="ew", padx=6)
        ctk.CTkLabel(c, text=titulo.upper(), font=F(10, "bold"),
                     text_color=COLOR_TEXT_MUTED,
                     anchor="w").pack(fill="x", padx=18, pady=(14, 4))
        lbl = ctk.CTkLabel(c, text=valor, font=F(24, "bold"),
                           text_color=color, anchor="w")
        lbl.pack(fill="x", padx=18, pady=(0, 14))
        return lbl

    def _buscar(self):
        nro = self.e_nro.get().strip()
        if not nro.isdigit():
            self.app.toast("Nro. socio invalido.", "error"); return
        with get_conn() as con:
            socio = con.execute(
                "SELECT nombre, fec_baj FROM socios WHERE nro_socio=?",
                (int(nro),)).fetchone()
            if not socio:
                self.tabla.clear()
                self.lbl_socio.configure(text=f"Socio {nro} no existe.",
                                          text_color=COLOR_DANGER)
                return
            filas = con.execute(
                "SELECT c.nro_cuota, c.fec_vencimiento, c.importe, "
                "c.estado, c.fec_cobro, d.tip_compro, d.nro_compro, "
                "d.concepto "
                "FROM cuotas_socio c "
                "JOIN desc_compras_sno d ON d.id = c.desc_compra_id "
                "WHERE d.nro_socio=? "
                "ORDER BY c.fec_vencimiento, d.tip_compro, d.nro_compro, "
                "c.nro_cuota", (int(nro),)).fetchall()

        estado_socio = " (dado de baja)" if socio["fec_baj"] else ""
        self.lbl_socio.configure(
            text=f"{socio['nombre']}{estado_socio}",
            text_color=COLOR_WARNING if socio["fec_baj"]
            else COLOR_SUCCESS)

        self.tabla.clear()
        total_pendiente = total_cobrado = total_anulado = 0.0
        for f in filas:
            estado_kind = {
                "PENDIENTE": "warning",
                "COBRADA":   "success",
                "ANULADA":   "danger",
            }.get(f["estado"], "info")
            self.tabla.add_row({
                "comp":     f"{f['tip_compro']}-{f['nro_compro']}",
                "concepto": (f["concepto"] or "")[:34],
                "cuota":    f["nro_cuota"],
                "venc":     fecha_ui(f["fec_vencimiento"]),
                "importe":  fmt_moneda(f["importe"]),
                "estado":   f["estado"],
            }, badges={"estado": estado_kind})
            if f["estado"] == "PENDIENTE": total_pendiente += f["importe"]
            elif f["estado"] == "COBRADA": total_cobrado += f["importe"]
            elif f["estado"] == "ANULADA": total_anulado += f["importe"]

        self._m_pendiente.configure(text=fmt_moneda(total_pendiente))
        self._m_cobrado.configure(text=fmt_moneda(total_cobrado))
        self._m_anulado.configure(text=fmt_moneda(total_anulado))
        self._datos_export = (
            f"Socio {nro} - {socio['nombre']}"
            + (f" (baja {fecha_ui(socio['fec_baj'])})"
               if socio["fec_baj"] else ""),
            [dict(f, comp=f"{f['tip_compro']}-{f['nro_compro']}")
             for f in filas],
            [("Pendiente de cobro", total_pendiente),
             ("Ya cobrado", total_cobrado),
             ("Anulado", total_anulado)], nro)
        self.app.toast(f"Estado de cuenta de {socio['nombre']} generado.",
                       "success")

    def _exportar(self):
        if not self._datos_export:
            self.app.toast("Primero busca un socio.", "warning"); return
        sub, filas, totales, nro = self._datos_export
        exportar_reporte(
            self.app, "Estado de cuenta", sub,
            [("Comprobante", "comp", 2.2, "txt"),
             ("Concepto", "concepto", 5, "txt"),
             ("Cuota", "nro_cuota", 1, "int"),
             ("Vencimiento", "fec_vencimiento", 2, "fecha"),
             ("Importe", "importe", 2.2, "moneda"),
             ("Estado", "estado", 2, "txt"),
             ("Cobrada el", "fec_cobro", 2, "fecha")],
            filas, totales, f"estado_cuenta_{nro}", "EXPORTA_REPORTE")


# =====================================================================
#  PANEL: CUOTAS VENCIDAS / A VENCER
# =====================================================================
class PanelCuotasVencidas(ctk.CTkFrame):
    DIAS_A_VENCER = 7
    FILTROS = ["Vencidas", f"A vencer ({DIAS_A_VENCER} dias)",
              "Todas las pendientes"]

    def __init__(self, master, app, titulo="Cuotas vencidas", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.tipo = "PROVEEDOR"
        app.set_breadcrumb("Reportes", "Cuotas vencidas / a vencer")
        app.set_badge("")

        tb = Card(self)
        tb.pack(fill="x", pady=(0, 12))
        wrap = ctk.CTkFrame(tb, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)

        tabs = ctk.CTkFrame(wrap, fg_color="transparent")
        tabs.pack(side="left")
        self.btn_prov = ctk.CTkButton(
            tabs, text="Proveedores (a pagar)",
            font=F(13, "bold"), height=36, corner_radius=6,
            fg_color=COLOR_ACCENT, text_color="white",
            border_color=COLOR_BORDER_STRONG, border_width=1,
            hover_color=COLOR_ACCENT_HOVER,
            command=lambda: self._cambiar_tipo("PROVEEDOR"))
        self.btn_prov.pack(side="left", padx=(0, 4))
        self.btn_soc = ctk.CTkButton(
            tabs, text="Socios (a cobrar)",
            font=F(13, "bold"), height=36, corner_radius=6,
            fg_color=COLOR_CARD, text_color=COLOR_TEXT,
            border_color=COLOR_BORDER_STRONG, border_width=1,
            hover_color=COLOR_ACCENT_HOVER,
            command=lambda: self._cambiar_tipo("SOCIO"))
        self.btn_soc.pack(side="left")

        self.var_filtro = ctk.StringVar(value=self.FILTROS[0])
        ctk.CTkComboBox(wrap, values=self.FILTROS,
                        variable=self.var_filtro,
                        width=200, font=F(13), dropdown_font=F(13),
                        fg_color=COLOR_CARD, border_color=COLOR_BORDER,
                        button_color=COLOR_BORDER,
                        button_hover_color=COLOR_ACCENT,
                        text_color=COLOR_TEXT, height=36, corner_radius=6,
                        command=lambda v: self._refrescar(),
                        state="readonly").pack(side="right")
        AccentButton(wrap, "Exportar", "\u2913", command=self._exportar,
                     width=130).pack(side="right", padx=8)
        self._export = ([], 0.0)

        card = Card(self)
        card.pack(fill="both", expand=True, pady=6)
        wrap2 = ctk.CTkFrame(card, fg_color="transparent")
        wrap2.pack(fill="both", expand=True, padx=14, pady=14)

        self.tabla = DataTable(wrap2, columns=[
            (110, "Comprobante", "comp"),
            (60,  "Cuota",       "cuota"),
            (240, "Contraparte", "nombre"),
            (110, "Vencimiento", "venc"),
            (140, "Situacion",   "situacion"),
            (120, "Importe",     "importe"),
        ])
        self.tabla.pack(fill="both", expand=True)

        self.lbl_total = ctk.CTkLabel(card, text="", font=F(12, "bold"),
                                       text_color=COLOR_TEXT_MUTED)
        self.lbl_total.pack(pady=(4, 12))

        self._refrescar()

    def _cambiar_tipo(self, tipo):
        self.tipo = tipo
        self.btn_prov.configure(
            fg_color=COLOR_ACCENT if tipo == "PROVEEDOR" else COLOR_CARD,
            text_color="white" if tipo == "PROVEEDOR" else COLOR_TEXT)
        self.btn_soc.configure(
            fg_color=COLOR_ACCENT if tipo == "SOCIO" else COLOR_CARD,
            text_color="white" if tipo == "SOCIO" else COLOR_TEXT)
        self._refrescar()

    def _refrescar(self):
        tabla = "cuotas_proveedor" if self.tipo == "PROVEEDOR" \
                else "cuotas_socio"
        campo_join = "cod_proveedor" if self.tipo == "PROVEEDOR" \
                    else "nro_socio"
        tabla_join = "proveedores" if self.tipo == "PROVEEDOR" else "socios"
        campo_nombre = "razon_social" if self.tipo == "PROVEEDOR" \
                       else "nombre"

        sql = (f"SELECT c.nro_cuota, c.fec_vencimiento, c.importe, "
              f"d.tip_compro, d.nro_compro, "
              f"j.{campo_nombre} AS nombre "
              f"FROM {tabla} c "
              f"JOIN desc_compras_sno d ON d.id = c.desc_compra_id "
              f"LEFT JOIN {tabla_join} j "
              f"       ON j.{campo_join} = d.{campo_join} "
              f"WHERE c.estado = 'PENDIENTE'")
        with get_conn() as con:
            rows = con.execute(sql).fetchall()

        hoy = datetime.now()
        filtro = self.var_filtro.get()
        procesadas = []
        for r in rows:
            venc = parse_fecha(r["fec_vencimiento"])
            dias = (hoy - venc).days if venc else None
            if filtro == "Vencidas" and not (dias is not None and dias > 0):
                continue
            if filtro.startswith("A vencer") and not (
                    dias is not None and -self.DIAS_A_VENCER <= dias <= 0):
                continue
            procesadas.append((r, dias))
        procesadas.sort(key=lambda t: (t[1] is None, t[1] or 0),
                        reverse=True)

        self.tabla.clear()
        total = 0.0
        filas_exp = []
        for r, dias in procesadas:
            if dias is None:
                situacion = "SIN FECHA"; kind = "muted"
            elif dias > 0:
                situacion = f"VENCIDA {dias}d"; kind = "danger"
            elif dias == 0:
                situacion = "VENCE HOY"; kind = "warning"
            else:
                situacion = f"VENCE EN {-dias}d"; kind = "info"
            self.tabla.add_row({
                "comp":      f"{r['tip_compro']}-{r['nro_compro']}",
                "cuota":     r["nro_cuota"],
                "nombre":    (r["nombre"] or "")[:36],
                "venc":      fecha_ui(r["fec_vencimiento"]),
                "situacion": situacion,
                "importe":   fmt_moneda(r["importe"]),
            }, badges={"situacion": kind})
            total += r["importe"]
            filas_exp.append(dict(r, situacion=situacion,
                                  comp=f"{r['tip_compro']}-"
                                       f"{r['nro_compro']}"))

        etiqueta = "a pagar" if self.tipo == "PROVEEDOR" else "a cobrar"
        self.lbl_total.configure(
            text=f"{len(procesadas)} cuotas  ·  Total {etiqueta}: "
                 f"{fmt_moneda(total)}")
        self._export = (filas_exp, total)

    def _exportar(self):
        filas, total = self._export
        prov = self.tipo == "PROVEEDOR"
        exportar_reporte(
            self.app,
            "Cuotas a pagar a proveedores" if prov
            else "Cuotas a cobrar a socios",
            self.var_filtro.get(),
            [("Comprobante", "comp", 2.2, "txt"),
             ("Cuota", "nro_cuota", 1, "int"),
             ("Proveedor" if prov else "Socio", "nombre", 5, "txt"),
             ("Vencimiento", "fec_vencimiento", 2, "fecha"),
             ("Situacion", "situacion", 2.4, "txt"),
             ("Importe", "importe", 2.2, "moneda")],
            filas, [(f"Total {'a pagar' if prov else 'a cobrar'}", total)],
            "cuotas_proveedores" if prov else "cuotas_socios",
            "EXPORTA_REPORTE")


# =====================================================================
#  PANEL: PADRON INAES Res. 756
# =====================================================================
class PanelInaesRes756(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Padron INAES", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.entries = {}
        app.set_breadcrumb("Reportes", "Padron INAES - Res. 756")
        app.set_badge("Sujeto no obligado", "warning")

        # Configuracion
        card1 = Card(self, title="Configuracion del padron")
        card1.pack(fill="x", pady=6)
        g = ctk.CTkFrame(card1, fg_color="transparent")
        g.pack(fill="x", padx=18, pady=(0, 16))

        ctk.CTkLabel(g, text="TIPO DE MOVIMIENTO", font=F(11, "bold"),
                     text_color=COLOR_TEXT_MUTED, anchor="w").pack(
                     fill="x", pady=(0, 6))
        self.var_tipo = ctk.StringVar(value="1")
        row = ctk.CTkFrame(g, fg_color="transparent")
        row.pack(fill="x", pady=(0, 12))
        ctk.CTkRadioButton(row, text="Altas (fecha de alta)",
                            variable=self.var_tipo, value="1",
                            font=F(13),
                            fg_color=COLOR_ACCENT,
                            hover_color=COLOR_ACCENT_HOVER).pack(
                            side="left", padx=(0, 20))
        ctk.CTkRadioButton(row, text="Bajas (fecha de baja)",
                            variable=self.var_tipo, value="2",
                            font=F(13),
                            fg_color=COLOR_ACCENT,
                            hover_color=COLOR_ACCENT_HOVER).pack(
                            side="left")

        row2 = ctk.CTkFrame(g, fg_color="transparent")
        row2.pack(fill="x", pady=6)
        ctk.CTkLabel(row2, text="Genera archivos", font=F(13),
                     text_color=COLOR_TEXT).pack(side="left", padx=(0, 12))
        self.var_genera = ctk.StringVar(value="N")
        ctk.CTkComboBox(row2, values=["N", "S"], variable=self.var_genera,
                        width=80, font=F(13), dropdown_font=F(13),
                        fg_color=COLOR_CARD, border_color=COLOR_BORDER,
                        button_color=COLOR_BORDER,
                        button_hover_color=COLOR_ACCENT,
                        text_color=COLOR_TEXT, height=34, corner_radius=6,
                        state="readonly").pack(side="left")

        ctk.CTkLabel(row2, text="Solo errores", font=F(13),
                     text_color=COLOR_TEXT).pack(side="left",
                                                  padx=(40, 12))
        self.var_solo_err = ctk.StringVar(value="N")
        ctk.CTkComboBox(row2, values=["N", "S"],
                        variable=self.var_solo_err,
                        width=80, font=F(13), dropdown_font=F(13),
                        fg_color=COLOR_CARD, border_color=COLOR_BORDER,
                        button_color=COLOR_BORDER,
                        button_hover_color=COLOR_ACCENT,
                        text_color=COLOR_TEXT, height=34, corner_radius=6,
                        state="readonly").pack(side="left")

        ctk.CTkLabel(row2, text="Registros por archivo", font=F(13),
                     text_color=COLOR_TEXT).pack(side="left", padx=(40, 12))
        self.e_cant = ctk.CTkEntry(row2, width=100, font=F(13),
                                    fg_color=COLOR_CARD,
                                    border_color=COLOR_BORDER,
                                    text_color=COLOR_TEXT, height=34,
                                    corner_radius=6)
        self.e_cant.insert(0, "99999")
        self.e_cant.pack(side="left")

        # Rangos
        card2 = Card(self, title="Rangos de datos")
        card2.pack(fill="x", pady=6)
        g2 = ctk.CTkFrame(card2, fg_color="transparent")
        g2.pack(fill="x", padx=18, pady=(0, 16))
        g2.grid_columnconfigure((1, 2), weight=1)

        ctk.CTkLabel(g2, text="", width=100).grid(row=0, column=0)
        ctk.CTkLabel(g2, text="Desde", font=F(11, "bold"),
                     text_color=COLOR_TEXT_MUTED).grid(row=0, column=1,
                                                        sticky="w", padx=6)
        ctk.CTkLabel(g2, text="Hasta", font=F(11, "bold"),
                     text_color=COLOR_TEXT_MUTED).grid(row=0, column=2,
                                                        sticky="w", padx=6)

        filas = [
            ("Socio",        "soc_desde",  "soc_hasta",  "1", "21772234"),
            ("Fecha ing.",   "fing_desde", "fing_hasta", "",  "31/12/2099"),
            ("Fecha baja",   "fbaj_desde", "fbaj_hasta", "",  "31/12/2099"),
        ]
        for r, (label, n1, n2, def1, def2) in enumerate(filas, start=1):
            ctk.CTkLabel(g2, text=label, font=F(13),
                         text_color=COLOR_TEXT,
                         anchor="w").grid(row=r, column=0, sticky="w",
                                          padx=6, pady=4)
            e1 = ctk.CTkEntry(g2, font=F(13),
                              fg_color=COLOR_CARD,
                              border_color=COLOR_BORDER,
                              text_color=COLOR_TEXT, height=34,
                              corner_radius=6)
            e1.grid(row=r, column=1, sticky="ew", padx=6, pady=4)
            e1.insert(0, def1)
            e2 = ctk.CTkEntry(g2, font=F(13),
                              fg_color=COLOR_CARD,
                              border_color=COLOR_BORDER,
                              text_color=COLOR_TEXT, height=34,
                              corner_radius=6)
            e2.grid(row=r, column=2, sticky="ew", padx=6, pady=4)
            e2.insert(0, def2)
            self.entries[n1] = e1
            self.entries[n2] = e2

        # Resumen
        self.lbl_resumen = ctk.CTkLabel(self, text="",
                                         font=F(12),
                                         text_color=COLOR_TEXT_MUTED,
                                         justify="left", anchor="w")
        self.lbl_resumen.pack(fill="x", padx=8, pady=(4, 8))

        # Botones
        bar = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                           border_color=COLOR_BORDER, border_width=1,
                           corner_radius=10, height=72)
        bar.pack(fill="x", pady=(6, 8))
        bar.pack_propagate(False)
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=16)

        SecondaryButton(inner, "Vista previa", "\u25B6",
                        command=self._preview,
                        width=150).pack(side="left", padx=4)
        PrimaryButton(inner, "Emitir padron", "\u2691",
                      command=self._emitir,
                      width=170).pack(side="right", padx=4)

    def _obtener_socios(self):
        tipo = self.var_tipo.get()
        try:
            soc_d = int(self.entries["soc_desde"].get() or "0")
            soc_h = int(self.entries["soc_hasta"].get() or "999999999")
        except ValueError:
            self.app.toast("Rango de socio invalido.", "error")
            return None

        fing_d = parse_fecha(self.entries["fing_desde"].get())
        fing_h = parse_fecha(self.entries["fing_hasta"].get())
        fbaj_d = parse_fecha(self.entries["fbaj_desde"].get())
        fbaj_h = parse_fecha(self.entries["fbaj_hasta"].get())

        q = ("SELECT nro_socio, nombre, tipo_doc, cuil, fec_nac, sexo, "
             "       direccion, localidad, cp, telefono, mail, "
             "       fec_ing, fec_baj, fec_alta, categoria, es_pep, "
             "       riesgo, extranjero "
             "FROM socios WHERE nro_socio BETWEEN ? AND ?")
        params = [soc_d, soc_h]
        if tipo == "1":
            q += " AND fec_ing IS NOT NULL AND fec_ing <> ''"
        else:
            q += " AND fec_baj IS NOT NULL AND fec_baj <> ''"
        q += " ORDER BY nro_socio"
        with get_conn() as con:
            rows = con.execute(q, params).fetchall()

        out = []; errores = []
        for r in rows:
            d = dict(r)
            ok = True
            fi = parse_fecha(d.get("fec_ing") or "")
            if fing_d and (not fi or fi < fing_d): ok = False
            if fing_h and fi and fi > fing_h:      ok = False
            fb = parse_fecha(d.get("fec_baj") or "")
            if fbaj_d and (not fb or fb < fbaj_d): ok = False
            if fbaj_h and fb and fb > fbaj_h:      ok = False
            if not ok: continue

            err = []
            if not d.get("nombre"):   err.append("falta nombre")
            if not d.get("cuil"):     err.append("falta CUIL")
            if not d.get("fec_nac"):  err.append("falta fec.nac")
            if not d.get("tipo_doc"): err.append("falta tipo doc")
            if err:
                errores.append((d["nro_socio"], d.get("nombre", ""),
                                ", ".join(err)))
            elif self.var_solo_err.get() == "S":
                continue
            out.append(d)
        return out, errores

    def _preview(self):
        res = self._obtener_socios()
        if res is None: return
        socios, errores = res
        tipo_txt = "ALTAS" if self.var_tipo.get() == "1" else "BAJAS"
        txt = (f"Preview padron {tipo_txt}\n"
               f"Registros: {len(socios)}   ·   "
               f"Con errores: {len(errores)}")
        if errores:
            det = "\n".join(f"  - Socio {n}: {e}"
                            for n, _, e in errores[:8])
            if len(errores) > 8:
                det += f"\n  ... y {len(errores) - 8} mas"
            txt += "\n\nErrores:\n" + det
        self.lbl_resumen.configure(text=txt,
                                    text_color=COLOR_WARNING if errores
                                    else COLOR_SUCCESS)
        self.app.toast(f"Preview: {len(socios)} registros listos.",
                       "info")

    def _emitir(self):
        if (self.var_genera.get() == "S"
                and not self.app.puede(NIVEL_OPERAR, "emitir el padron")):
            return
        try:
            cant_x_arch = int(self.e_cant.get() or "99999")
        except ValueError:
            self.app.toast("Cantidad por archivo invalida.", "error")
            return
        if cant_x_arch < 1: return

        res = self._obtener_socios()
        if res is None: return
        socios, errores = res
        if not socios and not errores:
            ConfirmDialog.info("Padron INAES",
                        "No hay registros que cumplan los criterios.")
            return
        tipo = self.var_tipo.get()
        tipo_txt = "ALTAS" if tipo == "1" else "BAJAS"

        if self.var_genera.get() != "S":
            self.app.toast(
                f"Vista de {len(socios)} registros ({tipo_txt}).", "info")
            self._preview()
            return

        usar_dialogo = messagebox.askyesnocancel(
            "Guardar padron",
            "Desea elegir el nombre y ubicacion del archivo?\n\n"
            "SI: abre el explorador para elegir carpeta/nombre.\n"
            "NO: guarda como INAES.CSV en la carpeta INAES/ del programa.\n"
            "CANCELAR: no genera nada.")
        if usar_dialogo is None:
            self.app.toast("Emision cancelada.", "warning"); return

        if usar_dialogo:
            ruta_base = filedialog.asksaveasfilename(
                title="Guardar padron INAES como...",
                defaultextension=".csv",
                filetypes=[("Archivos CSV", "*.csv"),
                           ("Todos los archivos", "*.*")],
                initialfile="INAES.CSV")
            if not ruta_base:
                self.app.toast("Emision cancelada.", "warning"); return
            if not ruta_base.lower().endswith(".csv"):
                ruta_base += ".csv"
            out_dir = os.path.dirname(ruta_base) or "."
            nombre_sin_ext = os.path.splitext(
                os.path.basename(ruta_base))[0]
            eliminados = 0
        else:
            out_dir = os.path.join(_base_dir(), "INAES")
            os.makedirs(out_dir, exist_ok=True)
            nombre_sin_ext = "INAES"
            eliminados = 0
            for f in os.listdir(out_dir):
                if f.upper().startswith("INAES") and \
                   f.upper().endswith(".CSV"):
                    try:
                        os.remove(os.path.join(out_dir, f))
                        eliminados += 1
                    except OSError: pass
            ruta_base = os.path.join(out_dir, f"{nombre_sin_ext}.CSV")

        header = ["NRO_SOCIO", "NOMBRE", "TIPO_DOC", "CUIL",
                  "FEC_NAC", "SEXO", "DIRECCION", "LOCALIDAD",
                  "CP", "TELEFONO", "MAIL", "FEC_ING", "FEC_BAJ",
                  "CATEGORIA", "ES_PEP", "RIESGO", "EXTRANJERO",
                  "TIPO_MOVIMIENTO"]
        tipo_mov = "ALTA" if tipo == "1" else "BAJA"

        def fila(d):
            return [str(d["nro_socio"]),
                    (d.get("nombre") or "").strip(),
                    d.get("tipo_doc") or "",
                    d.get("cuil") or "",
                    fmt_inaes(d.get("fec_nac")),
                    d.get("sexo") or "",
                    (d.get("direccion") or "").strip(),
                    (d.get("localidad") or "").strip(),
                    d.get("cp") or "",
                    d.get("telefono") or "",
                    d.get("mail") or "",
                    fmt_inaes(d.get("fec_ing")),
                    fmt_inaes(d.get("fec_baj")),
                    d.get("categoria") or "",
                    d.get("es_pep") or "N",
                    d.get("riesgo") or "B",
                    d.get("extranjero") or "N",
                    tipo_mov]

        archivos_creados = []
        n_total = len(socios)
        if n_total <= cant_x_arch:
            try:
                with open(ruta_base, "w", newline="",
                          encoding="utf-8") as f:
                    w = csv.writer(f, delimiter=";")
                    w.writerow(header)
                    for d in socios: w.writerow(fila(d))
                archivos_creados.append((os.path.basename(ruta_base),
                                          n_total, ruta_base))
            except OSError as e:
                self.app.toast(f"Error al escribir: {e}", "error"); return
        else:
            nro_arch = 1; i = 0
            while i < n_total:
                chunk = socios[i:i + cant_x_arch]
                nombre = f"{nombre_sin_ext}{nro_arch:02d}.CSV"
                path = os.path.join(out_dir, nombre)
                try:
                    with open(path, "w", newline="",
                              encoding="utf-8") as f:
                        w = csv.writer(f, delimiter=";")
                        w.writerow(header)
                        for d in chunk: w.writerow(fila(d))
                    archivos_creados.append((nombre, len(chunk), path))
                except OSError as e:
                    self.app.toast(f"Error al escribir {nombre}: {e}",
                                   "error"); return
                i += cant_x_arch; nro_arch += 1

        if errores:
            err_path = os.path.join(out_dir,
                                    f"{nombre_sin_ext}_ERRORES.LOG")
            try:
                with open(err_path, "w", encoding="utf-8") as f:
                    f.write(f"PADRON INAES - {tipo_txt}  "
                            f"{datetime.now():%d/%m/%Y %H:%M}\n")
                    f.write("=" * 60 + "\n")
                    for n, nom, e in errores:
                        f.write(f"Socio {n:>7}  {nom:<35}  {e}\n")
            except OSError: pass

        registrar_auditoria(self.app.usuario["usuario"],
                            "EMITIR_PADRON_INAES",
                            f"{tipo_txt} archivos={len(archivos_creados)} "
                            f"registros={n_total}")

        carpeta_abs = os.path.abspath(out_dir)
        resumen = (f"Padron INAES ({tipo_txt}) emitido OK.\n"
                   f"Carpeta: {carpeta_abs}\n")
        if eliminados:
            resumen += f"Archivos previos eliminados: {eliminados}\n"
        resumen += f"Archivos generados: {len(archivos_creados)}\n"
        for nom, n, _ in archivos_creados:
            resumen += f"  - {nom}  ({n} registros)\n"
        if errores:
            resumen += (f"Errores: {len(errores)} (ver "
                        f"{nombre_sin_ext}_ERRORES.LOG)\n")
        self.lbl_resumen.configure(text=resumen,
                                    text_color=COLOR_SUCCESS)
        self.app.toast(
            f"Padron emitido: {len(archivos_creados)} archivo(s).",
            "success")
        if ConfirmDialog.yes_no("Padron INAES",
                f"Se generaron {len(archivos_creados)} archivo(s) en:\n"
                f"{carpeta_abs}\n\nDesea abrir la carpeta?"):
            abrir_carpeta(carpeta_abs)


# =====================================================================
#  PANEL: BACKUP DE BASE DE DATOS
# =====================================================================
class PanelBackup(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Backup", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        app.set_breadcrumb("Administracion", "Backup de base de datos")
        app.set_badge("")

        card = Card(self, title="Backup de la base de datos")
        card.pack(fill="x", pady=8)
        inner = ctk.CTkFrame(card, fg_color="transparent")
        inner.pack(fill="x", padx=18, pady=(0, 20))

        ctk.CTkLabel(inner,
            text="Genera una copia de seguridad completa y consistente de "
                 f"la base de datos ({DB_NOMBRE}).\n\n"
                 "Ademas, cada vez que se cierra el programa se guarda un "
                 "backup automatico en la carpeta 'backups' (se conservan "
                 f"los ultimos {BACKUPS_AUTO_A_CONSERVAR}). Igual conviene "
                 "copiar un backup fuera de la PC (pendrive, disco externo, "
                 "nube) al menos una vez por semana.",
            font=F(13), text_color=COLOR_TEXT_MUTED,
            justify="left", anchor="w",
            wraplength=800).pack(fill="x")

        card2 = Card(self, title="Estado actual")
        card2.pack(fill="x", pady=8)
        info = ctk.CTkFrame(card2, fg_color="transparent")
        info.pack(fill="x", padx=18, pady=(0, 20))

        try:
            size = os.path.getsize(DB_PATH)
            size_mb = size / (1024 * 1024)
            self._info_row(info, "Ruta de la base:", DB_PATH)
            self._info_row(info, "Tamano:", f"{size_mb:.2f} MB")
        except Exception:
            self._info_row(info, "Estado:", "Base no accesible")

        try:
            with get_conn() as con:
                n_soc = con.execute(
                    "SELECT COUNT(*) AS c FROM socios").fetchone()["c"]
                n_pro = con.execute(
                    "SELECT COUNT(*) AS c FROM proveedores").fetchone()["c"]
                n_com = con.execute(
                    "SELECT COUNT(*) AS c FROM desc_compras_sno"
                    ).fetchone()["c"]
            self._info_row(info, "Socios registrados:", str(n_soc))
            self._info_row(info, "Proveedores:", str(n_pro))
            self._info_row(info, "Comprobantes:", str(n_com))
        except Exception:
            pass
        try:
            autos = sorted(f for f in os.listdir(BACKUP_DIR)
                           if f.startswith("novamut_auto_"))
        except OSError:
            autos = []
        if autos:
            ult = autos[-1][len("novamut_auto_"):-3]
            try:
                ult = datetime.strptime(ult, "%Y%m%d_%H%M%S").strftime(
                    "%d/%m/%Y %H:%M")
            except ValueError:
                pass
            self._info_row(info, "Backups automaticos:",
                           f"{len(autos)} (ultimo: {ult})")
        else:
            self._info_row(info, "Backups automaticos:",
                           "todavia ninguno (se hace al cerrar)")

        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.pack(fill="x", pady=(4, 8))
        SecondaryButton(bar, "Abrir carpeta de backups", "\u21AA",
                        command=self._abrir_backups,
                        width=240).pack(side="left", padx=4)
        PrimaryButton(bar, "Generar backup ahora", "\u21BA",
                      command=self._backup,
                      width=240).pack(side="right", padx=4)

        self.lbl_msg = ctk.CTkLabel(self, text="", font=F(12),
                                     text_color=COLOR_TEXT_MUTED,
                                     justify="left")
        self.lbl_msg.pack(fill="x", padx=8)

    def _info_row(self, parent, label, valor):
        row = ctk.CTkFrame(parent, fg_color="transparent")
        row.pack(fill="x", pady=2)
        ctk.CTkLabel(row, text=label, font=F(12),
                     text_color=COLOR_TEXT_MUTED,
                     width=200, anchor="w").pack(side="left")
        ctk.CTkLabel(row, text=valor, font=F(12, "bold"),
                     text_color=COLOR_TEXT,
                     anchor="w").pack(side="left", fill="x", expand=True)

    def _abrir_backups(self):
        os.makedirs(BACKUP_DIR, exist_ok=True)
        abrir_carpeta(BACKUP_DIR)

    def _backup(self):
        if not self.app.puede(NIVEL_OPERAR, "hacer backups"): return
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        default_name = f"novamut_backup_{stamp}.db"
        destino = filedialog.asksaveasfilename(
            title="Guardar backup como...",
            defaultextension=".db",
            filetypes=[("Base SQLite", "*.db"),
                       ("Todos", "*.*")],
            initialfile=default_name)
        if not destino:
            self.app.toast("Backup cancelado.", "warning"); return
        try:
            hacer_backup(destino)
            registrar_auditoria(self.app.usuario["usuario"], "BACKUP",
                                destino)
            tam = os.path.getsize(destino) / (1024 * 1024)
            self.lbl_msg.configure(
                text=f"OK. Backup guardado en:\n{destino}  "
                     f"({tam:.2f} MB)",
                text_color=COLOR_SUCCESS)
            self.app.toast("Backup generado.", "success")
            if ConfirmDialog.yes_no("Backup",
                    f"Backup guardado en:\n{destino}\n\n"
                    "Desea abrir la carpeta?"):
                abrir_carpeta(os.path.dirname(destino))
        except Exception as e:
            self.lbl_msg.configure(text=f"ERROR: {e}",
                                    text_color=COLOR_DANGER)
            self.app.toast(f"Error en backup: {e}", "error")


# =====================================================================
#  PANEL: CAMBIAR CONTRASENA (propio)
# =====================================================================
class PanelCambiarPassword(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Cambiar contrasena",
                 forzado=False, **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.forzado = forzado
        app.set_breadcrumb("Mi cuenta", "Cambiar contrasena")
        if forzado:
            app.set_badge("Requerido", "danger")
        else:
            app.set_badge("")

        # Espaciador arriba
        ctk.CTkFrame(self, fg_color="transparent", height=40).pack()

        # Contenedor centrado
        wrap = ctk.CTkFrame(self, fg_color="transparent")
        wrap.pack()

        # Tarjeta principal - crece con el contenido
        card = ctk.CTkFrame(wrap, fg_color=COLOR_CARD,
                            border_color=COLOR_BORDER, border_width=1,
                            corner_radius=12)
        card.pack(padx=20, pady=20)

        # Icono
        icon_box = ctk.CTkFrame(card, fg_color=COLOR_WARNING_BG
                                 if forzado else COLOR_ACCENT_BG,
                                 corner_radius=12, width=64, height=64)
        icon_box.pack(pady=(28, 12), padx=60)
        icon_box.pack_propagate(False)
        ctk.CTkLabel(icon_box, text="\u2318", font=F(30, "bold"),
                     text_color=COLOR_WARNING_TXT if forzado
                     else COLOR_ACCENT).pack(expand=True)

        # Titulo
        ctk.CTkLabel(card, text="Cambiar contrasena",
                     font=F(22, "bold"),
                     text_color=COLOR_TEXT).pack()

        # Subtitulo
        if forzado:
            ctk.CTkLabel(card,
                text="Es la primera vez que ingresas o un administrador\n"
                     "reseteo tu clave. Debes elegir una nueva para "
                     "continuar.",
                font=F(12), text_color=COLOR_TEXT_MUTED,
                justify="center").pack(pady=(4, 18), padx=40)
        else:
            ctk.CTkLabel(card, text="Actualiza tu clave de acceso",
                         font=F(12),
                         text_color=COLOR_TEXT_MUTED).pack(pady=(4, 18))

        # Formulario (widgets internos manejan el ancho)
        self.fields = {}
        if not forzado:
            f0 = Field(card, "Clave actual", password=True, width=380)
            f0.pack(padx=40, pady=(0, 12))
            self.fields["actual"] = f0

        f1 = Field(card, "Clave nueva", password=True, width=380)
        f1.pack(padx=40, pady=(0, 12))
        self.fields["nueva"] = f1

        f2 = Field(card, "Repetir clave nueva", password=True, width=380)
        f2.pack(padx=40, pady=(0, 4))
        self.fields["confirma"] = f2

        # Hint
        hint = ctk.CTkLabel(card,
            text="Minimo 8 caracteres, con al menos una letra y un numero.",
            font=F(11), text_color=COLOR_TEXT_MUTED,
            anchor="w", width=380)
        hint.pack(padx=40, pady=(8, 0))

        # Mensaje de error
        self.lbl_msg = ctk.CTkLabel(card, text="", font=F(12),
                                     text_color=COLOR_DANGER,
                                     wraplength=380, width=380)
        self.lbl_msg.pack(padx=40, pady=(6, 0))

        # Botones
        btns = ctk.CTkFrame(card, fg_color="transparent")
        btns.pack(padx=40, pady=(20, 28))

        PrimaryButton(btns, "Guardar", "\u2713",
                      command=self._guardar,
                      width=170, height=42).pack(side="right", padx=4)
        if forzado:
            DangerButton(btns, "Cerrar sesion", "\u21B6",
                         command=self._cancelar_forzado,
                         width=170, height=42).pack(side="right", padx=4)
        else:
            SecondaryButton(btns, "Cancelar",
                            command=lambda: self.app._on_sidebar_click(
                                "socios"),
                            width=140, height=42).pack(side="right",
                                                        padx=4)

        # Focus inicial
        self.after(100, lambda: (self.fields["actual"].focus()
                                  if "actual" in self.fields
                                  else self.fields["nueva"].focus()))

    def _guardar(self):
        nueva = self.fields["nueva"].get()
        confirma = self.fields["confirma"].get()
        if not val_password_fuerte(nueva):
            self.lbl_msg.configure(
                text="La clave nueva no cumple la politica minima "
                     "(8+ caracteres, letras y numeros).")
            return
        if nueva != confirma:
            self.lbl_msg.configure(text="Las claves no coinciden.")
            return
        with get_conn() as con:
            row = con.execute(
                "SELECT salt, password FROM usuarios WHERE id=?",
                (self.app.usuario["id"],)).fetchone()
            if not self.forzado:
                actual = self.fields["actual"].get()
                if not verify_password(actual, row["salt"],
                                        row["password"]):
                    self.lbl_msg.configure(
                        text="La clave actual es incorrecta.")
                    return
            nuevo_hash = hash_password(nueva, row["salt"])
            con.execute("UPDATE usuarios SET password=?, "
                        "debe_cambiar_pwd=0 WHERE id=?",
                        (nuevo_hash, self.app.usuario["id"]))
        registrar_auditoria(self.app.usuario["usuario"],
                            "CAMBIO_PASSWORD_PROPIO")
        self.app.usuario["debe_cambiar_pwd"] = False
        self.app.toast("Contrasena actualizada correctamente.", "success")
        self.app._on_sidebar_click("socios")

    def _cancelar_forzado(self):
        self.app.usuario = None
        self.app.show_login()


# =====================================================================
#  PANEL: GESTION DE USUARIOS
# =====================================================================
class PanelGestionUsuarios(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Usuarios", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.mi_rol = app.usuario["rol"]
        self.modo = "LISTADO"
        self.usuarios_actuales = []
        self.sel_actual = None

        app.set_breadcrumb("Administracion", "Gestion de usuarios")
        app.set_badge(app.usuario["rol"], "info")

        self._build_toolbar()
        self._build_tabla()
        self._build_form()
        self._build_action_bar()
        self._set_modo("LISTADO")
        self._refrescar()

    def _build_toolbar(self):
        tb = Card(self)
        tb.pack(fill="x", pady=(0, 12))
        wrap = ctk.CTkFrame(tb, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)

        ctk.CTkLabel(wrap, text="Buscar:", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 8))
        self.e_q = ctk.CTkEntry(wrap, width=300, font=F(13),
                                 fg_color=COLOR_CARD,
                                 border_color=COLOR_BORDER,
                                 text_color=COLOR_TEXT, height=36,
                                 corner_radius=6,
                                 placeholder_text="Usuario o nombre...")
        self.e_q.pack(side="left")
        self.e_q.bind("<KeyRelease>", lambda e: self._refrescar())

    def _build_tabla(self):
        card = Card(self)
        card.pack(fill="both", expand=True, pady=6)
        wrap = ctk.CTkFrame(card, fg_color="transparent")
        wrap.pack(fill="both", expand=True, padx=14, pady=14)

        self.tabla = DataTable(wrap, columns=[
            (160, "Usuario",       "usuario"),
            (240, "Nombre",        "nombre"),
            (110, "Rol",           "rol"),
            (80,  "Estado",        "estado"),
            (160, "Ultimo acceso", "ultimo"),
        ], on_row_click=self._seleccionar_key)
        self.tabla.pack(fill="both", expand=True)

    def _build_form(self):
        self.form_card = Card(self, title="Datos del usuario")
        g = ctk.CTkFrame(self.form_card, fg_color="transparent")
        g.pack(fill="x", padx=18, pady=(0, 16))
        g.grid_columnconfigure((0, 1, 2), weight=1)

        self.fields = {}
        self._add_field(g, "usuario",  "Usuario",       0, 0)
        self._add_field(g, "nombre",   "Nombre",        0, 1, cspan=2)
        self._add_field(g, "password", "Clave",         1, 0, password=True)
        self._add_field(g, "confirma", "Repetir clave", 1, 1, password=True)
        self._add_field(g, "rol",      "Rol",           1, 2,
                        values=["OPERADOR"])

        self.var_activo = ctk.BooleanVar(value=True)
        self.chk_activo = ctk.CTkCheckBox(
            g, text="Usuario activo",
            variable=self.var_activo,
            font=F(12), text_color=COLOR_TEXT,
            fg_color=COLOR_ACCENT, hover_color=COLOR_ACCENT_HOVER,
            corner_radius=4)
        self.chk_activo.grid(row=2, column=0, columnspan=3, sticky="w",
                             padx=6, pady=(10, 0))

        self.lbl_form_msg = ctk.CTkLabel(self.form_card, text="",
                                          font=F(12),
                                          text_color=COLOR_DANGER)
        self.lbl_form_msg.pack(pady=(0, 12))

    def _add_field(self, parent, name, label, row, col, cspan=1,
                   password=False, values=None):
        f = Field(parent, label, name=name, password=password,
                  values=values)
        f.grid(row=row, column=col, columnspan=cspan,
               sticky="ew", padx=6, pady=6)
        self.fields[name] = f

    def _build_action_bar(self):
        bar = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                           border_color=COLOR_BORDER, border_width=1,
                           corner_radius=10, height=72)
        bar.pack(fill="x", pady=(6, 8))
        bar.pack_propagate(False)
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="both", expand=True, padx=18, pady=16)

        left = ctk.CTkFrame(inner, fg_color="transparent")
        left.pack(side="left")
        SecondaryButton(left, "Nuevo", "+", command=self._nuevo,
                        width=110).pack(side="left", padx=4)
        SecondaryButton(left, "Editar", "\u270E", command=self._editar,
                        width=110).pack(side="left", padx=4)
        SecondaryButton(left, "Reset clave", "\u21BA",
                        command=self._reset_pwd,
                        width=130).pack(side="left", padx=4)
        DangerButton(left, "Activar/Desactivar", "\u21C6",
                     command=self._toggle_activo,
                     width=180).pack(side="left", padx=4)

        right = ctk.CTkFrame(inner, fg_color="transparent")
        right.pack(side="right")
        self.btn_guardar = PrimaryButton(
            right, "Guardar", "\u2713",
            command=self._guardar, width=160)
        self.btn_guardar.pack(side="right", padx=4)

    def _seleccionar_key(self, key):
        for u in self.usuarios_actuales:
            if u["id"] == key:
                self.sel_actual = u
                self.app.toast(f"Seleccionado: {u['usuario']}", "info")
                return

    def _set_modo(self, modo):
        self.modo = modo
        if modo == "LISTADO":
            self.form_card.pack_forget()
        else:
            self.form_card.pack(fill="x", pady=6)
        self.lbl_form_msg.configure(text="")

        alta = (modo == "ALTA")
        editar = (modo == "EDITAR")
        reset = (modo == "RESET")

        self.fields["usuario"].set_state("normal" if alta else "disabled")
        self.fields["nombre"].set_state(
            "normal" if (alta or editar) else "disabled")
        self.fields["password"].set_state(
            "normal" if (alta or reset) else "disabled")
        self.fields["confirma"].set_state(
            "normal" if (alta or reset) else "disabled")
        self.fields["rol"].set_state(
            "normal" if (alta or editar) else "disabled")
        self.chk_activo.configure(
            state="normal" if editar else "disabled")

        editable = alta or editar or reset
        self.btn_guardar.configure(
            state="normal" if editable else "disabled",
            fg_color=COLOR_SUCCESS if editable else "#94a3b8")

        if modo == "ALTA":
            for f in self.fields.values():
                f.set("")
            self.var_activo.set(True)
            asignables = roles_asignables(self.mi_rol)
            self._poblar_roles(asignables,
                               asignables[-1] if asignables
                               else "OPERADOR")

    def _poblar_roles(self, roles, seleccion):
        self.fields["rol"].widget.configure(values=list(roles))
        self.fields["rol"].set(seleccion)

    def _refrescar(self):
        q = f"%{self.e_q.get().strip().upper()}%"
        with get_conn() as con:
            rows = con.execute(
                "SELECT id, usuario, nombre, rol, activo, ultimo_log "
                "FROM usuarios "
                "WHERE UPPER(usuario) LIKE ? OR UPPER(nombre) LIKE ? "
                "ORDER BY usuario", (q, q)).fetchall()
        self.usuarios_actuales = [dict(r) for r in rows]
        self.tabla.clear()
        for u in self.usuarios_actuales:
            estado = "ACTIVO" if u["activo"] else "BAJA"
            ultimo = (u["ultimo_log"] or "-")[:16].replace("T", " ")
            marca = "  (yo)" if u["usuario"] == self.app.usuario["usuario"] \
                    else ""
            self.tabla.add_row({
                "usuario": u["usuario"] + marca,
                "nombre":  u["nombre"] or "",
                "rol":     u["rol"],
                "estado":  estado,
                "ultimo":  ultimo,
            }, badges={"estado":
                       "success" if u["activo"] else "danger"},
                key=u["id"])
        self.sel_actual = None

    def _nuevo(self):
        self._set_modo("ALTA")
        self.fields["usuario"].focus()

    def _editar(self):
        if not self.sel_actual:
            self.app.toast("Selecciona un usuario.", "warning"); return
        if self.sel_actual["usuario"] == self.app.usuario["usuario"]:
            self.app.toast(
                "Usa 'Cambiar clave' para tu propio usuario.",
                "warning"); return
        if not puede_gestionar_rol(self.mi_rol, self.sel_actual["rol"]):
            self.app.toast("No tienes permisos sobre ese rol.", "error")
            return
        self._set_modo("EDITAR")
        self.fields["usuario"].set(self.sel_actual["usuario"])
        self.fields["nombre"].set(self.sel_actual["nombre"])
        asignables = list(roles_asignables(self.mi_rol))
        if self.sel_actual["rol"] not in asignables:
            asignables.append(self.sel_actual["rol"])
        self._poblar_roles(asignables, self.sel_actual["rol"])
        self.var_activo.set(bool(self.sel_actual["activo"]))

    def _reset_pwd(self):
        if not self.sel_actual:
            self.app.toast("Selecciona un usuario.", "warning"); return
        if self.sel_actual["usuario"] == self.app.usuario["usuario"]:
            self.app.toast(
                "Usa 'Cambiar clave' para tu propio usuario.",
                "warning"); return
        if not puede_gestionar_rol(self.mi_rol, self.sel_actual["rol"]):
            self.app.toast("No tienes permisos sobre ese rol.", "error")
            return
        self._set_modo("RESET")
        self.fields["usuario"].set(self.sel_actual["usuario"])
        self.fields["password"].focus()

    def _toggle_activo(self):
        if not self.sel_actual:
            self.app.toast("Selecciona un usuario.", "warning"); return
        fila = self.sel_actual
        if fila["usuario"] == self.app.usuario["usuario"]:
            self.app.toast("No puedes desactivar tu propio usuario.",
                           "error"); return
        if not puede_gestionar_rol(self.mi_rol, fila["rol"]):
            self.app.toast("No tienes permisos sobre ese rol.", "error")
            return
        activar = not fila["activo"]
        if not activar and fila["rol"] == "SUPERADMIN":
            with get_conn() as con:
                otros = con.execute(
                    "SELECT COUNT(*) AS c FROM usuarios WHERE rol="
                    "'SUPERADMIN' AND activo=1 AND id!=?",
                    (fila["id"],)).fetchone()["c"]
            if otros == 0:
                self.app.toast(
                    "Debe quedar al menos un SUPERADMIN activo.",
                    "error"); return
        verbo = "activar" if activar else "desactivar"
        if not ConfirmDialog.yes_no("Confirmar",
                f"Confirma {verbo} al usuario {fila['usuario']}?"):
            return
        with get_conn() as con:
            con.execute("UPDATE usuarios SET activo=? WHERE id=?",
                        (1 if activar else 0, fila["id"]))
        registrar_auditoria(
            self.app.usuario["usuario"],
            "ACTIVAR_USUARIO" if activar else "DESACTIVAR_USUARIO",
            fila["usuario"])
        self.app.toast(f"Usuario {fila['usuario']} {verbo}.",
                       "success" if activar else "warning")
        self._refrescar()

    def _guardar(self):
        if self.modo == "LISTADO": return
        rol_elegido = self.fields["rol"].get()

        if self.modo == "ALTA":
            usuario = self.fields["usuario"].get().lower()
            nombre = self.fields["nombre"].get()
            pwd = self.fields["password"].get()
            confirma = self.fields["confirma"].get()
            if not usuario or not usuario.isascii() or " " in usuario:
                self.lbl_form_msg.configure(
                    text="Usuario invalido (sin espacios).")
                return
            if not nombre:
                self.lbl_form_msg.configure(text="Falta el nombre."); return
            if not val_password_fuerte(pwd):
                self.lbl_form_msg.configure(
                    text="La clave no cumple la politica minima.")
                return
            if pwd != confirma:
                self.lbl_form_msg.configure(
                    text="Las claves no coinciden.")
                return
            try:
                with get_conn() as con:
                    if con.execute("SELECT 1 FROM usuarios WHERE usuario=?",
                                   (usuario,)).fetchone():
                        self.lbl_form_msg.configure(
                            text=f"Ya existe el usuario '{usuario}'.")
                        return
                    salt = secrets.token_hex(16)
                    con.execute(
                        "INSERT INTO usuarios (usuario, nombre, password, "
                        "salt, rol, activo, creado, debe_cambiar_pwd, "
                        "creado_por) VALUES (?, ?, ?, ?, ?, 1, ?, 1, ?)",
                        (usuario, nombre, hash_password(pwd, salt), salt,
                         rol_elegido,
                         datetime.now().isoformat(timespec="seconds"),
                         self.app.usuario["usuario"]))
            except sqlite3.Error as e:
                self.lbl_form_msg.configure(text=f"Error de BD: {e}")
                return
            registrar_auditoria(self.app.usuario["usuario"],
                                "ALTA_USUARIO",
                                f"{usuario} ({rol_elegido})")
            self.app.toast(
                f"Usuario {usuario} creado. Debera cambiar su "
                "clave en el primer ingreso.", "success")

        elif self.modo == "EDITAR":
            fila = self.sel_actual
            nombre = self.fields["nombre"].get()
            if not nombre:
                self.lbl_form_msg.configure(text="Falta el nombre."); return
            activo_nuevo = 1 if self.var_activo.get() else 0
            if (fila["activo"] == 1 and activo_nuevo == 0
                    and fila["rol"] == "SUPERADMIN"):
                with get_conn() as con:
                    otros = con.execute(
                        "SELECT COUNT(*) AS c FROM usuarios WHERE "
                        "rol='SUPERADMIN' AND activo=1 AND id!=?",
                        (fila["id"],)).fetchone()["c"]
                if otros == 0:
                    self.lbl_form_msg.configure(
                        text="Debe quedar al menos un SUPERADMIN activo.")
                    return
            with get_conn() as con:
                con.execute("UPDATE usuarios SET nombre=?, rol=?, activo=? "
                            "WHERE id=?",
                            (nombre, rol_elegido, activo_nuevo,
                             fila["id"]))
            registrar_auditoria(
                self.app.usuario["usuario"], "EDITAR_USUARIO",
                f"{fila['usuario']} -> rol={rol_elegido} "
                f"activo={activo_nuevo}")
            self.app.toast(f"Usuario {fila['usuario']} actualizado.",
                           "success")

        elif self.modo == "RESET":
            fila = self.sel_actual
            pwd = self.fields["password"].get()
            confirma = self.fields["confirma"].get()
            if not val_password_fuerte(pwd):
                self.lbl_form_msg.configure(
                    text="La clave no cumple la politica minima.")
                return
            if pwd != confirma:
                self.lbl_form_msg.configure(
                    text="Las claves no coinciden.")
                return
            with get_conn() as con:
                salt = secrets.token_hex(16)
                con.execute(
                    "UPDATE usuarios SET password=?, salt=?, "
                    "debe_cambiar_pwd=1, intentos_fallidos=0, "
                    "bloqueado_hasta=NULL WHERE id=?",
                    (hash_password(pwd, salt), salt, fila["id"]))
            registrar_auditoria(self.app.usuario["usuario"],
                                "RESET_PASSWORD", fila["usuario"])
            self.app.toast(f"Clave de {fila['usuario']} reseteada.",
                           "success")

        self._set_modo("LISTADO")
        self._refrescar()


# =====================================================================
#  PANEL: AUDITORIA Y ACCESOS
# =====================================================================
class PanelAuditoria(ctk.CTkFrame):
    LIMITE = 500

    def __init__(self, master, app, titulo="Auditoria", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.vista = "AUDITORIA"
        app.set_breadcrumb("Administracion", "Auditoria y accesos")
        app.set_badge("")

        tb = Card(self)
        tb.pack(fill="x", pady=(0, 12))
        wrap = ctk.CTkFrame(tb, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)

        tabs = ctk.CTkFrame(wrap, fg_color="transparent")
        tabs.pack(side="left")
        self.btn_aud = ctk.CTkButton(
            tabs, text="Log de auditoria",
            font=F(13, "bold"), height=36, corner_radius=6,
            fg_color=COLOR_ACCENT, text_color="white",
            border_color=COLOR_BORDER_STRONG, border_width=1,
            hover_color=COLOR_ACCENT_HOVER,
            command=lambda: self._cambiar_vista("AUDITORIA"))
        self.btn_aud.pack(side="left", padx=(0, 4))
        self.btn_acc = ctk.CTkButton(
            tabs, text="Log de accesos",
            font=F(13, "bold"), height=36, corner_radius=6,
            fg_color=COLOR_CARD, text_color=COLOR_TEXT,
            border_color=COLOR_BORDER_STRONG, border_width=1,
            hover_color=COLOR_ACCENT_HOVER,
            command=lambda: self._cambiar_vista("ACCESOS"))
        self.btn_acc.pack(side="left")

        self.e_q = ctk.CTkEntry(wrap, width=220, font=F(13),
                                 fg_color=COLOR_CARD,
                                 border_color=COLOR_BORDER,
                                 text_color=COLOR_TEXT, height=36,
                                 corner_radius=6,
                                 placeholder_text="Buscar por usuario...")
        self.e_q.pack(side="right", padx=(0, 8))
        self.e_q.bind("<KeyRelease>", lambda e: self._refrescar())

        self.var_solo_fallidos = ctk.BooleanVar(value=False)
        self.chk_fallidos = ctk.CTkCheckBox(
            wrap, text="Solo fallidos",
            variable=self.var_solo_fallidos,
            font=F(12), text_color=COLOR_TEXT,
            fg_color=COLOR_ACCENT,
            command=self._refrescar,
            corner_radius=4)
        self.chk_fallidos.pack(side="right", padx=8)

        self.card = Card(self)
        self.card.pack(fill="both", expand=True, pady=6)
        wrap2 = ctk.CTkFrame(self.card, fg_color="transparent")
        wrap2.pack(fill="both", expand=True, padx=14, pady=14)

        self.tabla_container = wrap2
        self.tabla = None
        self.lbl_total = ctk.CTkLabel(self.card, text="",
                                       font=F(12),
                                       text_color=COLOR_TEXT_MUTED)
        self.lbl_total.pack(pady=(0, 12))

        self._cambiar_vista("AUDITORIA")

    def _cambiar_vista(self, vista):
        self.vista = vista
        self.btn_aud.configure(
            fg_color=COLOR_ACCENT if vista == "AUDITORIA" else COLOR_CARD,
            text_color="white" if vista == "AUDITORIA" else COLOR_TEXT)
        self.btn_acc.configure(
            fg_color=COLOR_ACCENT if vista == "ACCESOS" else COLOR_CARD,
            text_color="white" if vista == "ACCESOS" else COLOR_TEXT)

        if self.tabla is not None:
            self.tabla.destroy()
        if vista == "AUDITORIA":
            self.chk_fallidos.pack_forget()
            cols = [(140, "Fecha/hora",  "fecha"),
                    (140, "Usuario",     "usuario"),
                    (180, "Accion",      "accion"),
                    (280, "Detalle",     "detalle")]
        else:
            self.chk_fallidos.pack(side="right", padx=8)
            cols = [(140, "Fecha/hora",  "fecha"),
                    (140, "Usuario",     "usuario"),
                    (100, "Resultado",   "resultado"),
                    (240, "Host",        "host")]
        self.tabla = DataTable(self.tabla_container, columns=cols)
        self.tabla.pack(fill="both", expand=True)
        self._refrescar()

    def _refrescar(self):
        if self.tabla is None: return
        q = f"%{self.e_q.get().strip().upper()}%"
        self.tabla.clear()
        if self.vista == "AUDITORIA":
            with get_conn() as con:
                rows = con.execute(
                    "SELECT fecha, usuario_actor, accion, detalle "
                    "FROM log_auditoria "
                    "WHERE UPPER(usuario_actor) LIKE ? "
                    "ORDER BY id DESC LIMIT ?",
                    (q, self.LIMITE)).fetchall()
            for r in rows:
                fecha = (r["fecha"] or "")[:16].replace("T", " ")
                self.tabla.add_row({
                    "fecha":   fecha,
                    "usuario": r["usuario_actor"] or "",
                    "accion":  r["accion"] or "",
                    "detalle": (r["detalle"] or "")[:60],
                })
        else:
            solo_fallidos = self.var_solo_fallidos.get()
            sql = ("SELECT fecha, usuario, exito, host FROM log_accesos "
                  "WHERE UPPER(usuario) LIKE ?")
            params = [q]
            if solo_fallidos: sql += " AND exito=0"
            sql += " ORDER BY id DESC LIMIT ?"
            params.append(self.LIMITE)
            with get_conn() as con:
                rows = con.execute(sql, params).fetchall()
            for r in rows:
                fecha = (r["fecha"] or "")[:16].replace("T", " ")
                self.tabla.add_row({
                    "fecha":     fecha,
                    "usuario":   r["usuario"] or "",
                    "resultado": "OK" if r["exito"] else "FALLIDO",
                    "host":      r["host"] or "",
                }, badges={"resultado":
                           "success" if r["exito"] else "danger"})
        self.lbl_total.configure(
            text=f"Mostrando {len(rows)} registros (limite {self.LIMITE}).")


# =====================================================================
#  CREDENCIALES DE SOCIO (pantalla + PDF)
# =====================================================================
CRED_ANCHO_CM = 8.6   # tamano tarjeta estandar (ISO/IEC 7810 ID-1)
CRED_ALTO_CM = 5.4


def _importar_reportlab():
    """Importa reportlab recien cuando se necesita, asi el sistema abre
    aunque no este instalado. Devuelve el modulo o None (avisando)."""
    try:
        import reportlab.pdfgen.canvas  # noqa: F401
        import reportlab.lib.units      # noqa: F401
        import reportlab.lib.utils      # noqa: F401
        import reportlab.lib.pagesizes  # noqa: F401
        import reportlab
        return reportlab
    except ImportError:
        ConfirmDialog.error(
            "Falta reportlab",
            "Para generar PDF hay que instalar reportlab.\n\n"
            "En la carpeta del programa ejecuta:\n"
            ".\\.venv\\Scripts\\python.exe -m pip install reportlab")
        return None


def _socio_para_credencial(row):
    """Normaliza una fila de socios para la credencial (sin None)."""
    s = {k: ("" if row[k] is None else str(row[k])) for k in row.keys()}
    for k in ("fec_nac", "fec_ing", "fec_baj"):
        if k in s:
            s[k] = fecha_ui(s[k])
    return s


def dibujar_credencial(pdf, s, x0=0.0, y0=0.0):
    """Dibuja una credencial en `pdf` (canvas de reportlab) con la
    esquina inferior izquierda en (x0, y0), en puntos."""
    from reportlab.lib.units import cm
    from reportlab.lib.utils import simpleSplit
    from reportlab.lib import colors

    ancho, alto = CRED_ANCHO_CM * cm, CRED_ALTO_CM * cm
    azul = colors.HexColor(COLOR_SIDEBAR)
    acento = colors.HexColor(COLOR_ACCENT)

    # Marco
    pdf.setStrokeColor(azul)
    pdf.setLineWidth(1.2)
    pdf.roundRect(x0 + 0.1 * cm, y0 + 0.1 * cm, ancho - 0.2 * cm,
                  alto - 0.2 * cm, 0.3 * cm, stroke=1, fill=0)

    # Franja superior
    franja_h = 1.1 * cm
    pdf.setFillColor(azul)
    pdf.roundRect(x0 + 0.1 * cm, y0 + alto - 0.1 * cm - franja_h,
                  ancho - 0.2 * cm, franja_h, 0.3 * cm, stroke=0, fill=1)
    # tapa las esquinas redondeadas de abajo de la franja
    pdf.rect(x0 + 0.1 * cm, y0 + alto - 0.1 * cm - franja_h,
             ancho - 0.2 * cm, 0.3 * cm, stroke=0, fill=1)
    pdf.setFillColor(colors.white)
    ent = nombre_entidad()
    if ent:
        tam = 9
        while tam > 6 and pdf.stringWidth(ent, "Helvetica-Bold", tam) > \
                ancho - 3.2 * cm:
            tam -= 0.5
        pdf.setFont("Helvetica-Bold", tam)
        pdf.drawString(x0 + 0.5 * cm, y0 + alto - 0.62 * cm, ent)
        pdf.setFont("Helvetica", 6.5)
        pdf.drawString(x0 + 0.5 * cm, y0 + alto - 0.95 * cm,
                       "CREDENCIAL DE SOCIO")
    else:
        pdf.setFont("Helvetica-Bold", 11)
        pdf.drawString(x0 + 0.5 * cm, y0 + alto - 0.75 * cm,
                       "CREDENCIAL DE SOCIO")
    pdf.setFont("Helvetica-Bold", 13)
    pdf.drawRightString(x0 + ancho - 0.5 * cm, y0 + alto - 0.8 * cm,
                        f"N° {s['nro_socio']}")

    # Datos
    pdf.setFillColor(colors.black)
    x_lbl = x0 + 0.5 * cm
    x_val = x0 + 2.4 * cm
    max_w = ancho - 2.4 * cm - 0.5 * cm
    filas = [
        ("Nombre", s["nombre"]),
        ("CUIL", s["cuil"]),
        ("Fecha nac.", s["fec_nac"]),
        ("Ingreso", s["fec_ing"]),
        ("Categoria", s["categoria"]),
    ]
    y = y0 + alto - 1.75 * cm
    for etiqueta, valor in filas:
        pdf.setFillColor(colors.HexColor(COLOR_TEXT_MUTED))
        pdf.setFont("Helvetica-Bold", 7)
        pdf.drawString(x_lbl, y, etiqueta.upper())
        pdf.setFillColor(colors.black)
        tam = 9
        while tam > 7 and pdf.stringWidth(valor, "Helvetica", tam) > max_w:
            tam -= 0.5
        lineas = simpleSplit(valor or "-", "Helvetica", tam, max_w)[:2]
        pdf.setFont("Helvetica-Bold" if etiqueta == "Nombre"
                    else "Helvetica", tam)
        for j, linea in enumerate(lineas):
            pdf.drawString(x_val, y - j * 0.33 * cm, linea)
        y -= 0.58 * cm + (len(lineas) - 1) * 0.33 * cm

    # Sello de baja
    if s.get("fec_baj"):
        pdf.saveState()
        pdf.setFillColor(colors.HexColor(COLOR_DANGER))
        pdf.setFont("Helvetica-Bold", 10)
        pdf.drawRightString(x0 + ancho - 0.5 * cm, y0 + 0.4 * cm,
                            f"BAJA {s['fec_baj']}")
        pdf.restoreState()
    else:
        pdf.setFillColor(acento)
        pdf.setFont("Helvetica", 6)
        pdf.drawRightString(x0 + ancho - 0.5 * cm, y0 + 0.4 * cm,
                            f"Emitida {datetime.now().strftime('%d/%m/%Y')}")


def generar_pdf_credencial(archivo, socio):
    """Un PDF tamano tarjeta con la credencial de un socio."""
    from reportlab.pdfgen import canvas as rl_canvas
    from reportlab.lib.units import cm
    pdf = rl_canvas.Canvas(archivo, pagesize=(CRED_ANCHO_CM * cm,
                                              CRED_ALTO_CM * cm))
    pdf.setTitle(f"Credencial socio {socio['nro_socio']}")
    dibujar_credencial(pdf, socio)
    pdf.save()


def generar_pdf_credenciales_a4(archivo, socios):
    """Varias credenciales en hojas A4 (2 x 5 por hoja) con marcas de
    corte, para imprimir y recortar."""
    from reportlab.pdfgen import canvas as rl_canvas
    from reportlab.lib.units import cm
    from reportlab.lib.pagesizes import A4
    pdf = rl_canvas.Canvas(archivo, pagesize=A4)
    pdf.setTitle("Credenciales de socios")
    hoja_w, hoja_h = A4
    w, h = CRED_ANCHO_CM * cm, CRED_ALTO_CM * cm
    cols, filas = 2, 5
    sep = 0.4 * cm
    mx = (hoja_w - cols * w - (cols - 1) * sep) / 2
    my = (hoja_h - filas * h - (filas - 1) * sep) / 2
    por_hoja = cols * filas
    for i, s in enumerate(socios):
        if i and i % por_hoja == 0:
            pdf.showPage()
        k = i % por_hoja
        c, f = k % cols, k // cols
        x = mx + c * (w + sep)
        y = hoja_h - my - (f + 1) * h - f * sep
        dibujar_credencial(pdf, s, x, y)
        # marcas de corte en las 4 esquinas
        pdf.setStrokeColorRGB(0.6, 0.6, 0.6)
        pdf.setLineWidth(0.3)
        for cx, cy in ((x, y), (x + w, y), (x, y + h), (x + w, y + h)):
            pdf.line(cx - 0.15 * cm, cy, cx + 0.15 * cm, cy)
            pdf.line(cx, cy - 0.15 * cm, cx, cy + 0.15 * cm)
    pdf.save()


class PanelCredencialSocio(ctk.CTkFrame):
    SQL_SOCIO = ("SELECT nro_socio, nombre, cuil, fec_nac, fec_ing, "
                 "fec_baj, categoria FROM socios ")

    def __init__(self, master, app, titulo="Credenciales",
                 nro_inicial=None, **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        self.socio = None
        app.set_breadcrumb("Reportes", "Credencial de socio")
        app.set_badge("")

        # --- Barra de busqueda ---
        tb = Card(self)
        tb.pack(fill="x", pady=(0, 12))
        wrap = ctk.CTkFrame(tb, fg_color="transparent")
        wrap.pack(fill="x", padx=18, pady=14)
        ctk.CTkLabel(wrap, text="Nro. socio", font=F(11),
                     text_color=COLOR_TEXT_MUTED).pack(side="left",
                                                       padx=(0, 8))
        self.e_nro = ctk.CTkEntry(wrap, width=140, font=F(14, "bold"),
                                  fg_color=COLOR_CARD,
                                  border_color=COLOR_BORDER,
                                  text_color=COLOR_TEXT, height=38,
                                  corner_radius=6, placeholder_text="1001")
        self.e_nro.pack(side="left", padx=(0, 8))
        self.e_nro.bind("<Return>", lambda e: self._buscar())
        SecondaryButton(wrap, "Buscar", "⌕", command=self._buscar,
                        width=120).pack(side="left", padx=4)
        SecondaryButton(wrap, "Listar socios", "≡",
                        command=self._listar,
                        width=150).pack(side="left", padx=4)

        # --- Vista previa ---
        card = Card(self, title="Vista previa")
        card.pack(fill="x", pady=6)
        holder = ctk.CTkFrame(card, fg_color="transparent")
        holder.pack(pady=(0, 20))
        self._build_preview(holder)

        # --- Acciones ---
        bar = Card(self)
        bar.pack(fill="x", pady=(12, 8))
        inner = ctk.CTkFrame(bar, fg_color="transparent")
        inner.pack(fill="x", padx=18, pady=14)
        ctk.CTkLabel(inner,
                     text="Todas las credenciales: un PDF A4 con 10 por "
                          "hoja, para imprimir y recortar.",
                     font=F(12), text_color=COLOR_TEXT_MUTED,
                     anchor="w").pack(side="left")
        self.btn_pdf = PrimaryButton(inner, "PDF de este socio", "⤓",
                                     command=self._pdf_uno, width=190)
        self.btn_pdf.pack(side="right", padx=4)
        AccentButton(inner, "PDF de todos los activos", "⤓",
                     command=self._pdf_todos,
                     width=230).pack(side="right", padx=4)
        self._actualizar_preview()

        if nro_inicial:
            self.e_nro.insert(0, str(nro_inicial))
            self.after(50, self._buscar)
        else:
            self.after(100, self.e_nro.focus_set)

    # ---------------------------------------------------------------
    def _build_preview(self, parent):
        # Tarjeta a escala (8.6 x 5.4 -> 430 x 270 px)
        self.cred = ctk.CTkFrame(parent, width=430, height=270,
                                 fg_color="white",
                                 border_color=COLOR_SIDEBAR, border_width=2,
                                 corner_radius=14)
        self.cred.pack()
        self.cred.pack_propagate(False)

        franja = ctk.CTkFrame(self.cred, fg_color=COLOR_SIDEBAR,
                              corner_radius=8, height=52)
        franja.pack(fill="x", padx=6, pady=(6, 0))
        franja.pack_propagate(False)
        tit = ctk.CTkFrame(franja, fg_color="transparent")
        tit.pack(side="left", padx=18)
        ent = nombre_entidad()
        if ent:
            ctk.CTkLabel(tit, text=ent, font=F(13, "bold"),
                         text_color="white", anchor="w").pack(anchor="w")
            ctk.CTkLabel(tit, text="CREDENCIAL DE SOCIO", font=F(9),
                         text_color="#cbd5e1", anchor="w").pack(anchor="w")
        else:
            ctk.CTkLabel(tit, text="CREDENCIAL DE SOCIO",
                         font=F(15, "bold"),
                         text_color="white").pack(anchor="w")
        self.p_nro = ctk.CTkLabel(franja, text="", font=F(17, "bold"),
                                  text_color="white")
        self.p_nro.pack(side="right", padx=18)

        cuerpo = ctk.CTkFrame(self.cred, fg_color="transparent")
        cuerpo.pack(fill="both", expand=True, padx=20, pady=(12, 4))
        cuerpo.grid_columnconfigure(1, weight=1)
        self.p = {}
        for i, (key, lbl) in enumerate([("nombre", "NOMBRE"),
                                        ("cuil", "CUIL"),
                                        ("fec_nac", "FECHA NAC."),
                                        ("fec_ing", "INGRESO"),
                                        ("categoria", "CATEGORIA")]):
            ctk.CTkLabel(cuerpo, text=lbl, font=F(10, "bold"),
                         text_color=COLOR_TEXT_MUTED, anchor="w",
                         width=90).grid(row=i, column=0, sticky="nw",
                                        pady=3)
            v = ctk.CTkLabel(cuerpo, text="",
                             font=F(13, "bold" if key == "nombre"
                                    else "normal"),
                             text_color=COLOR_TEXT, anchor="w",
                             justify="left", wraplength=290)
            v.grid(row=i, column=1, sticky="w", pady=3)
            self.p[key] = v
        self.p_pie = ctk.CTkLabel(self.cred, text="", font=F(11, "bold"),
                                  text_color=COLOR_DANGER, anchor="e")
        self.p_pie.pack(fill="x", padx=20, pady=(0, 10))

    def _actualizar_preview(self):
        s = self.socio
        if not s:
            self.p_nro.configure(text="N° ----")
            for k, lbl in self.p.items():
                lbl.configure(text="-", text_color=COLOR_TEXT_LIGHT)
            self.p_pie.configure(text="Busca un socio para ver su "
                                      "credencial.",
                                 text_color=COLOR_TEXT_LIGHT)
            self.btn_pdf.configure(state="disabled")
            return
        self.p_nro.configure(text=f"N° {s['nro_socio']}")
        for k, lbl in self.p.items():
            lbl.configure(text=s[k] or "-", text_color=COLOR_TEXT)
        if s["fec_baj"]:
            self.p_pie.configure(text=f"BAJA {s['fec_baj']}",
                                 text_color=COLOR_DANGER)
        else:
            self.p_pie.configure(
                text=f"Emitida {datetime.now().strftime('%d/%m/%Y')}",
                text_color=COLOR_ACCENT)
        self.btn_pdf.configure(state="normal")

    # ---------------------------------------------------------------
    def _buscar(self):
        nro = self.e_nro.get().strip()
        if not nro.isdigit():
            self.app.toast("Nro. socio invalido.", "error"); return
        with get_conn() as con:
            row = con.execute(self.SQL_SOCIO + "WHERE nro_socio=?",
                              (int(nro),)).fetchone()
        if not row:
            self.socio = None
            self._actualizar_preview()
            self.app.toast(f"Socio {nro} no existe.", "warning"); return
        self.socio = _socio_para_credencial(row)
        self._actualizar_preview()
        if self.socio["fec_baj"]:
            self.app.toast(f"Atencion: el socio {nro} esta dado de baja.",
                           "warning")

    def _listar(self):
        VentanaListaSocios(self.app, callback=self._elegido)

    def _elegido(self, nro):
        self.e_nro.delete(0, "end")
        self.e_nro.insert(0, str(nro))
        self._buscar()

    def _pdf_uno(self):
        s = self.socio
        if not s:
            self.app.toast("Primero busca un socio.", "warning"); return
        if s["fec_baj"] and not ConfirmDialog.yes_no(
                "Socio dado de baja",
                f"El socio {s['nro_socio']} tiene fecha de baja "
                f"{s['fec_baj']}.\nEmitir la credencial igual?"):
            return
        if not _importar_reportlab():
            return
        archivo = filedialog.asksaveasfilename(
            title="Guardar credencial", defaultextension=".pdf",
            filetypes=[("PDF", "*.pdf")],
            initialfile=f"Credencial_{s['nro_socio']}.pdf")
        if not archivo:
            return
        try:
            generar_pdf_credencial(archivo, s)
        except Exception as e:
            ConfirmDialog.error("PDF", f"No se pudo generar el PDF:\n{e}")
            return
        registrar_auditoria(self.app.usuario["usuario"], "CREDENCIAL_PDF",
                            f"socio={s['nro_socio']} archivo={archivo}")
        self.app.toast("Credencial generada.", "success")
        if ConfirmDialog.yes_no("PDF", f"Credencial guardada en:\n"
                                       f"{archivo}\n\nAbrir la carpeta?"):
            abrir_carpeta(os.path.dirname(archivo))

    def _pdf_todos(self):
        with get_conn() as con:
            rows = con.execute(
                self.SQL_SOCIO + "WHERE COALESCE(fec_baj,'') = '' "
                "ORDER BY nro_socio").fetchall()
        if not rows:
            self.app.toast("No hay socios activos.", "warning"); return
        hojas = (len(rows) + 9) // 10
        if not ConfirmDialog.yes_no(
                "Credenciales",
                f"Se van a generar {len(rows)} credenciales "
                f"({hojas} hoja/s A4).\nContinuar?"):
            return
        if not _importar_reportlab():
            return
        archivo = filedialog.asksaveasfilename(
            title="Guardar credenciales", defaultextension=".pdf",
            filetypes=[("PDF", "*.pdf")],
            initialfile=f"Credenciales_"
                        f"{datetime.now().strftime('%Y%m%d')}.pdf")
        if not archivo:
            return
        try:
            generar_pdf_credenciales_a4(
                archivo, [_socio_para_credencial(r) for r in rows])
        except Exception as e:
            ConfirmDialog.error("PDF", f"No se pudo generar el PDF:\n{e}")
            return
        registrar_auditoria(self.app.usuario["usuario"],
                            "CREDENCIALES_PDF",
                            f"cantidad={len(rows)} archivo={archivo}")
        self.app.toast(f"{len(rows)} credenciales generadas.", "success")
        if ConfirmDialog.yes_no("PDF", f"Credenciales guardadas en:\n"
                                       f"{archivo}\n\nAbrir la carpeta?"):
            abrir_carpeta(os.path.dirname(archivo))


# =====================================================================
#  TERMINOS Y CONDICIONES / PROGRAMADORES
# =====================================================================
PROGRAMADORES = [
    ("Diego Alejandro Fernandez", "11 6437-6391"),
    ("Joshua Giuliano Venticinque", "11 3594-6259"),
]


def _contactos_txt():
    return "\n".join(f"  -  {n}  -  Tel. {t}" for n, t in PROGRAMADORES)


# Si se cambia el texto de los terminos, subir TERMINOS_VERSION: todos los
# usuarios tendran que volver a aceptarlos.
TERMINOS_VERSION = "1"

TERMINOS_TXT = (
    "NovaMut - Sistema de Gestion Mutual\n"
    "Terminos y condiciones de uso\n\n"
    "1. Este programa es de uso exclusivo de la entidad a la que fue "
    "entregado por sus autores.\n\n"
    "2. Queda prohibida su copia, distribucion, venta, prestamo, "
    "publicacion o entrega a terceros, total o parcial, por cualquier "
    "medio, sin autorizacion escrita de sus autores.\n\n"
    "3. Queda prohibido modificar, descompilar o intentar obtener el "
    "codigo fuente del programa sin autorizacion de sus autores.\n\n"
    "4. Quien quiera obtener el programa o una licencia de uso debe "
    "contactarse con los programadores:\n\n"
    + _contactos_txt() + "\n\n"
    "5. La informacion cargada en el sistema es responsabilidad de la "
    "entidad usuaria, que debe conservar copias de seguridad.\n\n"
    "Al presionar \"Acepto\" declaras haber leido y aceptado estos "
    "terminos. Cada usuario los acepta una sola vez; si no los aceptas, "
    "el programa se cierra."
)


class PanelTerminos(ctk.CTkFrame):
    """Se muestra cada vez que se abre el programa, antes del login."""

    def __init__(self, master, app, **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        ctk.CTkFrame(self, fg_color="transparent", height=10).pack()
        card = ctk.CTkFrame(self, fg_color=COLOR_CARD,
                            border_color=COLOR_BORDER, border_width=1,
                            corner_radius=12)
        card.pack(padx=20, pady=10)

        ctk.CTkLabel(card, text="Terminos y condiciones",
                     font=F(22, "bold"),
                     text_color=COLOR_TEXT).pack(pady=(24, 4), padx=40)
        ctk.CTkLabel(card, text="Lee y acepta para continuar",
                     font=F(12), text_color=COLOR_TEXT_MUTED).pack(
                     pady=(0, 14))

        box = ctk.CTkTextbox(card, width=640, height=360, font=F(13),
                             fg_color=COLOR_BG, border_color=COLOR_BORDER,
                             border_width=1, corner_radius=8,
                             text_color=COLOR_TEXT, wrap="word")
        box.pack(padx=32)
        box.insert("1.0", TERMINOS_TXT)
        box.configure(state="disabled")

        btns = ctk.CTkFrame(card, fg_color="transparent")
        btns.pack(pady=(18, 24))
        DangerButton(btns, "No acepto", "✕", command=self._rechazar,
                     width=170, height=42).pack(side="left", padx=6)
        PrimaryButton(btns, "Acepto", "✓", command=self._aceptar,
                      width=170, height=42).pack(side="left", padx=6)

    def _aceptar(self):
        self.app.terminos_aceptados()

    def _rechazar(self):
        self.app.terminos_rechazados()


class PanelProgramadores(ctk.CTkFrame):
    def __init__(self, master, app, titulo="Programadores", **kwargs):
        super().__init__(master, fg_color="transparent")
        self.app = app
        app.set_breadcrumb("Acerca de", "Programadores")
        app.set_badge("")

        card = Card(self, title="Desarrollado por")
        card.pack(fill="x", pady=(0, 12))
        grid = ctk.CTkFrame(card, fg_color="transparent")
        grid.pack(fill="x", padx=18, pady=(0, 18))
        grid.grid_columnconfigure((0, 1), weight=1)
        for i, (nombre, tel) in enumerate(PROGRAMADORES):
            c = ctk.CTkFrame(grid, fg_color=COLOR_BG,
                             border_color=COLOR_BORDER, border_width=1,
                             corner_radius=10)
            c.grid(row=0, column=i, sticky="nsew", padx=6)
            partes = nombre.split()
            ini = (partes[0][0] + partes[-1][0]).upper()
            av = ctk.CTkFrame(c, fg_color=COLOR_ACCENT_BG, corner_radius=28,
                              width=56, height=56)
            av.pack(anchor="w", padx=18, pady=(18, 10))
            av.pack_propagate(False)
            ctk.CTkLabel(av, text=ini, font=F(18, "bold"),
                         text_color=COLOR_ACCENT).pack(expand=True)
            ctk.CTkLabel(c, text=nombre, font=F(16, "bold"),
                         text_color=COLOR_TEXT, anchor="w").pack(
                         fill="x", padx=18)
            ctk.CTkLabel(c, text=f"Tel. {tel}", font=F(14),
                         text_color=COLOR_TEXT_MUTED, anchor="w").pack(
                         fill="x", padx=18, pady=(2, 18))

        card2 = Card(self, title="Licencia")
        card2.pack(fill="x", pady=6)
        ctk.CTkLabel(card2,
                     text="NovaMut es de uso exclusivo de la entidad "
                          "autorizada. Prohibida su copia o distribucion "
                          "sin autorizacion de los autores. Para obtener "
                          "el programa o una licencia, contactate con los "
                          "programadores.",
                     font=F(13), text_color=COLOR_TEXT, justify="left",
                     anchor="w", wraplength=820).pack(
                     fill="x", padx=18, pady=(0, 12))
        SecondaryButton(card2, "Ver terminos y condiciones completos",
                        command=self._ver_terminos,
                        width=300).pack(anchor="w", padx=18, pady=(0, 18))

        ctk.CTkLabel(self, text=f"{APP_NOMBRE} version {APP_VERSION}",
                     font=F(11), text_color=COLOR_TEXT_LIGHT).pack(
                     anchor="w", pady=(10, 0))

    def _ver_terminos(self):
        ConfirmDialog.info("Terminos y condiciones", TERMINOS_TXT)


if __name__ == "__main__":
    init_db()
    app = NovaMutApp()
    app.mainloop()
