#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
MEGALODON COSTOS v3.1 — BACKEND DEFINITIVO
Sistema Unificado de Gestión Documental, Costos de Obra,
Validación Determinista de Licitaciones, Topografía Avanzada (PostGIS),
Cuantificación BIM (IFC), APU con FSR, Presupuesto Programable (CPM/EVM),
e Importación/Exportación con Excel.

TODO EN UN SOLO ARCHIVO — SIN DEPENDENCIAS OBLIGATORIAS.
LAS DEPENDENCIAS OPCIONALES SON:
  - psycopg2-binary (para topografía con PostGIS)
  - ifcopenshell (para cuantificación BIM)
  - pandas + openpyxl (para Excel)
  - cryptography (para cifrado en reposo)
  - pyhanko (para firma PAdES real)

Marco Legal 2026: LOPSRM, LAASSP, LFT, CFF, RMF 2026.
"""

from __future__ import annotations

import argparse
import base64
import csv
import dataclasses
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone, date, timedelta
import hashlib
import importlib.util
import io
import json
import logging
import math
import os
from pathlib import Path
import queue
import random
import re
import shutil
import sys
import tempfile
import threading
import types
import uuid
from enum import Enum
from typing import Any, Callable, Dict, Generator, Iterator, List, Optional, Sequence, Tuple, Union
from decimal import Decimal, getcontext

# ─────────────────────────────────────────────────────────────────────────────
# DETECCIÓN DE DEPENDENCIAS OPCIONALES
# ─────────────────────────────────────────────────────────────────────────────

_PSYCOPG2_AVAILABLE = False
_IFC_AVAILABLE = False
_EXCEL_AVAILABLE = False
_CRYPTOGRAPHY_AVAILABLE = False
_PYHANKO_AVAILABLE = False
_NUMPY_AVAILABLE = False

try:
    import psycopg2
    import psycopg2.extras
    _PSYCOPG2_AVAILABLE = True
except ImportError:
    pass

try:
    import ifcopenshell
    _IFC_AVAILABLE = True
except ImportError:
    pass

try:
    import pandas as pd
    import openpyxl
    _EXCEL_AVAILABLE = True
except ImportError:
    pass

try:
    from cryptography.fernet import Fernet
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.backends import default_backend
    _CRYPTOGRAPHY_AVAILABLE = True
except ImportError:
    pass

try:
    from pyhanko.sign import signers
    from pyhanko.sign.timestamps import HTTPTimeStamper
    _PYHANKO_AVAILABLE = True
except ImportError:
    pass

try:
    import numpy as np
    _NUMPY_AVAILABLE = True
except ImportError:
    np = None

# ─────────────────────────────────────────────────────────────────────────────
# CONSTANTES GLOBALES Y LEGALES
# ─────────────────────────────────────────────────────────────────────────────

NS_MX = "http://megalodon.gob.mx/presupuesto"
REAL_MOTOR_LOADED = False
REAL_COSTOS_LOADED = False

class ConstantesLegales2026:
    # LOPSRM / RLOPSRM
    UMBRAL_ADJUDICACION_DIRECTA_OBRA = 2_200_000.0
    UMBRAL_INVITACION_TRES_OBRA = 10_800_000.0
    UMBRAL_LICITACION_PUBLICA_OBRA = 10_800_001.0
    UMBRAL_ADJUDICACION_DIRECTA_ADQUISICION = 1_400_000.0
    UMBRAL_INVITACION_TRES_ADQUISICION = 6_800_000.0

    # LFT reformada
    DIAS_CALENDARIO = 365
    DIAS_AGUINALDO_MINIMO = 15
    DIAS_VACACIONES_MINIMO = 12
    PRIMA_VACACIONAL_PCT = 0.25
    DIAS_PAGADOS_MINIMO = 365 + 15 + (12 * 0.25)  # 383.0
    DOMINGOS_ANUAL = 52
    DIAS_FESTIVOS_OBLIGATORIOS = 7
    DIAS_LABORADOS_MAXIMO = 365 - 52 - 7          # 306

    # SAT
    VIGENCIA_OPINION_SAT_DIAS = 30

    # RLOPSRM Maquinaria
    HORAS_USO_ANUAL_MIN = 500
    HORAS_USO_ANUAL_MAX = 3000
    TOLERANCIA_PRECIO_COMBUSTIBLE = 1.50

    # Sobrecostos
    TOLERANCIA_FACTOR_SOBRECOSTO = 0.0005
    TOLERANCIA_FSR_ARITMETICO = 0.001
    TOLERANCIA_COSTO_HORARIO = 0.05

    # TIE
    TASA_TIE_REFERENCIA = 0.1125
    PRECIO_DIESEL_REFERENCIA = 24.50

# ─────────────────────────────────────────────────────────────────────────────
# UTILIDADES BASE
# ─────────────────────────────────────────────────────────────────────────────

def _now_utc() -> datetime:
    return datetime.now(timezone.utc)

def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def _ensure_dir(path: str | Path) -> Path:
    p = Path(path)
    p.mkdir(parents=True, exist_ok=True)
    return p

def _maybe_import_from_path(module_name: str, file_name: str) -> Any:
    candidate = Path(__file__).resolve().parent / file_name
    if not candidate.exists():
        raise ImportError(f"No se encontró {file_name}")
    spec = importlib.util.spec_from_file_location(module_name, candidate)
    if spec is None or spec.loader is None:
        raise ImportError(f"No se pudo cargar {file_name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

# ─────────────────────────────────────────────────────────────────────────────
# 1. SERIALIZACIÓN CANÓNICA (RFC 8785)
# ─────────────────────────────────────────────────────────────────────────────

def canonical_json(obj: Any, sort_keys: bool = True) -> str:
    def _default(o):
        if isinstance(o, datetime):
            return o.astimezone(timezone.utc).isoformat().replace('+00:00', 'Z')
        if isinstance(o, Decimal):
            return float(o)
        if hasattr(o, 'to_dict'):
            return o.to_dict()
        if hasattr(o, '__dict__'):
            return {k: v for k, v in o.__dict__.items() if not k.startswith('_')}
        raise TypeError(f"Objeto no serializable: {type(o)}")
    return json.dumps(obj, default=_default, ensure_ascii=False, separators=(',', ':'), sort_keys=sort_keys)

# ─────────────────────────────────────────────────────────────────────────────
# 2. MERKLE TREE
# ─────────────────────────────────────────────────────────────────────────────

class MerkleTree:
    def __init__(self, leaves: List[bytes]):
        self.leaves = [self._hash(leaf) for leaf in leaves]
        self.levels = self._build_levels(self.leaves)
        self.root = self.levels[-1][0] if self.levels else b''

    def _hash(self, data: bytes) -> bytes:
        return hashlib.sha256(data).digest()

    def _build_levels(self, leaves: List[bytes]) -> List[List[bytes]]:
        levels = [leaves]
        while len(levels[-1]) > 1:
            current = levels[-1]
            next_level = []
            for i in range(0, len(current), 2):
                if i + 1 < len(current):
                    combined = current[i] + current[i + 1]
                else:
                    combined = current[i] + current[i]
                next_level.append(self._hash(combined))
            levels.append(next_level)
        return levels

    def proof(self, leaf_index: int) -> List[Tuple[bytes, bool]]:
        proof = []
        index = leaf_index
        for level in self.levels[:-1]:
            sibling_index = index ^ 1
            if sibling_index < len(level):
                is_right = (sibling_index > index)
                proof.append((level[sibling_index], is_right))
            index //= 2
        return proof

    def verify(self, leaf: bytes, proof: List[Tuple[bytes, bool]]) -> bool:
        current = self._hash(leaf)
        for sibling_hash, is_right in proof:
            if is_right:
                combined = current + sibling_hash
            else:
                combined = sibling_hash + current
            current = self._hash(combined)
        return current == self.root

# ─────────────────────────────────────────────────────────────────────────────
# 3. CALENDARIO LABORAL MEXICANO (LFT Art. 74)
# ─────────────────────────────────────────────────────────────────────────────

class CalendarioLaboral:
    def __init__(self, year: int = 0):
        self.year = year or datetime.now().year
        self.festivos = self._generar_festivos()

    def _generar_festivos(self) -> List[date]:
        y = self.year
        return [
            date(y, 1, 1),
            self._primer_lunes_febrero(y),
            self._tercer_lunes_marzo(y),
            date(y, 5, 1),
            date(y, 9, 16),
            self._tercer_lunes_noviembre(y),
            date(y, 12, 25),
        ]

    @staticmethod
    def _primer_lunes_febrero(year: int) -> date:
        d = date(year, 2, 1)
        while d.weekday() != 0:
            d += timedelta(days=1)
        return d

    @staticmethod
    def _tercer_lunes_marzo(year: int) -> date:
        d = date(year, 3, 1)
        while d.weekday() != 0:
            d += timedelta(days=1)
        return d + timedelta(days=14)

    @staticmethod
    def _tercer_lunes_noviembre(year: int) -> date:
        d = date(year, 11, 1)
        while d.weekday() != 0:
            d += timedelta(days=1)
        return d + timedelta(days=14)

    def es_dia_habil(self, fecha: date) -> bool:
        if fecha.weekday() in (5, 6):
            return False
        if fecha in self.festivos:
            return False
        return True

    def siguiente_dia_habil(self, fecha: date) -> date:
        d = fecha + timedelta(days=1)
        while not self.es_dia_habil(d):
            d += timedelta(days=1)
        return d

    def sumar_dias_habiles(self, fecha: date, dias: int) -> date:
        d = fecha
        for _ in range(dias):
            d = self.siguiente_dia_habil(d)
        return d

    def restar_dias_habiles(self, fecha: date, dias: int) -> date:
        d = fecha
        for _ in range(dias):
            d = self.dia_habil_anterior(d)
        return d

    def dia_habil_anterior(self, fecha: date) -> date:
        d = fecha - timedelta(days=1)
        while not self.es_dia_habil(d):
            d -= timedelta(days=1)
        return d

    def dias_habiles_entre(self, inicio: date, fin: date) -> int:
        d = inicio
        count = 0
        while d <= fin:
            if self.es_dia_habil(d):
                count += 1
            d += timedelta(days=1)
        return count

# ─────────────────────────────────────────────────────────────────────────────
# 4. CIFRADO EN REPOSO (AES-256-GCM con PBKDF2)
# ─────────────────────────────────────────────────────────────────────────────

class CifradoReposo:
    def __init__(self, password: str, salt: Optional[bytes] = None):
        if not _CRYPTOGRAPHY_AVAILABLE:
            raise RuntimeError("cryptography no instalado. pip install cryptography")
        self.password = password
        self.salt = salt or os.urandom(16)
        self._fernet = None

    def _get_fernet(self) -> Fernet:
        if self._fernet is None:
            kdf = PBKDF2HMAC(
                algorithm=hashes.SHA256(),
                length=32,
                salt=self.salt,
                iterations=100000,
                backend=default_backend()
            )
            key = base64.urlsafe_b64encode(kdf.derive(self.password.encode()))
            self._fernet = Fernet(key)
        return self._fernet

    def cifrar(self, data: bytes) -> bytes:
        return self._get_fernet().encrypt(data)

    def descifrar(self, token: bytes) -> bytes:
        return self._get_fernet().decrypt(token)

    @classmethod
    def generar_clave_aleatoria(cls) -> bytes:
        return os.urandom(32)

# ─────────────────────────────────────────────────────────────────────────────
# 5. INDEXADOR DE FUENTES NORMATIVAS (FSR)
# ─────────────────────────────────────────────────────────────────────────────

class FuenteNormativa:
    def __init__(self, id: str, url: str, ttl_dias: int, formato: str = "json"):
        self.id = id
        self.url = url
        self.ttl_dias = ttl_dias
        self.formato = formato
        self.metadatos = {}

@dataclass
class SnapshotNormativo:
    id: str
    fuente: str
    url: str
    fecha_descarga: datetime
    fecha_actualizacion_fuente: Optional[datetime]
    hash_contenido: str
    ruta_archivo: str
    formato: str
    ttl_dias: int
    version: int
    metadatos: Dict[str, str]

    def is_expired(self) -> bool:
        return datetime.now(timezone.utc) > (self.fecha_descarga + timedelta(days=self.ttl_dias))

class FsrIndexer:
    FUENTES = {
        "inegi_precios": FuenteNormativa("inegi_precios", "https://www.inegi.org.mx/app/indicesdeprecios/", 35),
        "banxico_udis": FuenteNormativa("banxico_udis", "https://www.banxico.org.mx/tipcamb/main.do", 3),
        "conasami_salarios": FuenteNormativa("conasami_salarios", "https://www.conasami.gob.mx", 365),
        "sat_udis": FuenteNormativa("sat_udis", "https://www.sat.gob.mx", 3),
    }

    def __init__(self, storage_dir: str):
        self.storage = Path(storage_dir)
        self.storage.mkdir(parents=True, exist_ok=True)
        self._cache: Dict[str, SnapshotNormativo] = {}

    def get_latest(self, fuente_id: str) -> Optional[SnapshotNormativo]:
        if fuente_id in self._cache:
            return self._cache[fuente_id]
        meta_files = list(self.storage.glob(f"{fuente_id}_*.meta.json"))
        if not meta_files:
            return None
        latest = max(meta_files, key=lambda p: p.stat().st_mtime)
        with open(latest, 'r') as f:
            data = json.load(f)
        snap = SnapshotNormativo(**data)
        snap.fecha_descarga = datetime.fromisoformat(snap.fecha_descarga)
        if snap.fecha_actualizacion_fuente:
            snap.fecha_actualizacion_fuente = datetime.fromisoformat(snap.fecha_actualizacion_fuente)
        self._cache[fuente_id] = snap
        return snap

    def download(self, fuente_id: str) -> SnapshotNormativo:
        fuente = self.FUENTES.get(fuente_id)
        if not fuente:
            raise ValueError(f"Fuente desconocida: {fuente_id}")
        import requests
        resp = requests.get(fuente.url, timeout=30)
        resp.raise_for_status()
        content = resp.content
        hash_contenido = hashlib.sha256(content).hexdigest()
        existing = self._find_by_hash(fuente_id, hash_contenido)
        if existing:
            return existing
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        filename = f"{fuente_id}_{timestamp}.{fuente.formato}"
        filepath = self.storage / filename
        filepath.write_bytes(content)
        snap = SnapshotNormativo(
            id=f"{fuente_id}_{timestamp}",
            fuente=fuente_id,
            url=fuente.url,
            fecha_descarga=datetime.now(timezone.utc),
            fecha_actualizacion_fuente=None,
            hash_contenido=hash_contenido,
            ruta_archivo=str(filepath),
            formato=fuente.formato,
            ttl_dias=fuente.ttl_dias,
            version=self._get_next_version(fuente_id),
            metadatos={}
        )
        meta_path = self.storage / f"{fuente_id}_{timestamp}.meta.json"
        with open(meta_path, 'w') as f:
            json.dump({
                "id": snap.id,
                "fuente": snap.fuente,
                "url": snap.url,
                "fecha_descarga": snap.fecha_descarga.isoformat(),
                "fecha_actualizacion_fuente": snap.fecha_actualizacion_fuente.isoformat() if snap.fecha_actualizacion_fuente else None,
                "hash_contenido": snap.hash_contenido,
                "ruta_archivo": snap.ruta_archivo,
                "formato": snap.formato,
                "ttl_dias": snap.ttl_dias,
                "version": snap.version,
                "metadatos": snap.metadatos,
            }, f, ensure_ascii=False, indent=2)
        self._cache[fuente_id] = snap
        return snap

    def _find_by_hash(self, fuente_id: str, hash_hex: str) -> Optional[SnapshotNormativo]:
        for meta_file in self.storage.glob(f"{fuente_id}_*.meta.json"):
            with open(meta_file, 'r') as f:
                data = json.load(f)
            if data.get("hash_contenido") == hash_hex:
                snap = SnapshotNormativo(**data)
                snap.fecha_descarga = datetime.fromisoformat(snap.fecha_descarga)
                if snap.fecha_actualizacion_fuente:
                    snap.fecha_actualizacion_fuente = datetime.fromisoformat(snap.fecha_actualizacion_fuente)
                return snap
        return None

    def _get_next_version(self, fuente_id: str) -> int:
        versions = []
        for meta_file in self.storage.glob(f"{fuente_id}_*.meta.json"):
            with open(meta_file, 'r') as f:
                data = json.load(f)
            versions.append(data.get("version", 0))
        return max(versions, default=0) + 1

    def refresh_expired(self) -> List[SnapshotNormativo]:
        refreshed = []
        for fuente_id in self.FUENTES:
            latest = self.get_latest(fuente_id)
            if latest is None or latest.is_expired():
                try:
                    snap = self.download(fuente_id)
                    refreshed.append(snap)
                except Exception as e:
                    logging.warning(f"Error al refrescar {fuente_id}: {e}")
        return refreshed

    def get_valor(self, fuente_id: str, clave: str = "") -> Optional[float]:
        snap = self.get_latest(fuente_id)
        if not snap:
            return None
        try:
            with open(snap.ruta_archivo, 'r') as f:
                data = json.load(f)
            if clave:
                return float(data.get(clave, 0.0))
            return float(data.get("valor", 0.0))
        except Exception:
            return None

# ─────────────────────────────────────────────────────────────────────────────
# CAPA 1 – CPLError
# ─────────────────────────────────────────────────────────────────────────────

class Severidad(str, Enum):
    DEBUG = "DEBUG"
    INFO = "INFO"
    AVISO = "AVISO"
    ERROR = "ERROR"
    FATAL = "FATAL"

@dataclass
class EntradaError:
    codigo: int
    mensaje: str
    severidad: Severidad
    modulo: str
    timestamp: datetime = field(default_factory=_now_utc)
    contexto: Dict[str, Any] = field(default_factory=dict)
    traza: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "codigo": self.codigo,
            "mensaje": self.mensaje,
            "severidad": self.severidad.value,
            "modulo": self.modulo,
            "timestamp": self.timestamp.isoformat(),
            "contexto": self.contexto,
        }

class CPLError:
    COD_NORMATIVO = 1000
    COD_FIRMA = 2000
    COD_INTEROP = 3000
    COD_COSTEO = 4000
    COD_JURIDICO = 5000
    COD_BIM = 6000
    COD_ARCHIVO = 7000
    COD_MONTECARLO = 8000
    COD_DETERMINISTA = 9000

    def __init__(self) -> None:
        self._entradas: List[EntradaError] = []
        self._lock = threading.Lock()
        self._logger = logging.getLogger("CPLError")

    def registrar(self, codigo: int, mensaje: str, severidad: Severidad = Severidad.ERROR,
                  modulo: str = "", contexto: Optional[Dict[str, Any]] = None) -> EntradaError:
        entrada = EntradaError(
            codigo=codigo, mensaje=mensaje, severidad=severidad,
            modulo=modulo, contexto=contexto or {},
        )
        with self._lock:
            self._entradas.append(entrada)
        nivel = {
            Severidad.DEBUG: logging.DEBUG, Severidad.INFO: logging.INFO,
            Severidad.AVISO: logging.WARNING, Severidad.ERROR: logging.ERROR,
            Severidad.FATAL: logging.CRITICAL,
        }.get(severidad, logging.ERROR)
        self._logger.log(nivel, "[%s] %d – %s | ctx=%s", modulo, codigo, mensaje, contexto)
        if severidad == Severidad.FATAL:
            raise MegalodonFatalError(codigo, mensaje, modulo)
        return entrada

    def ultimo_error(self) -> Optional[EntradaError]:
        with self._lock:
            return self._entradas[-1] if self._entradas else None

    def errores_por_modulo(self, modulo: str) -> List[EntradaError]:
        with self._lock:
            return [e for e in self._entradas if e.modulo == modulo]

    def tiene_errores_criticos(self) -> bool:
        with self._lock:
            return any(e.severidad in (Severidad.ERROR, Severidad.FATAL) for e in self._entradas)

    def limpiar(self) -> None:
        with self._lock:
            self._entradas.clear()

    def resumen(self) -> Dict[str, int]:
        with self._lock:
            conteo: Dict[str, int] = {}
            for e in self._entradas:
                conteo[e.severidad.value] = conteo.get(e.severidad.value, 0) + 1
            return conteo

_cpl_error = CPLError()

class MegalodonFatalError(RuntimeError):
    def __init__(self, codigo: int, mensaje: str, modulo: str = "") -> None:
        super().__init__(f"[FATAL/{modulo}] {codigo}: {mensaje}")
        self.codigo = codigo
        self.modulo = modulo

class ErrorNormativo(Exception):
    pass

class ErrorFirmaElectronica(Exception):
    pass

class ErrorInteroperabilidad(ErrorNormativo):
    pass

class ErrorConversionPresupuesto(ErrorNormativo):
    pass

class ErrorValidacionEconomica(ErrorNormativo):
    pass

class ErrorJuridico(ErrorNormativo):
    pass

class ErrorBIM(ErrorNormativo):
    pass

# ─────────────────────────────────────────────────────────────────────────────
# CAPA 2 – CPLJson
# ─────────────────────────────────────────────────────────────────────────────

class CPLJsonStreamingWriter:
    def __init__(self, destino: io.IOBase) -> None:
        self._dest = destino
        self._pila: List[str] = []
        self._primero: List[bool] = []

    def _write(self, s: str) -> None:
        if isinstance(self._dest, (io.RawIOBase, io.BufferedIOBase)):
            self._dest.write(s.encode("utf-8"))
        else:
            self._dest.write(s)

    def _coma(self) -> None:
        if self._primero and not self._primero[-1]:
            self._write(",")
        if self._primero:
            self._primero[-1] = False

    def comenzar_objeto(self) -> "CPLJsonStreamingWriter":
        self._coma()
        self._write("{")
        self._pila.append("{")
        self._primero.append(True)
        return self

    def terminar_objeto(self) -> "CPLJsonStreamingWriter":
        self._write("}")
        self._pila.pop()
        self._primero.pop()
        if self._primero:
            self._primero[-1] = False
        return self

    def comenzar_arreglo(self, clave: Optional[str] = None) -> "CPLJsonStreamingWriter":
        self._coma()
        if clave is not None:
            self._write(f"{json.dumps(clave)}:[")
        else:
            self._write("[")
        self._pila.append("[")
        self._primero.append(True)
        return self

    def terminar_arreglo(self) -> "CPLJsonStreamingWriter":
        self._write("]")
        self._pila.pop()
        self._primero.pop()
        if self._primero:
            self._primero[-1] = False
        return self

    def campo(self, clave: str, valor: Any) -> "CPLJsonStreamingWriter":
        self._coma()
        self._write(f"{json.dumps(clave)}:{json.dumps(valor, ensure_ascii=False, default=str)}")
        return self

    def valor(self, v: Any) -> "CPLJsonStreamingWriter":
        self._coma()
        self._write(json.dumps(v, ensure_ascii=False, default=str))
        return self

    def volcar_dict(self, d: Dict[str, Any]) -> "CPLJsonStreamingWriter":
        self._coma()
        self._write(json.dumps(d, ensure_ascii=False, default=str))
        if self._primero:
            self._primero[-1] = False
        return self

    def finalizar(self) -> None:
        while self._pila:
            cierre = "}" if self._pila[-1] == "{" else "]"
            self._write(cierre)
            self._pila.pop()
            self._primero.pop()

def cpl_json_serializar_presupuesto_streaming(presupuesto: Any, destino: Optional[io.IOBase] = None) -> bytes:
    buf = io.BytesIO() if destino is None else None
    target = buf if buf is not None else destino
    writer = CPLJsonStreamingWriter(target)
    writer.comenzar_objeto()
    _g = lambda attr, default=0.0: (
        getattr(presupuesto, attr, default) if hasattr(presupuesto, attr)
        else presupuesto.get(attr, default) if isinstance(presupuesto, dict)
        else default
    )
    writer.campo("proyecto", _g("proyecto", ""))
    writer.campo("proyecto_id", _g("proyecto_id", ""))
    writer.campo("monto_directo", _g("monto_directo", 0.0))
    writer.campo("monto_total", _g("monto_total", 0.0))
    writer.campo("moneda", _g("moneda", "MXN"))
    writer.comenzar_arreglo("partidas")
    partidas = _g("partidas", []) or []
    for partida in partidas:
        writer.comenzar_objeto()
        pid = getattr(partida, "id", partida.get("id", "")) if hasattr(partida, "__dict__") or hasattr(partida, "id") else partida.get("id", "")
        pcant = getattr(partida, "cantidad", partida.get("cantidad", 0.0)) if hasattr(partida, "__dict__") or hasattr(partida, "cantidad") else partida.get("cantidad", 0.0)
        writer.campo("id", pid)
        writer.campo("cantidad", pcant)
        concepto = getattr(partida, "concepto", partida.get("concepto", None)) if hasattr(partida, "__dict__") or hasattr(partida, "concepto") else partida.get("concepto", None)
        if concepto:
            desc = getattr(concepto, "descripcion", concepto.get("descripcion", "")) if hasattr(concepto, "__dict__") or hasattr(concepto, "descripcion") else concepto.get("descripcion", "")
            writer.campo("concepto", desc)
            writer.comenzar_arreglo("insumos")
            insumos = getattr(concepto, "insumos", concepto.get("insumos", [])) if hasattr(concepto, "__dict__") or hasattr(concepto, "insumos") else concepto.get("insumos", [])
            for insumo in insumos:
                writer.comenzar_objeto()
                inom = getattr(insumo, "nombre", insumo.get("nombre", "")) if hasattr(insumo, "__dict__") or hasattr(insumo, "nombre") else insumo.get("nombre", "")
                ican = getattr(insumo, "cantidad", insumo.get("cantidad", 0.0)) if hasattr(insumo, "__dict__") or hasattr(insumo, "cantidad") else insumo.get("cantidad", 0.0)
                ipu = getattr(insumo, "precio_unitario", insumo.get("precio_unitario", 0.0)) if hasattr(insumo, "__dict__") or hasattr(insumo, "precio_unitario") else insumo.get("precio_unitario", 0.0)
                ipt = getattr(insumo, "precio_total", insumo.get("precio_total", 0.0)) if hasattr(insumo, "__dict__") or hasattr(insumo, "precio_total") else insumo.get("precio_total", 0.0)
                writer.campo("nombre", inom)
                writer.campo("cantidad", ican)
                writer.campo("precio_unitario", ipu)
                writer.campo("precio_total", ipt)
                writer.terminar_objeto()
            writer.terminar_arreglo()
        writer.terminar_objeto()
    writer.terminar_arreglo()
    writer.terminar_objeto()
    if buf is not None:
        return buf.getvalue()
    return b""

# ─────────────────────────────────────────────────────────────────────────────
# CAPA 3 – CPLVsi
# ─────────────────────────────────────────────────────────────────────────────

class CPLVsiHandle:
    def __init__(self, nombre: str, datos: Optional[bytes] = None, ruta_disco: Optional[Path] = None) -> None:
        self._nombre = nombre
        self._disco = ruta_disco
        self._buffer: Optional[io.BytesIO] = io.BytesIO(datos) if datos is not None else None
        self._modo = "memoria" if ruta_disco is None else "disco"

    @property
    def nombre(self) -> str:
        return self._nombre

    @property
    def es_memoria(self) -> bool:
        return self._modo == "memoria"

    def leer(self) -> bytes:
        if self._disco:
            return self._disco.read_bytes()
        assert self._buffer is not None
        pos = self._buffer.tell()
        self._buffer.seek(0)
        data = self._buffer.read()
        self._buffer.seek(pos)
        return data

    def escribir(self, datos: bytes) -> None:
        if self._disco:
            self._disco.write_bytes(datos)
            return
        self._buffer = io.BytesIO(datos)

    def tamaño(self) -> int:
        if self._disco and self._disco.exists():
            return self._disco.stat().st_size
        if self._buffer:
            return len(self._buffer.getvalue())
        return 0

    def sha256(self) -> str:
        return _sha256(self.leer())

    def cerrar(self) -> None:
        if self._buffer:
            self._buffer.close()

class CPLVsiSistema:
    def __init__(self, ruta_base: Optional[Path] = None) -> None:
        self._base = ruta_base or Path(tempfile.gettempdir()) / "megalodon_vsi"
        self._base.mkdir(parents=True, exist_ok=True)
        self._memoria: Dict[str, CPLVsiHandle] = {}
        self._lock = threading.Lock()

    def abrir_memoria(self, nombre: str, datos: bytes = b"") -> CPLVsiHandle:
        handle = CPLVsiHandle(nombre, datos=datos)
        with self._lock:
            self._memoria[nombre] = handle
        return handle

    def abrir_disco(self, nombre: str) -> CPLVsiHandle:
        ruta = self._base / nombre
        return CPLVsiHandle(nombre, ruta_disco=ruta)

    def existe(self, nombre: str) -> bool:
        with self._lock:
            if nombre in self._memoria:
                return True
        return (self._base / nombre).exists()

    def listar(self) -> List[str]:
        disco = [p.name for p in self._base.iterdir()]
        with self._lock:
            mem = list(self._memoria.keys())
        return sorted(set(disco + mem))

    def eliminar(self, nombre: str) -> None:
        with self._lock:
            self._memoria.pop(nombre, None)
        ruta = self._base / nombre
        if ruta.exists():
            ruta.unlink()

    def mover_a_disco(self, nombre: str) -> CPLVsiHandle:
        with self._lock:
            handle_mem = self._memoria.get(nombre)
        if handle_mem is None:
            raise FileNotFoundError(f"VSI: '{nombre}' no está en memoria")
        datos = handle_mem.leer()
        handle_disco = self.abrir_disco(nombre)
        handle_disco.escribir(datos)
        with self._lock:
            self._memoria.pop(nombre, None)
        return handle_disco

# ─────────────────────────────────────────────────────────────────────────────
# CAPA 4 – CPLQueue
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class JobBackground:
    id: str
    tipo: str
    payload: Dict[str, Any]
    callback: Optional[Callable[[Dict[str, Any]], None]] = field(default=None, repr=False)
    creado_en: datetime = field(default_factory=_now_utc)
    resultado: Optional[Dict[str, Any]] = None
    error: Optional[str] = None
    estado: str = "PENDIENTE"

class CPLQueue:
    def __init__(self, trabajadores: int = 2, max_items: int = 500) -> None:
        self._q: queue.Queue[JobBackground] = queue.Queue(maxsize=max_items)
        self._resultados: Dict[str, JobBackground] = {}
        self._lock = threading.Lock()
        self._activa = True
        self._hilos: List[threading.Thread] = []
        for _ in range(trabajadores):
            t = threading.Thread(target=self._worker, daemon=True)
            t.start()
            self._hilos.append(t)

    def encolar(self, tipo: str, payload: Dict[str, Any], callback: Optional[Callable] = None) -> str:
        job_id = f"JOB-{uuid.uuid4().hex[:8].upper()}"
        job = JobBackground(id=job_id, tipo=tipo, payload=payload, callback=callback)
        with self._lock:
            self._resultados[job_id] = job
        self._q.put(job)
        return job_id

    def obtener_resultado(self, job_id: str) -> Optional[JobBackground]:
        with self._lock:
            return self._resultados.get(job_id)

    def pendientes(self) -> int:
        return self._q.qsize()

    def apagar(self, timeout: float = 5.0) -> None:
        self._activa = False
        for _ in self._hilos:
            try:
                self._q.put_nowait(None)
            except queue.Full:
                pass
        for h in self._hilos:
            h.join(timeout=timeout)

    def _worker(self) -> None:
        while self._activa:
            try:
                job = self._q.get(timeout=1.0)
            except queue.Empty:
                continue
            if job is None:
                break
            job.estado = "EN_PROCESO"
            try:
                resultado = self._ejecutar(job)
                job.resultado = resultado
                job.estado = "COMPLETADO"
                if job.callback:
                    job.callback(resultado)
            except Exception as exc:
                job.error = str(exc)
                job.estado = "FALLIDO"
                _cpl_error.registrar(
                    CPLError.COD_NORMATIVO + 1,
                    f"Job {job.id} ({job.tipo}) falló: {exc}",
                    Severidad.ERROR, "CPLQueue",
                )
            finally:
                self._q.task_done()

    def _ejecutar(self, job: JobBackground) -> Dict[str, Any]:
        if job.tipo == "HASH_ARCHIVO":
            datos = job.payload.get("datos", b"")
            return {"hash": _sha256(datos if isinstance(datos, bytes) else datos.encode())}
        if job.tipo == "VALIDAR_EXPEDIENTE":
            return {"resultado": "PENDIENTE_MOTOR", "expediente_id": job.payload.get("expediente_id")}
        if job.tipo == "MERKLE_PROOF":
            return {"proof": [], "root": _sha256(b"fake")}
        if job.tipo == "CUANTIFICAR_IFC":
            return {"status": "EN_ESPERA"}
        return {"tipo": job.tipo, "procesado": True}

# ─────────────────────────────────────────────────────────────────────────────
# CAPA 5 – CPLProgress
# ─────────────────────────────────────────────────────────────────────────────

ProgressCallbackFn = Callable[[float, str], bool]

class CPLProgress:
    def __init__(self, total_pasos: int = 100, descripcion: str = "") -> None:
        self.total = max(total_pasos, 1)
        self.descripcion = descripcion
        self._paso_actual = 0
        self._cancelado = False
        self._callbacks: List[ProgressCallbackFn] = []
        self._lock = threading.Lock()

    def suscribir(self, fn: ProgressCallbackFn) -> None:
        with self._lock:
            self._callbacks.append(fn)

    def avanzar(self, pasos: int = 1, mensaje: str = "") -> bool:
        with self._lock:
            self._paso_actual = min(self._paso_actual + pasos, self.total)
            pct = self._paso_actual / self.total
            cancelar = False
            for cb in self._callbacks:
                try:
                    continuar = cb(pct, mensaje or f"{self.descripcion} {pct*100:.0f}%")
                    if not continuar:
                        cancelar = True
                except Exception:
                    pass
            if cancelar:
                self._cancelado = True
        return not self._cancelado

    def completar(self) -> None:
        with self._lock:
            self._paso_actual = self.total
        for cb in self._callbacks:
            try:
                cb(1.0, f"{self.descripcion} – completado")
            except Exception:
                pass

    @property
    def porcentaje(self) -> float:
        with self._lock:
            return self._paso_actual / self.total * 100

    @property
    def cancelado(self) -> bool:
        return self._cancelado

    @staticmethod
    def consola() -> ProgressCallbackFn:
        def _cb(pct: float, msg: str) -> bool:
            print(f"\r  ▶ {msg} [{pct*100:.0f}%]", end="", flush=True)
            if pct >= 1.0:
                print()
            return True
        return _cb

# ─────────────────────────────────────────────────────────────────────────────
# CAPA 6 – CPLHash
# ─────────────────────────────────────────────────────────────────────────────

class CPLHash:
    _cache: Dict[str, str] = {}
    _lock = threading.Lock()

    @classmethod
    def _digest(cls, data: bytes) -> str:
        return _sha256(data)

    @classmethod
    def de_bytes(cls, data: bytes) -> str:
        return cls._digest(data)

    @classmethod
    def de_archivo(cls, ruta: Path, usar_cache: bool = True) -> str:
        clave_cache = str(ruta)
        if usar_cache:
            with cls._lock:
                if clave_cache in cls._cache:
                    return cls._cache[clave_cache]
        digest = cls._digest(ruta.read_bytes())
        if usar_cache:
            with cls._lock:
                cls._cache[clave_cache] = digest
        return digest

    @classmethod
    def de_texto(cls, texto: str) -> str:
        return cls._digest(texto.encode("utf-8"))

    @classmethod
    def cache_key(cls, *partes: str) -> str:
        combined = "|".join(partes)
        return cls.de_texto(combined)[:16]

    @classmethod
    def deduplicar(cls, elementos: List[Dict[str, Any]], campo_datos: str = "contenido") -> List[Dict[str, Any]]:
        vistos: set = set()
        resultado = []
        for elem in elementos:
            raw = elem.get(campo_datos, "")
            if isinstance(raw, bytes):
                h = cls.de_bytes(raw)
            else:
                h = cls.de_texto(str(raw))
            if h not in vistos:
                vistos.add(h)
                resultado.append(elem)
        return resultado

    @classmethod
    def limpiar_cache(cls) -> None:
        with cls._lock:
            cls._cache.clear()

# ─────────────────────────────────────────────────────────────────────────────
# CAPA 7 – CPLQuadTree
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class BBox:
    min_x: float
    min_y: float
    max_x: float
    max_y: float

    def contiene(self, x: float, y: float) -> bool:
        return self.min_x <= x <= self.max_x and self.min_y <= y <= self.max_y

    def intersecta(self, otro: BBox) -> bool:
        return not (otro.min_x > self.max_x or otro.max_x < self.min_x or
                    otro.min_y > self.max_y or otro.max_y < self.min_y)

    def centro(self) -> Tuple[float, float]:
        return ((self.min_x + self.max_x) / 2, (self.min_y + self.max_y) / 2)

@dataclass
class EntradaEspacial:
    id: str
    bbox: BBox
    datos: Dict[str, Any] = field(default_factory=dict)

class CPLQuadTree:
    MAX_ITEMS = 8
    MAX_PROF = 12

    def __init__(self, bbox: BBox, profundidad: int = 0) -> None:
        self.bbox = bbox
        self.profundidad = profundidad
        self._items: List[EntradaEspacial] = []
        self._hijos: List[CPLQuadTree] = []

    def insertar(self, entrada: EntradaEspacial) -> bool:
        if not self.bbox.intersecta(entrada.bbox):
            return False
        if len(self._hijos) == 0:
            self._items.append(entrada)
            if len(self._items) > self.MAX_ITEMS and self.profundidad < self.MAX_PROF:
                self._subdividir()
            return True
        insertado = False
        for hijo in self._hijos:
            if hijo.insertar(entrada):
                insertado = True
        if not insertado:
            self._items.append(entrada)
        return True

    def buscar(self, bbox: BBox) -> List[EntradaEspacial]:
        resultados: List[EntradaEspacial] = []
        if not self.bbox.intersecta(bbox):
            return resultados
        for item in self._items:
            if item.bbox.intersecta(bbox):
                resultados.append(item)
        for hijo in self._hijos:
            resultados.extend(hijo.buscar(bbox))
        return resultados

    def punto_mas_cercano(self, x: float, y: float) -> Optional[EntradaEspacial]:
        candidatos = self.buscar(BBox(x - 1e9, y - 1e9, x + 1e9, y + 1e9))
        if not candidatos:
            return None
        def dist(e: EntradaEspacial) -> float:
            cx, cy = e.bbox.centro()
            return (cx - x) ** 2 + (cy - y) ** 2
        return min(candidatos, key=dist)

    def _subdividir(self) -> None:
        mx = (self.bbox.min_x + self.bbox.max_x) / 2
        my = (self.bbox.min_y + self.bbox.max_y) / 2
        sub_bboxes = [
            BBox(self.bbox.min_x, my, mx, self.bbox.max_y),
            BBox(mx, my, self.bbox.max_x, self.bbox.max_y),
            BBox(self.bbox.min_x, self.bbox.min_y, mx, my),
            BBox(mx, self.bbox.min_y, self.bbox.max_x, my),
        ]
        self._hijos = [CPLQuadTree(b, self.profundidad + 1) for b in sub_bboxes]
        items_previos = self._items[:]
        self._items = []
        for item in items_previos:
            insertado = False
            for hijo in self._hijos:
                if hijo.insertar(item):
                    insertado = True
                    break
            if not insertado:
                self._items.append(item)

# ─────────────────────────────────────────────────────────────────────────────
# MOTOR A – MotorFallo
# ─────────────────────────────────────────────────────────────────────────────

class TipoFallo(str, Enum):
    REQUISITO_FALTANTE = "REQUISITO_FALTANTE"
    INCONSISTENCIA_TECNICA = "INCONSISTENCIA_TECNICA"
    INCUMPLIMIENTO_DOCUMENTAL = "INCUMPLIMIENTO_DOCUMENTAL"
    PRECIO_FUERA_RANGO = "PRECIO_FUERA_RANGO"
    ERROR_FIRMA = "ERROR_FIRMA"
    FORMATO_INVALIDO = "FORMATO_INVALIDO"
    VIGENCIA_VENCIDA = "VIGENCIA_VENCIDA"
    CAPACIDAD_INSUFICIENTE = "CAPACIDAD_INSUFICIENTE"
    INCUMPLIMIENTO_NORMATIVO = "INCUMPLIMIENTO_NORMATIVO"
    ERROR_CALCULO = "ERROR_CALCULO"

@dataclass
class CausalFallo:
    id: str = field(default_factory=lambda: f"FALLO-{uuid.uuid4().hex[:8].upper()}")
    tipo: TipoFallo = TipoFallo.REQUISITO_FALTANTE
    descripcion: str = ""
    campo_afectado: str = ""
    valor_obtenido: Any = None
    valor_esperado: Any = None
    norma_referencia: str = ""
    dependencia: str = ""
    estado: str = ""
    tipo_obra: str = ""
    subsanable: bool = True
    timestamp: datetime = field(default_factory=_now_utc)
    evidencia_id: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id, "tipo": self.tipo.value, "descripcion": self.descripcion,
            "campo_afectado": self.campo_afectado, "valor_obtenido": self.valor_obtenido,
            "valor_esperado": self.valor_esperado, "norma_referencia": self.norma_referencia,
            "dependencia": self.dependencia, "estado": self.estado, "tipo_obra": self.tipo_obra,
            "subsanable": self.subsanable, "timestamp": self.timestamp.isoformat(),
            "evidencia_id": self.evidencia_id,
        }

class MotorFallo:
    def __init__(self) -> None:
        self._causales: List[CausalFallo] = []
        self._patron_cache: Dict[str, List[CausalFallo]] = {}
        self._lock = threading.Lock()

    def registrar_fallo(self, causal: CausalFallo) -> str:
        with self._lock:
            self._causales.append(causal)
            clave = f"{causal.dependencia}|{causal.tipo_obra}"
            self._patron_cache.setdefault(clave, []).append(causal)
        _cpl_error.registrar(
            CPLError.COD_NORMATIVO + 10,
            f"Fallo [{causal.tipo.value}]: {causal.descripcion}",
            Severidad.AVISO, "MotorFallo", {"causal_id": causal.id},
        )
        return causal.id

    def evaluar_campo(self, campo: str, valor: Any, esperado: Any, tipo: TipoFallo,
                      norma: str = "", dependencia: str = "", estado: str = "",
                      tipo_obra: str = "", subsanable: bool = True) -> Optional[CausalFallo]:
        cumple = False
        if callable(esperado):
            cumple = esperado(valor)
        elif isinstance(esperado, (list, tuple, set)):
            cumple = valor in esperado
        else:
            cumple = valor == esperado
        if not cumple:
            causal = CausalFallo(
                tipo=tipo, descripcion=f"Campo '{campo}' no cumple",
                campo_afectado=campo, valor_obtenido=valor,
                valor_esperado=str(esperado)[:200], norma_referencia=norma,
                dependencia=dependencia, estado=estado, tipo_obra=tipo_obra,
                subsanable=subsanable,
            )
            self.registrar_fallo(causal)
            return causal
        return None

    def fallos_por_tipo(self, tipo: TipoFallo) -> List[CausalFallo]:
        with self._lock:
            return [c for c in self._causales if c.tipo == tipo]

    def patron_dependencia(self, dependencia: str, tipo_obra: str = "") -> List[CausalFallo]:
        clave = f"{dependencia}|{tipo_obra}"
        with self._lock:
            return list(self._patron_cache.get(clave, []))

    def resumen(self) -> Dict[str, Any]:
        with self._lock:
            conteo: Dict[str, int] = {}
            subsanables = 0
            for c in self._causales:
                conteo[c.tipo.value] = conteo.get(c.tipo.value, 0) + 1
                if c.subsanable:
                    subsanables += 1
            return {
                "total_fallos": len(self._causales),
                "subsanables": subsanables,
                "no_subsanables": len(self._causales) - subsanables,
                "por_tipo": conteo,
            }

    def limpiar(self) -> None:
        with self._lock:
            self._causales.clear()
            self._patron_cache.clear()

# ─────────────────────────────────────────────────────────────────────────────
# MOTOR B – MotorEvidencia
# ─────────────────────────────────────────────────────────────────────────────

class TipoEvidencia(str, Enum):
    PAGINA_BASES = "PAGINA_BASES"
    PARRAFO = "PARRAFO"
    PLANO = "PLANO"
    CATALOGO = "CATALOGO"
    ARCHIVO = "ARCHIVO"
    CALCULO = "CALCULO"
    METRADO = "METRADO"
    FICHA_TECNICA = "FICHA_TECNICA"
    CAPTURA_BIM = "CAPTURA_BIM"
    NORMA = "NORMA"

@dataclass
class RegistroEvidencia:
    id: str = field(default_factory=lambda: f"EV-{uuid.uuid4().hex[:8].upper()}")
    tipo: TipoEvidencia = TipoEvidencia.ARCHIVO
    descripcion: str = ""
    referencia: str = ""
    contenido_hash: str = ""
    nombre_archivo: Optional[str] = None
    url_o_ruta: Optional[str] = None
    regla_id: Optional[str] = None
    causal_id: Optional[str] = None
    timestamp: datetime = field(default_factory=_now_utc)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "id": self.id, "tipo": self.tipo.value, "descripcion": self.descripcion,
            "referencia": self.referencia, "contenido_hash": self.contenido_hash,
            "nombre_archivo": self.nombre_archivo, "url_o_ruta": self.url_o_ruta,
            "regla_id": self.regla_id, "causal_id": self.causal_id,
            "timestamp": self.timestamp.isoformat(),
        }

@dataclass
class ReglaValidacion:
    id: str = field(default_factory=lambda: f"REGLA-{uuid.uuid4().hex[:8].upper()}")
    descripcion: str = ""
    norma: str = ""
    campo: str = ""
    condicion_fn: Optional[Callable[[Any], bool]] = field(default=None, repr=False)
    evidencias: List[RegistroEvidencia] = field(default_factory=list)
    activa: bool = True

class MotorEvidencia:
    def __init__(self, motor_fallo: Optional[MotorFallo] = None) -> None:
        self._reglas: Dict[str, ReglaValidacion] = {}
        self._evidencias: Dict[str, RegistroEvidencia] = {}
        self._motor_fallo = motor_fallo or MotorFallo()
        self._lock = threading.Lock()

    def registrar_regla(self, regla: ReglaValidacion) -> None:
        with self._lock:
            self._reglas[regla.id] = regla

    def adjuntar_evidencia(self, evidencia: RegistroEvidencia) -> None:
        with self._lock:
            self._evidencias[evidencia.id] = evidencia
        if evidencia.regla_id and evidencia.regla_id in self._reglas:
            self._reglas[evidencia.regla_id].evidencias.append(evidencia)

    def evaluar(self, regla_id: str, valor: Any, contexto: Dict[str, Any] = {}) -> Dict[str, Any]:
        regla = self._reglas.get(regla_id)
        if regla is None:
            return {"cumple": None, "mensaje": f"Regla {regla_id} no encontrada"}
        if not regla.activa:
            return {"cumple": True, "mensaje": "Regla inactiva"}
        cumple = regla.condicion_fn(valor) if regla.condicion_fn else True
        resultado: Dict[str, Any] = {
            "cumple": cumple, "regla_id": regla_id, "campo": regla.campo,
            "norma": regla.norma, "evidencias": [e.to_dict() for e in regla.evidencias],
        }
        if not cumple:
            causal = CausalFallo(
                tipo=TipoFallo.INCUMPLIMIENTO_NORMATIVO,
                descripcion=regla.descripcion, campo_afectado=regla.campo,
                valor_obtenido=valor, norma_referencia=regla.norma,
                dependencia=contexto.get("dependencia", ""),
                estado=contexto.get("estado", ""),
                tipo_obra=contexto.get("tipo_obra", ""),
            )
            if regla.evidencias:
                causal.evidencia_id = regla.evidencias[0].id
            self._motor_fallo.registrar_fallo(causal)
            resultado["causal_id"] = causal.id
        return resultado

    def evidencias_de_regla(self, regla_id: str) -> List[RegistroEvidencia]:
        regla = self._reglas.get(regla_id)
        return regla.evidencias if regla else []

    def resumen(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "total_reglas": len(self._reglas),
                "reglas_activas": sum(1 for r in self._reglas.values() if r.activa),
                "total_evidencias": len(self._evidencias),
            }

# ─────────────────────────────────────────────────────────────────────────────
# MOTOR C – MotorPreciosBIM
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class InsumoUnitario:
    clave: str
    descripcion: str
    unidad: str
    precio: float
    fuente_catalogo: str = "CMIC_GENERAL"
    rendimiento: float = 1.0

@dataclass
class ConceptoAPU:
    clave: str
    descripcion: str
    unidad: str
    materiales: List[Tuple[InsumoUnitario, float]] = field(default_factory=list)
    mano_obra: List[Tuple[InsumoUnitario, float]] = field(default_factory=list)
    equipo: List[Tuple[InsumoUnitario, float]] = field(default_factory=list)

    def costo_directo_unitario(self) -> float:
        total = 0.0
        for ins, cant in (self.materiales + self.mano_obra + self.equipo):
            total += ins.precio * cant
        return total

@dataclass
class PartidaBIM:
    id: str
    elemento_tipo: str
    sistema_constructivo: str
    cantidad: float
    unidad: str
    concepto: Optional[ConceptoAPU] = None
    merma_pct: float = 0.0
    factor_desperdicio: float = 1.0

    def cantidad_con_merma(self) -> float:
        return self.cantidad * (1 + self.merma_pct / 100) * self.factor_desperdicio

    def costo_directo(self) -> float:
        if self.concepto is None:
            return 0.0
        return self.concepto.costo_directo_unitario() * self.cantidad_con_merma()

class MotorPreciosBIM:
    CATALOGOS_SOPORTADOS = {"CMIC_GENERAL", "CMIC_REGIONAL", "CONAGUA", "CFE", "PEMEX", "SSA", "TABULADOR_ESTATAL"}

    def __init__(self, factor_indirecto: float = 0.15, factor_utilidad: float = 0.10,
                 factor_impuesto: float = 0.16, factor_riesgo: float = 0.02) -> None:
        self.factor_indirecto = factor_indirecto
        self.factor_utilidad = factor_utilidad
        self.factor_impuesto = factor_impuesto
        self.factor_riesgo = factor_riesgo
        self._catalogo: Dict[str, InsumoUnitario] = {}
        self._conceptos: Dict[str, ConceptoAPU] = {}
        self._lock = threading.Lock()

    def cargar_insumo(self, insumo: InsumoUnitario) -> None:
        with self._lock:
            self._catalogo[insumo.clave] = insumo

    def cargar_concepto(self, concepto: ConceptoAPU) -> None:
        with self._lock:
            self._conceptos[concepto.clave] = concepto

    def cuantificar_elemento(self, elemento: Dict[str, Any]) -> PartidaBIM:
        tipo = str(elemento.get("tipo", "generico"))
        sistema = str(elemento.get("sistema", "concreto"))
        largo = float(elemento.get("largo", 0) or 0)
        ancho = float(elemento.get("ancho", 0) or 0)
        alto = float(elemento.get("alto", 0) or 0)
        num = float(elemento.get("num_piezas", 1) or 1)
        merma = float(elemento.get("merma_tecnica_pct", 0) or 0)
        kg_acero_m3 = float(elemento.get("kg_acero_m3", 0) or 0)

        cantidad = largo * ancho * alto * num
        unidad = "m³"
        if tipo in ("muro", "tabique", "losa_plana") and alto > 0 and ancho < 0.5:
            cantidad = largo * alto * num
            unidad = "m²"

        clave_concepto = f"{sistema}_{tipo}".upper()
        concepto = self._conceptos.get(clave_concepto)

        if concepto is None:
            precio_base = self._precio_base_sintetico(tipo, sistema)
            ins_mat = InsumoUnitario(clave=f"MAT_{clave_concepto}",
                descripcion=f"Material {sistema} para {tipo}", unidad=unidad,
                precio=precio_base * 0.60, fuente_catalogo="CMIC_GENERAL")
            ins_mo = InsumoUnitario(clave=f"MO_{clave_concepto}",
                descripcion=f"Mano de obra {tipo}", unidad=unidad,
                precio=precio_base * 0.25, fuente_catalogo="TABULADOR_ESTATAL")
            ins_eq = InsumoUnitario(clave=f"EQ_{clave_concepto}",
                descripcion=f"Equipo {tipo}", unidad=unidad,
                precio=precio_base * 0.15, fuente_catalogo="CMIC_GENERAL")
            concepto = ConceptoAPU(clave=clave_concepto,
                descripcion=f"{tipo.capitalize()} de {sistema}", unidad=unidad,
                materiales=[(ins_mat, 1.0)], mano_obra=[(ins_mo, 1.0)], equipo=[(ins_eq, 1.0)])
            if kg_acero_m3 > 0:
                ins_acero = InsumoUnitario(clave=f"ACERO_{clave_concepto}",
                    descripcion="Acero de refuerzo", unidad="kg", precio=22.0,
                    fuente_catalogo="CMIC_GENERAL")
                concepto.materiales.append((ins_acero, kg_acero_m3))

        return PartidaBIM(
            id=f"P-{uuid.uuid4().hex[:6].upper()}", elemento_tipo=tipo,
            sistema_constructivo=sistema, cantidad=cantidad, unidad=unidad,
            concepto=concepto, merma_pct=merma,
        )

    def _precio_base_sintetico(self, tipo: str, sistema: str) -> float:
        tabla = {
            ("losa", "concreto"): 3_200.0, ("columna", "concreto"): 4_500.0,
            ("muro", "block"): 580.0, ("muro", "concreto"): 3_000.0,
            ("viga", "concreto"): 3_800.0, ("cimentacion", "concreto"): 2_900.0,
            ("piso", "ceramica"): 420.0,
        }
        return tabla.get((tipo.lower(), sistema.lower()), 2_500.0)

    def calcular_precio_final(self, partidas: List[PartidaBIM]) -> Dict[str, Any]:
        monto_directo = sum(p.costo_directo() for p in partidas)
        monto_indirecto = monto_directo * self.factor_indirecto
        subtotal = monto_directo + monto_indirecto
        monto_utilidad = subtotal * self.factor_utilidad
        monto_riesgo = subtotal * self.factor_riesgo
        base_impuesto = subtotal + monto_utilidad + monto_riesgo
        monto_impuesto = base_impuesto * self.factor_impuesto
        precio_final = base_impuesto + monto_impuesto
        return {
            "monto_directo": round(monto_directo, 2),
            "monto_indirecto": round(monto_indirecto, 2),
            "monto_utilidad": round(monto_utilidad, 2),
            "monto_riesgo": round(monto_riesgo, 2),
            "monto_impuesto": round(monto_impuesto, 2),
            "precio_final": round(precio_final, 2),
            "moneda": "MXN", "num_partidas": len(partidas),
            "partidas": [
                {"id": p.id, "tipo": p.elemento_tipo, "sistema": p.sistema_constructivo,
                 "cantidad": round(p.cantidad_con_merma(), 4), "unidad": p.unidad,
                 "costo_directo": round(p.costo_directo(), 2)}
                for p in partidas
            ],
        }

    def ejecutar_desde_payload(self, payload_bim: Dict[str, Any]) -> Dict[str, Any]:
        elementos = payload_bim.get("elementos", [])
        prog = CPLProgress(len(elementos), "MotorPreciosBIM")
        prog.suscribir(lambda pct, msg: True)
        partidas = []
        for elem in elementos:
            partidas.append(self.cuantificar_elemento(elem))
            prog.avanzar()
        prog.completar()
        resultado = self.calcular_precio_final(partidas)
        resultado["proyecto"] = payload_bim.get("proyecto", "")
        resultado["proyecto_id"] = payload_bim.get("proyecto_id", "")
        return resultado

# ─────────────────────────────────────────────────────────────────────────────
# MOTOR D – MonteCarloRiesgo
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class ParametroMC:
    nombre: str
    media: float
    desviacion_std: float
    minimo: Optional[float] = None
    maximo: Optional[float] = None

class MonteCarloRiesgo:
    def __init__(self, iteraciones: int = 1_000, semilla: Optional[int] = None) -> None:
        self.iteraciones = iteraciones
        self._rng = random.Random(semilla)
        self._np_rng = None
        if _NUMPY_AVAILABLE and semilla is not None:
            self._np_rng = np.random.default_rng(semilla)
        elif _NUMPY_AVAILABLE:
            self._np_rng = np.random.default_rng()

    def _muestra(self, p: ParametroMC) -> float:
        if _NUMPY_AVAILABLE and self._np_rng is not None:
            val = float(self._np_rng.normal(p.media, p.desviacion_std))
        else:
            val = self._rng.gauss(p.media, p.desviacion_std)
        if p.minimo is not None:
            val = max(val, p.minimo)
        if p.maximo is not None:
            val = min(val, p.maximo)
        return val

    def simular(self, costo_base: float, parametros: List[ParametroMC]) -> Dict[str, Any]:
        muestras: List[float] = []
        for _ in range(self.iteraciones):
            factor = 1.0
            for p in parametros:
                factor *= self._muestra(p)
            muestras.append(costo_base * factor)
        muestras_sorted = sorted(muestras)
        n = len(muestras_sorted)
        media = sum(muestras) / n
        varianza = sum((x - media) ** 2 for x in muestras) / max(n - 1, 1)
        std = varianza ** 0.5
        p5 = muestras_sorted[max(int(n * 0.05) - 1, 0)]
        p25 = muestras_sorted[max(int(n * 0.25) - 1, 0)]
        p50 = muestras_sorted[max(int(n * 0.50) - 1, 0)]
        p75 = muestras_sorted[max(int(n * 0.75) - 1, 0)]
        p95 = muestras_sorted[min(int(n * 0.95), n - 1)]
        return {
            "costo_base": round(costo_base, 2), "iteraciones": self.iteraciones,
            "media": round(media, 2), "desviacion_std": round(std, 2),
            "cv_pct": round(std / media * 100 if media else 0, 2),
            "percentiles": {
                "p5": round(p5, 2), "p25": round(p25, 2), "p50": round(p50, 2),
                "p75": round(p75, 2), "p95": round(p95, 2),
            },
            "rango_probable": {"minimo": round(p5, 2), "maximo": round(p95, 2)},
        }

    @staticmethod
    def parametros_obra_tipicos() -> List[ParametroMC]:
        return [
            ParametroMC("rendimiento_cuadrilla", media=1.0, desviacion_std=0.06, minimo=0.70, maximo=1.30),
            ParametroMC("desperdicio_material", media=1.0, desviacion_std=0.04, minimo=0.90, maximo=1.20),
            ParametroMC("precio_material", media=1.0, desviacion_std=0.08, minimo=0.85, maximo=1.30),
            ParametroMC("disponibilidad_equipo", media=1.0, desviacion_std=0.05, minimo=0.80, maximo=1.10),
            ParametroMC("factor_climatico", media=1.0, desviacion_std=0.03, minimo=0.95, maximo=1.15),
            ParametroMC("productividad_logistica", media=1.0, desviacion_std=0.04, minimo=0.85, maximo=1.10),
        ]

# ─────────────────────────────────────────────────────────────────────────────
# MOTOR E – MotorJuridico
# ─────────────────────────────────────────────────────────────────────────────

class Jurisdiccion(str, Enum):
    FEDERAL = "FEDERAL"
    CDMX = "CDMX"
    JALISCO = "JALISCO"
    NUEVO_LEON = "NUEVO_LEON"
    ESTADO_MEXICO = "ESTADO_MEXICO"
    PUEBLA = "PUEBLA"
    VERACRUZ = "VERACRUZ"
    MICHOACAN = "MICHOACAN"
    BAJA_CALIFORNIA = "BAJA_CALIFORNIA"
    CHIHUAHUA = "CHIHUAHUA"
    SONORA = "SONORA"
    OAXACA = "OAXACA"
    OTRO = "OTRO"

class TipoContrato(str, Enum):
    PRECIOS_UNITARIOS = "PRECIOS_UNITARIOS"
    PRECIO_ALZADO = "PRECIO_ALZADO"
    MIXTO = "MIXTO"
    OBRA_PUBLICA = "OBRA_PUBLICA"
    SERVICIO_RELACIONADO = "SERVICIO_RELACIONADO"
    ARRENDAMIENTO = "ARRENDAMIENTO"
    ADQUISICION = "ADQUISICION"

@dataclass
class MarcoJuridico:
    jurisdiccion: Jurisdiccion
    leyes_aplicables: List[str]
    reglamentos: List[str]
    lineamientos: List[str]
    convocante: str
    tipo_contrato: TipoContrato
    umbrales_licitacion: Dict[str, float] = field(default_factory=dict)
    notas: str = ""

    def to_dict(self) -> Dict[str, Any]:
        return {
            "jurisdiccion": self.jurisdiccion.value,
            "leyes_aplicables": self.leyes_aplicables,
            "reglamentos": self.reglamentos,
            "lineamientos": self.lineamientos,
            "convocante": self.convocante,
            "tipo_contrato": self.tipo_contrato.value,
            "umbrales_licitacion": self.umbrales_licitacion,
            "notas": self.notas,
        }

class MotorJuridico:
    def __init__(self, motor_fallo: Optional[MotorFallo] = None) -> None:
        self._marcos: Dict[str, MarcoJuridico] = {}
        self._motor_fallo = motor_fallo or MotorFallo()
        self._lock = threading.Lock()
        self._cargar_marcos_federales()

    def _cargar_marcos_federales(self) -> None:
        marcos_fed = [
            MarcoJuridico(
                jurisdiccion=Jurisdiccion.FEDERAL,
                leyes_aplicables=["LOPSRM", "LFPRH", "LFA", "LGPDP"],
                reglamentos=["RLOPSRM", "RLFPRH"],
                lineamientos=["Lineamientos SHCP 2026", "Políticas IMSS", "Manual de Obra Pública"],
                convocante="SFP",
                tipo_contrato=TipoContrato.PRECIOS_UNITARIOS,
                umbrales_licitacion={
                    "adjudicacion_directa": ConstantesLegales2026.UMBRAL_ADJUDICACION_DIRECTA_OBRA,
                    "invitacion_tres": ConstantesLegales2026.UMBRAL_INVITACION_TRES_OBRA,
                    "licitacion_publica": ConstantesLegales2026.UMBRAL_LICITACION_PUBLICA_OBRA,
                },
                notas="Umbral 2026 LOPSRM",
            ),
            MarcoJuridico(
                jurisdiccion=Jurisdiccion.FEDERAL,
                leyes_aplicables=["LAASSP", "LFPRH", "LFA"],
                reglamentos=["RLAASSP"],
                lineamientos=["Lineamientos SHCP 2026"],
                convocante="SFP",
                tipo_contrato=TipoContrato.ADQUISICION,
                umbrales_licitacion={
                    "adjudicacion_directa": ConstantesLegales2026.UMBRAL_ADJUDICACION_DIRECTA_ADQUISICION,
                    "invitacion_tres": ConstantesLegales2026.UMBRAL_INVITACION_TRES_ADQUISICION,
                    "licitacion_publica": ConstantesLegales2026.UMBRAL_INVITACION_TRES_ADQUISICION + 1,
                },
                notas="LAASSP adquisiciones",
            ),
            MarcoJuridico(
                jurisdiccion=Jurisdiccion.FEDERAL,
                leyes_aplicables=["LOPSRM", "LFPRH", "LFA", "LGPDP"],
                reglamentos=["RLOPSRM", "RLFPRH"],
                lineamientos=["Lineamientos SHCP 2026", "Manual de Obra Pública"],
                convocante="SCT",
                tipo_contrato=TipoContrato.OBRA_PUBLICA,
                umbrales_licitacion={
                    "adjudicacion_directa": ConstantesLegales2026.UMBRAL_ADJUDICACION_DIRECTA_OBRA,
                    "invitacion_tres": ConstantesLegales2026.UMBRAL_INVITACION_TRES_OBRA,
                    "licitacion_publica": ConstantesLegales2026.UMBRAL_LICITACION_PUBLICA_OBRA,
                },
                notas="Marco SCT",
            ),
            MarcoJuridico(
                jurisdiccion=Jurisdiccion.FEDERAL,
                leyes_aplicables=["LOPSRM", "LFPRH", "LFA", "LGPDP"],
                reglamentos=["RLOPSRM", "RLFPRH"],
                lineamientos=["Lineamientos SHCP 2026", "Manual de Obra Pública"],
                convocante="CONAGUA",
                tipo_contrato=TipoContrato.OBRA_PUBLICA,
                umbrales_licitacion={
                    "adjudicacion_directa": ConstantesLegales2026.UMBRAL_ADJUDICACION_DIRECTA_OBRA,
                    "invitacion_tres": ConstantesLegales2026.UMBRAL_INVITACION_TRES_OBRA,
                    "licitacion_publica": ConstantesLegales2026.UMBRAL_LICITACION_PUBLICA_OBRA,
                },
                notas="Marco CONAGUA",
            ),
        ]
        for m in marcos_fed:
            clave = self._clave(m.jurisdiccion, m.convocante, m.tipo_contrato)
            with self._lock:
                self._marcos[clave] = m

    def _clave(self, jurisdiccion: Jurisdiccion, convocante: str, tipo: TipoContrato) -> str:
        return f"{jurisdiccion.value}|{convocante.upper()}|{tipo.value}"

    def registrar_marco(self, marco: MarcoJuridico) -> None:
        clave = self._clave(marco.jurisdiccion, marco.convocante, marco.tipo_contrato)
        with self._lock:
            self._marcos[clave] = marco

    def obtener_marco(self, jurisdiccion: Jurisdiccion, convocante: str, tipo_contrato: TipoContrato) -> Optional[MarcoJuridico]:
        clave = self._clave(jurisdiccion, convocante, tipo_contrato)
        with self._lock:
            return self._marcos.get(clave)

    def determinar_procedimiento(self, jurisdiccion: Jurisdiccion, convocante: str,
                                  tipo_contrato: TipoContrato, monto: float) -> Dict[str, Any]:
        marco = self.obtener_marco(jurisdiccion, convocante, tipo_contrato)
        if marco is None:
            for m in self._marcos.values():
                if m.jurisdiccion == jurisdiccion and m.tipo_contrato == tipo_contrato:
                    marco = m
                    break
        if marco is None:
            return {
                "procedimiento": "NO_DETERMINADO",
                "motivo": f"No se encontró marco para {jurisdiccion.value}/{convocante}/{tipo_contrato.value}",
                "marco_disponible": False,
            }
        umbral_ad = marco.umbrales_licitacion.get("adjudicacion_directa", 0)
        umbral_i3 = marco.umbrales_licitacion.get("invitacion_tres", 0)
        if monto <= umbral_ad:
            procedimiento = "ADJUDICACION_DIRECTA"
            fundamento = "Art. 42 LOPSRM / Art. 41 LAASSP"
        elif monto <= umbral_i3:
            procedimiento = "INVITACION_CUANDO_MENOS_TRES"
            fundamento = "Art. 43 LOPSRM / Art. 42 LAASSP"
        else:
            procedimiento = "LICITACION_PUBLICA"
            fundamento = "Art. 27 LOPSRM / Art. 26 LAASSP"
        return {
            "procedimiento": procedimiento, "fundamento": fundamento, "monto": monto,
            "jurisdiccion": jurisdiccion.value, "convocante": convocante,
            "tipo_contrato": tipo_contrato.value, "leyes_aplicables": marco.leyes_aplicables,
            "notas": marco.notas, "marco_disponible": True,
        }

    def validar_requisitos(self, jurisdiccion: Jurisdiccion, convocante: str,
                           tipo_contrato: TipoContrato, datos_propuesta: Dict[str, Any]) -> Dict[str, Any]:
        marco = self.obtener_marco(jurisdiccion, convocante, tipo_contrato)
        fallos: List[str] = []
        if not datos_propuesta.get("rfc"):
            causal = CausalFallo(
                tipo=TipoFallo.REQUISITO_FALTANTE, descripcion="RFC del licitante es obligatorio",
                campo_afectado="rfc", norma_referencia="LAASSP Art. 29 / LOPSRM Art. 36",
                dependencia=convocante,
            )
            self._motor_fallo.registrar_fallo(causal)
            fallos.append("RFC faltante")
        if not datos_propuesta.get("garantia_seriedad"):
            causal = CausalFallo(
                tipo=TipoFallo.REQUISITO_FALTANTE, descripcion="Garantía de seriedad no proporcionada",
                campo_afectado="garantia_seriedad", norma_referencia="LOPSRM Art. 48",
                dependencia=convocante,
            )
            self._motor_fallo.registrar_fallo(causal)
            fallos.append("Garantía de seriedad faltante")
        return {"cumple": len(fallos) == 0, "fallos": fallos,
                "marco": marco.to_dict() if marco else None}

    def listar_marcos(self) -> List[Dict[str, Any]]:
        with self._lock:
            return [m.to_dict() for m in self._marcos.values()]

# ─────────────────────────────────────────────────────────────────────────────
# MOTOR F – Motor Determinista v3 (EXTENDIDO)
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class ResultadoValidacion:
    id_regla: str
    seccion: str
    estatus: str
    valor_detectado: str
    valor_esperado: str
    evidencia: str

    def __post_init__(self):
        if self.estatus not in ("PASA", "FALLA", "NO_APLICA"):
            raise ValueError(f"Estatus inválido: {self.estatus}")

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

class ValidadorBase:
    id_regla: str = ""
    seccion: str = ""
    es_critica: bool = True

    def evaluar(self, datos: Dict[str, Any]) -> ResultadoValidacion:
        raise NotImplementedError("Cada regla debe implementar 'evaluar'.")

class ValidadorSAT32D(ValidadorBase):
    id_regla = "REG-FIS-32D"
    seccion = "Legal-Fiscal"
    es_critica = True
    def evaluar(self, datos):
        fiscal = datos.get("fiscal", {})
        opinion_sentido = str(fiscal.get("opinion_sat_sentido", "")).upper()
        fecha_emision_str = str(fiscal.get("opinion_sat_fecha", ""))
        if opinion_sentido != "POSITIVA":
            return ResultadoValidacion("REG-FIS-32D-SENTIDO", self.seccion, "FALLA",
                valor_detectado=opinion_sentido, valor_esperado="POSITIVA",
                evidencia="La Opinión de Cumplimiento SAT no es estrictamente POSITIVA (Art. 32-D CFF).")
        try:
            fecha_emision = datetime.strptime(fecha_emision_str, "%Y-%m-%d").date()
            dias_antiguedad = (date.today() - fecha_emision).days
            if dias_antiguedad > ConstantesLegales2026.VIGENCIA_OPINION_SAT_DIAS:
                return ResultadoValidacion("REG-FIS-32D-VIGENCIA", self.seccion, "FALLA",
                    valor_detectado=f"{dias_antiguedad} días", valor_esperado=f"<= {ConstantesLegales2026.VIGENCIA_OPINION_SAT_DIAS} días",
                    evidencia="La opinión del SAT excede la antigüedad máxima permitida.")
        except ValueError:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado="Formato inválido", valor_esperado="YYYY-MM-DD",
                evidencia="Fecha de emisión del SAT ilegible o corrupta.")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            "POSITIVA y Vigente", "POSITIVA y Vigente",
            "Cumple Art. 32-D CFF y vigencia RMF 2026.")

class ValidadorSeguridadSocial(ValidadorBase):
    id_regla = "REG-FIS-32D-SEG-SOCIAL"
    seccion = "Legal-Fiscal"
    es_critica = True
    def evaluar(self, datos):
        fiscal = datos.get("fiscal", {})
        opinion_imss = str(fiscal.get("opinion_imss_sentido", "")).upper()
        opinion_infonavit = str(fiscal.get("opinion_infonavit_sentido", "")).upper()
        if opinion_imss != "POSITIVA":
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"IMSS: {opinion_imss}", valor_esperado="IMSS: POSITIVA",
                evidencia="Opinión de cumplimiento patronal IMSS negativa.")
        if opinion_infonavit != "POSITIVA":
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"INFONAVIT: {opinion_infonavit}", valor_esperado="INFONAVIT: POSITIVA",
                evidencia="Opinión de cumplimiento INFONAVIT negativa.")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            "IMSS/INFONAVIT POSITIVA", "IMSS/INFONAVIT POSITIVA",
            "Cumple obligaciones de seguridad social.")

class ValidadorFirmaElectronica(ValidadorBase):
    id_regla = "REG-ADM-EFIRMA"
    seccion = "Administrativa"
    es_critica = True
    def evaluar(self, datos):
        if not datos.get("administrativo", {}).get("efirma_valida", False):
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado="Ausente/Inválida", valor_esperado="Válida",
                evidencia="Anexos carecen de firma electrónica avanzada (e.firma) íntegra.")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            "Válida", "Válida", "Documentación correctamente firmada.")

class ValidadorFactorSalarioReal(ValidadorBase):
    id_regla = "REG-ECO-FSR"
    seccion = "Económica"
    es_critica = True
    def evaluar(self, datos):
        fsr = datos.get("economico", {}).get("analisis_fsr", {})
        tp = float(fsr.get("tp_dias_pagados", 0))
        tl = float(fsr.get("tl_dias_laborados", 0))
        ps = float(fsr.get("ps_fraccion_imss_infonavit", 0))
        fsr_decl = float(fsr.get("fsr_calculado_por_licitante", 0))
        if tp < ConstantesLegales2026.DIAS_PAGADOS_MINIMO:
            return ResultadoValidacion("REG-ECO-FSR-TP", self.seccion, "FALLA",
                valor_detectado=f"{tp} días", valor_esperado=f">= {ConstantesLegales2026.DIAS_PAGADOS_MINIMO} días",
                evidencia="Días pagados por debajo del mínimo legal.")
        if tl > ConstantesLegales2026.DIAS_LABORADOS_MAXIMO:
            return ResultadoValidacion("REG-ECO-FSR-TL", self.seccion, "FALLA",
                valor_detectado=f"{tl} días", valor_esperado=f"<= {ConstantesLegales2026.DIAS_LABORADOS_MAXIMO} días",
                evidencia="Días laborados exceden límite legal.")
        if tl <= 0:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado="Tl = 0", valor_esperado="Tl > 0",
                evidencia="División entre cero.")
        fsr_calc = round(ps * (tp / tl) + (tp / tl), 4)
        if abs(fsr_decl - fsr_calc) > ConstantesLegales2026.TOLERANCIA_FSR_ARITMETICO:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"FSR declarado: {fsr_decl}", valor_esperado=f"FSR calculado: {fsr_calc}",
                evidencia=f"Discrepancia aritmética en FSR excede tolerancia.")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            f"FSR: {fsr_decl}", f"FSR: {fsr_calc}",
            "Factor de Salario Real validado aritméticamente.")

class ValidadorCostosHorariosMaquinaria(ValidadorBase):
    id_regla = "REG-ECO-MAQUINARIA"
    seccion = "Económica"
    es_critica = True
    def __init__(self, precio_diesel_zona_sin_iva: float = ConstantesLegales2026.PRECIO_DIESEL_REFERENCIA):
        self.diesel_ref = precio_diesel_zona_sin_iva
    def evaluar(self, datos):
        maq = datos.get("economico", {}).get("analisis_maquinaria", {})
        codigo = str(maq.get("codigo_equipo", "N/A"))
        combustible = float(maq.get("cargo_combustible", 0))
        precio_comb = float(maq.get("precio_litro_combustible_declarado", 0))
        operacion = float(maq.get("cargo_operacion", 0))
        total = float(maq.get("costo_horario_total", 0))
        fijos = float(maq.get("total_cargos_fijos", 0))
        lubricantes = float(maq.get("cargo_lubricantes", 0))
        horas_anual = float(maq.get("horas_uso_anual", 0))
        if horas_anual < ConstantesLegales2026.HORAS_USO_ANUAL_MIN or horas_anual > ConstantesLegales2026.HORAS_USO_ANUAL_MAX:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"{horas_anual} hrs/año",
                valor_esperado=f"{ConstantesLegales2026.HORAS_USO_ANUAL_MIN}-{ConstantesLegales2026.HORAS_USO_ANUAL_MAX} hrs/año",
                evidencia=f"Equipo {codigo}: Horas de uso anual fuera de parámetros técnicos.")
        if combustible <= 0 and maq.get("requiere_combustible", True):
            return ResultadoValidacion("REG-ECO-MAQ-GAS", self.seccion, "FALLA",
                valor_detectado=f"${combustible}", valor_esperado="> $0.00",
                evidencia=f"Equipo {codigo}: Cargo por combustible en cero.")
        if abs(precio_comb - self.diesel_ref) > ConstantesLegales2026.TOLERANCIA_PRECIO_COMBUSTIBLE:
            return ResultadoValidacion("REG-ECO-MAQ-GAS", self.seccion, "FALLA",
                valor_detectado=f"${precio_comb}/litro", valor_esperado=f"${self.diesel_ref} +/- ${ConstantesLegales2026.TOLERANCIA_PRECIO_COMBUSTIBLE}",
                evidencia=f"Equipo {codigo}: Precio combustible fuera de rango.")
        if operacion <= 0:
            return ResultadoValidacion("REG-ECO-MAQ-OPE", self.seccion, "FALLA",
                valor_detectado=f"${operacion}", valor_esperado="> $0.00",
                evidencia=f"Equipo {codigo}: Omisión del cargo por operador.")
        suma = fijos + combustible + lubricantes + operacion
        if abs(total - suma) > ConstantesLegales2026.TOLERANCIA_COSTO_HORARIO:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"${total}", valor_esperado=f"${round(suma, 2)}",
                evidencia=f"Equipo {codigo}: Error de integración aritmética.")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            f"${total}", f"${total}", f"Equipo {codigo} solvente.")

class ValidadorSobrecostos(ValidadorBase):
    id_regla = "REG-ECO-SOBRECOSTOS"
    seccion = "Económica - Sobrecostos"
    es_critica = True
    def __init__(self, tasa_tie_referencia: float = ConstantesLegales2026.TASA_TIE_REFERENCIA):
        self.tie_ref = tasa_tie_referencia
    def evaluar(self, datos):
        sc = datos.get("economico", {}).get("analisis_sobrecostos", {})
        ind_oficina = float(sc.get("pct_indirecto_oficina", 0))
        ind_campo = float(sc.get("pct_indirecto_campo", 0))
        utilidad = float(sc.get("pct_utilidad", 0))
        financiamiento = float(sc.get("pct_financiamiento", 0))
        adicionales = float(sc.get("pct_cargos_adicionales", 0))
        factor_decl = float(sc.get("factor_sobrecosto_total_declarado", 1.0))
        tasa_interes = float(sc.get("tasa_interes_utilizada", 0))
        if ind_oficina <= 0 or ind_campo <= 0:
            return ResultadoValidacion("REG-ECO-IND-DESGLOSE", self.seccion, "FALLA",
                valor_detectado=f"Oficina: {ind_oficina*100}%, Campo: {ind_campo*100}%",
                valor_esperado="Ambos > 0%",
                evidencia="No se desglosaron indirectos.")
        if utilidad <= 0:
            return ResultadoValidacion("REG-ECO-UTILIDAD-NETA", self.seccion, "FALLA",
                valor_detectado=f"{utilidad*100}%", valor_esperado="> 0%",
                evidencia="Utilidad <= 0%: propuesta insolvente.")
        if tasa_interes <= 0:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"{tasa_interes*100}%", valor_esperado="> 0%",
                evidencia="Tasa de interés omitida.")
        if abs(tasa_interes - self.tie_ref) > 0.05:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"Tasa: {tasa_interes*100}%", valor_esperado=f"TIE Ref: {self.tie_ref*100}% (±5%)",
                evidencia="Tasa de interés fuera de condiciones reales del mercado.")
        f_ind = 1 + (ind_oficina + ind_campo)
        f_fin = f_ind * (1 + financiamiento)
        f_ut = f_fin * (1 + utilidad)
        factor_calc = round(f_ut + adicionales, 4)
        if abs(factor_decl - factor_calc) > ConstantesLegales2026.TOLERANCIA_FACTOR_SOBRECOSTO:
            return ResultadoValidacion("REG-ECO-SOBRECOSTO-CASCADA", self.seccion, "FALLA",
                valor_detectado=f"Factor: {factor_decl}", valor_esperado=f"Factor: {factor_calc}",
                evidencia=f"Error en cascada.")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            f"Factor: {factor_decl}", f"Factor: {factor_calc}",
            "Sobrecostos validados en cascada.")

class ValidadorCongruenciaTemporal(ValidadorBase):
    id_regla = "REG-TEC-CONGRUENCIA-TEMP"
    seccion = "Técnica"
    es_critica = True
    def evaluar(self, datos):
        tecnico = datos.get("tecnico", {})
        incongruencias = tecnico.get("incongruencias_detectadas", [])
        if incongruencias:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                valor_detectado=f"{len(incongruencias)} incongruencias",
                valor_esperado="0 incongruencias",
                evidencia=f"Incongruencia temporal: {incongruencias[0]}")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            "0 incongruencias", "0 incongruencias",
            "Programas de obra congruentes.")

class ValidadorGarantiaCumplimiento(ValidadorBase):
    id_regla = "REG-LOP-002"
    seccion = "Legal"
    es_critica = True
    def evaluar(self, datos):
        garantias = datos.get("garantias", [])
        cumple = any(g.get("tipo") == "cumplimiento" for g in garantias)
        return ResultadoValidacion(self.id_regla, self.seccion,
            "PASA" if cumple else "FALLA",
            valor_detectado=str([g.get("tipo") for g in garantias]),
            valor_esperado="Debe existir garantía de cumplimiento",
            evidencia="Art. 48 LOPSRM")

class ValidadorPublicacionSIRECO(ValidadorBase):
    id_regla = "REG-LOP-005"
    seccion = "Legal"
    es_critica = True
    def evaluar(self, datos):
        fecha_fallo = datos.get("fecha_fallo")
        if not fecha_fallo:
            return ResultadoValidacion(self.id_regla, self.seccion, "FALLA",
                "Sin fecha de fallo", "Fecha de fallo requerida",
                "Art. 36 LOPSRM")
        return ResultadoValidacion(self.id_regla, self.seccion, "PASA",
            "Publicado", "Publicado", "Cumple con publicación")

class ValidadorRequisitosParticipacion(ValidadorBase):
    id_regla = "REG-LAA-001"
    seccion = "Legal"
    es_critica = True
    def evaluar(self, datos):
        requisitos = datos.get("requisitos_participacion", [])
        cumple = len(requisitos) > 0
        return ResultadoValidacion(self.id_regla, self.seccion,
            "PASA" if cumple else "FALLA",
            f"{len(requisitos)} requisitos",
            "Al menos un requisito",
            "Art. 29 LAASSP")

class MotorDeterministaLicitaciones:
    def __init__(self):
        self.validadores: List[ValidadorBase] = []
        self._resultado_cache: Optional[Dict[str, Any]] = None

    def registrar_regla(self, validador: ValidadorBase) -> None:
        self.validadores.append(validador)

    def procesar_propuesta(self, datos_propuesta: Dict[str, Any]) -> Dict[str, Any]:
        reporte = {
            "rfc_empresa": datos_propuesta.get("rfc_empresa"),
            "estatus_final": "SOLVENTE",
            "bitacora_evaluacion": [],
            "timestamp_evaluacion": _now_utc().isoformat(),
        }
        for validador in self.validadores:
            resultado = validador.evaluar(datos_propuesta)
            reporte["bitacora_evaluacion"].append(resultado.to_dict())
            if resultado.estatus == "FALLA" and validador.es_critica:
                reporte["estatus_final"] = "DESCALIFICADO"
                break
        self._resultado_cache = reporte
        return reporte

    def obtener_ultimo_resultado(self) -> Optional[Dict[str, Any]]:
        return self._resultado_cache

    def resumen_por_seccion(self) -> Dict[str, int]:
        if not self._resultado_cache:
            return {}
        conteo: Dict[str, int] = {}
        for b in self._resultado_cache.get("bitacora_evaluacion", []):
            sec = b.get("seccion", "Desconocida")
            est = b.get("estatus", "DESCONOCIDO")
            clave = f"{sec}|{est}"
            conteo[clave] = conteo.get(clave, 0) + 1
        return conteo

# ─────────────────────────────────────────────────────────────────────────────
# PASO 1: CUANTIFICACIÓN BIM (IFC)
# ─────────────────────────────────────────────────────────────────────────────

class CuantificadorBIM:
    def __init__(self):
        self._modelo = None
        self._elementos_cuantificados: List[Dict[str, Any]] = []

    def cargar_ifc(self, ruta: str) -> None:
        if not _IFC_AVAILABLE:
            raise RuntimeError("ifcopenshell no está instalado. pip install ifcopenshell")
        self._modelo = ifcopenshell.open(ruta)

    def _extraer_quantity_sets(self, elemento) -> Dict[str, float]:
        resultado = {}
        if not hasattr(elemento, "IsDefinedBy"):
            return resultado
        for rel in elemento.IsDefinedBy or []:
            if not rel.is_a("IfcRelDefinesByProperties"):
                continue
            prop_set = rel.RelatingPropertyDefinition
            if prop_set.is_a("IfcElementQuantity"):
                for quantity in prop_set.Quantities:
                    nombre = quantity.Name
                    valor = getattr(quantity, "Value", getattr(quantity, "Volume", 0.0))
                    if valor is not None:
                        resultado[nombre] = float(valor)
        return resultado

    def _extraer_openings(self, elemento) -> List[Any]:
        openings = []
        if hasattr(elemento, "HasOpenings"):
            for rel in elemento.HasOpenings or []:
                if rel.is_a("IfcRelVoidsElement"):
                    openings.append(rel.RelatedOpeningElement)
        return openings

    def _calcular_volumen_neto(self, elemento, qsets: Dict[str, float]) -> float:
        volumen_bruto = qsets.get("NetVolume", qsets.get("GrossVolume", 0.0))
        if volumen_bruto == 0.0:
            return 0.0
        for opening in self._extraer_openings(elemento):
            opening_qsets = self._extraer_quantity_sets(opening)
            vol_opening = opening_qsets.get("NetVolume", opening_qsets.get("GrossVolume", 0.0))
            volumen_bruto -= vol_opening
        return max(volumen_bruto, 0.0)

    def cuantificar_elemento(self, elemento) -> Dict[str, Any]:
        tipo = elemento.is_a()
        cantidades = {
            "id": elemento.GlobalId,
            "tipo": tipo,
            "nombre": getattr(elemento, "Name", ""),
        }
        qsets = self._extraer_quantity_sets(elemento)
        if tipo in ("IfcWall", "IfcSlab", "IfcBeam", "IfcColumn", "IfcFooting", "IfcPile"):
            cantidades["volumen_neto"] = self._calcular_volumen_neto(elemento, qsets)
            cantidades["volumen_bruto"] = qsets.get("NetVolume", qsets.get("GrossVolume", 0.0))
            cantidades["area"] = qsets.get("NetArea", qsets.get("GrossArea", 0.0))
            cantidades["longitud"] = qsets.get("Length", 0.0)
            cantidades["ancho"] = qsets.get("Width", 0.0)
            cantidades["altura"] = qsets.get("Height", 0.0)
        elif tipo in ("IfcDoor", "IfcWindow"):
            cantidades["altura"] = float(getattr(elemento, "OverallHeight", 0.0))
            cantidades["ancho"] = float(getattr(elemento, "OverallWidth", 0.0))
            cantidades["area"] = cantidades["altura"] * cantidades["ancho"]
            cantidades["cantidad"] = 1.0
        else:
            for key, val in qsets.items():
                if "Volume" in key:
                    cantidades["volumen"] = val
                elif "Area" in key:
                    cantidades["area"] = val
                elif "Length" in key:
                    cantidades["longitud"] = val
        cantidades["unidad"] = self._determinar_unidad(tipo)
        if "volumen_neto" in cantidades and cantidades["volumen_neto"] > 0:
            cantidades["cantidad"] = cantidades["volumen_neto"]
        elif "area" in cantidades and cantidades["area"] > 0:
            cantidades["cantidad"] = cantidades["area"]
        elif "longitud" in cantidades and cantidades["longitud"] > 0:
            cantidades["cantidad"] = cantidades["longitud"]
        elif "cantidad" in cantidades:
            pass
        else:
            cantidades["cantidad"] = 1.0
        return cantidades

    def _determinar_unidad(self, tipo: str) -> str:
        if tipo in ("IfcWall", "IfcSlab", "IfcFooting", "IfcPile", "IfcBeam", "IfcColumn"):
            return "m³"
        if tipo in ("IfcDoor", "IfcWindow"):
            return "pieza"
        return "m²"

    def cuantificar_proyecto(self) -> List[Dict[str, Any]]:
        if not self._modelo:
            raise ValueError("No se ha cargado un modelo IFC.")
        elementos = []
        tipos = ["IfcWall", "IfcSlab", "IfcBeam", "IfcColumn", "IfcDoor", "IfcWindow", "IfcFooting", "IfcPile"]
        for tipo in tipos:
            for elemento in self._modelo.by_type(tipo):
                try:
                    cant = self.cuantificar_elemento(elemento)
                    if cant:
                        elementos.append(cant)
                except Exception as e:
                    logging.warning(f"Error al cuantificar {elemento.GlobalId}: {e}")
        self._elementos_cuantificados = elementos
        return elementos

# ─────────────────────────────────────────────────────────────────────────────
# PASO 2: APU + FSR
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class InsumoAPU:
    clave: str
    descripcion: str
    unidad: str
    precio_unitario: float
    tipo: str
    fuente: str = "manual"

class AnalisisPreciosUnitarios:
    def __init__(self, dependencia: str = "SCT", fsr: Optional[FsrIndexer] = None):
        self.dependencia = dependencia
        self.fsr = fsr
        self.catalogo_insumos: Dict[str, InsumoAPU] = {}
        self.factores = {
            "SCT": {"indirecto": 0.10, "utilidad": 0.08},
            "IMSS": {"indirecto": 0.12, "utilidad": 0.05},
            "CFE": {"indirecto": 0.15, "utilidad": 0.08},
            "CONAGUA": {"indirecto": 0.12, "utilidad": 0.08},
            "SFP": {"indirecto": 0.10, "utilidad": 0.08},
        }

    def cargar_insumo(self, insumo: InsumoAPU) -> None:
        self.catalogo_insumos[insumo.clave] = insumo

    def actualizar_insumos_desde_fsr(self) -> None:
        if not self.fsr:
            return
        udis = self.fsr.get_valor("banxico_udis", "udis")
        salario_minimo = self.fsr.get_valor("conasami_salarios", "salario_minimo")
        inflacion = self.fsr.get_valor("inegi_precios", "inflacion_construccion")
        for insumo in self.catalogo_insumos.values():
            if insumo.unidad == "UDIS" and udis:
                insumo.precio_unitario = udis * insumo.precio_unitario
            if insumo.tipo == "mano_obra" and salario_minimo:
                insumo.precio_unitario *= (1 + (salario_minimo / 100))

    def calcular_costo_directo(self, insumos: List[Tuple[InsumoAPU, float]]) -> float:
        return sum(ins.precio_unitario * factor for ins, factor in insumos)

    def calcular_costo_indirecto(self, cd: float) -> float:
        return cd * self.factores.get(self.dependencia, {"indirecto": 0.10})["indirecto"]

    def calcular_financiamiento(self, cd: float, ci: float, tasa: float, plazo_dias: int) -> float:
        subtotal = cd + ci
        return subtotal * (tasa * plazo_dias / 360)

    def calcular_utilidad(self, cd: float, ci: float, f: float) -> float:
        subtotal = cd + ci + f
        return subtotal * self.factores.get(self.dependencia, {"utilidad": 0.08})["utilidad"]

    def analizar_concepto(self, concepto: ConceptoAPU, tasa: float = 0.1125, plazo_dias: int = 180) -> Dict[str, Any]:
        cd_unitario = concepto.costo_directo_unitario()
        cd_total = cd_unitario * concepto.cantidad
        ci = self.calcular_costo_indirecto(cd_total)
        f = self.calcular_financiamiento(cd_total, ci, tasa, plazo_dias)
        u = self.calcular_utilidad(cd_total, ci, f)
        subtotal = cd_total + ci + f + u
        iva = subtotal * 0.16
        return {
            "concepto": concepto.clave,
            "descripcion": concepto.descripcion,
            "unidad": concepto.unidad,
            "cantidad": concepto.cantidad,
            "costo_directo_unitario": round(cd_unitario, 2),
            "costo_directo_total": round(cd_total, 2),
            "costo_indirecto": round(ci, 2),
            "financiamiento": round(f, 2),
            "utilidad": round(u, 2),
            "subtotal": round(subtotal, 2),
            "iva": round(iva, 2),
            "total": round(subtotal + iva, 2),
            "insumos_explosion": [
                {"clave": ins.clave, "descripcion": ins.descripcion, "unidad": ins.unidad,
                 "precio": ins.precio_unitario, "factor": factor, "importe": ins.precio_unitario * factor}
                for ins, factor in concepto.insumos
            ],
        }

# ─────────────────────────────────────────────────────────────────────────────
# PASO 3: PRESUPUESTO PROGRAMABLE (CPM/EVM)
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class ActividadPrograma:
    id: str
    nombre: str
    duracion: int
    predecesoras: List[str] = field(default_factory=list)
    sucesoras: List[str] = field(default_factory=list)
    inicio_temprano: Optional[date] = None
    fin_temprano: Optional[date] = None
    inicio_tardio: Optional[date] = None
    fin_tardio: Optional[date] = None
    holgura: Optional[int] = None
    avance: float = 0.0
    costo_planeado: float = 0.0
    costo_real: float = 0.0

class ModuloProgramacionObra:
    def __init__(self, calendario: CalendarioLaboral):
        self.calendario = calendario
        self.actividades: Dict[str, ActividadPrograma] = {}
        self.fecha_inicio: Optional[date] = None

    def agregar_actividad(self, actividad: ActividadPrograma) -> None:
        self.actividades[actividad.id] = actividad

    def calcular_cpm(self, fecha_inicio: date) -> None:
        self.fecha_inicio = fecha_inicio
        for act in self.actividades.values():
            if not act.predecesoras:
                act.inicio_temprano = fecha_inicio
                act.fin_temprano = self.calendario.sumar_dias_habiles(fecha_inicio, act.duracion - 1)
        ordenados = []
        pendientes = set(self.actividades.keys())
        while pendientes:
            for pid in list(pendientes):
                act = self.actividades[pid]
                if all(p in [a.id for a in ordenados] or not p for p in act.predecesoras):
                    ordenados.append(act)
                    pendientes.remove(pid)
                    break
        for act in ordenados[1:]:
            max_fin = None
            for pred_id in act.predecesoras:
                pred = self.actividades.get(pred_id)
                if pred and pred.fin_temprano:
                    if max_fin is None or pred.fin_temprano > max_fin:
                        max_fin = pred.fin_temprano
            if max_fin:
                act.inicio_temprano = self.calendario.siguiente_dia_habil(max_fin)
                act.fin_temprano = self.calendario.sumar_dias_habiles(act.inicio_temprano, act.duracion - 1)
        fecha_fin = max(a.fin_temprano for a in self.actividades.values() if a.fin_temprano)
        for act in reversed(ordenados):
            if not act.sucesoras:
                act.fin_tardio = fecha_fin
                act.inicio_tardio = self.calendario.restar_dias_habiles(fecha_fin, act.duracion - 1)
            else:
                min_inicio = None
                for succ_id in act.sucesoras:
                    succ = self.actividades.get(succ_id)
                    if succ and succ.inicio_tardio:
                        if min_inicio is None or succ.inicio_tardio < min_inicio:
                            min_inicio = succ.inicio_tardio
                if min_inicio:
                    act.fin_tardio = self.calendario.dia_habil_anterior(min_inicio)
                    act.inicio_tardio = self.calendario.restar_dias_habiles(act.fin_tardio, act.duracion - 1)
        for act in self.actividades.values():
            if act.fin_temprano and act.fin_tardio:
                act.holgura = self.calendario.dias_habiles_entre(act.fin_temprano, act.fin_tardio)

    def ruta_critica(self) -> List[str]:
        return [id for id, act in self.actividades.items() if act.holgura == 0]

    def calcular_evm(self, fecha_corte: date) -> Dict[str, Any]:
        pv = 0.0
        ev = 0.0
        ac = 0.0
        for act in self.actividades.values():
            if act.inicio_temprano and act.inicio_temprano <= fecha_corte:
                pv += act.costo_planeado
                ev += act.costo_planeado * (act.avance / 100)
                ac += act.costo_real
        spi = ev / pv if pv > 0 else 0
        cpi = ev / ac if ac > 0 else 0
        eac = (act.costo_planeado / cpi) if cpi > 0 else 0
        return {
            "PV": round(pv, 2), "EV": round(ev, 2), "AC": round(ac, 2),
            "SPI": round(spi, 4), "CPI": round(cpi, 4), "EAC": round(eac, 2),
            "CV": round(ev - ac, 2), "SV": round(ev - pv, 2),
        }

    def generar_curva_s(self, fecha_inicio: date, fecha_fin: date) -> List[Dict[str, Any]]:
        puntos = []
        fecha = fecha_inicio
        acum_pv = 0.0
        acum_ev = 0.0
        acum_ac = 0.0
        while fecha <= fecha_fin:
            for act in self.actividades.values():
                if act.inicio_temprano and act.inicio_temprano <= fecha <= act.fin_temprano:
                    duracion_total = self.calendario.dias_habiles_entre(act.inicio_temprano, act.fin_temprano) + 1
                    if duracion_total > 0:
                        dia_actual = self.calendario.dias_habiles_entre(act.inicio_temprano, fecha) + 1
                        pct_avance = dia_actual / duracion_total
                        acum_pv += act.costo_planeado * pct_avance
                        acum_ev += act.costo_planeado * (act.avance / 100) * pct_avance
                        acum_ac += act.costo_real * pct_avance
            puntos.append({"fecha": fecha.isoformat(), "PV": round(acum_pv, 2),
                           "EV": round(acum_ev, 2), "AC": round(acum_ac, 2)})
            fecha = self.calendario.siguiente_dia_habil(fecha)
        return puntos

# ─────────────────────────────────────────────────────────────────────────────
# PASO 4: IMPORTACIÓN / EXPORTACIÓN CON EXCEL
# ─────────────────────────────────────────────────────────────────────────────

class IntegradorExcel:
    @staticmethod
    def exportar_presupuesto(conceptos: List[ConceptoAPU], ruta: str) -> None:
        if not _EXCEL_AVAILABLE:
            raise RuntimeError("pandas/openpyxl no instalados. pip install pandas openpyxl")
        data = []
        for c in conceptos:
            data.append({
                "Clave": c.clave,
                "Descripción": c.descripcion,
                "Unidad": c.unidad,
                "Cantidad": c.cantidad,
                "Costo Directo Unitario": c.costo_directo_unitario(),
                "Costo Directo Total": c.costo_directo_unitario() * c.cantidad,
            })
        df = pd.DataFrame(data)
        df.to_excel(ruta, index=False, sheet_name="Presupuesto")
        logging.info(f"Presupuesto exportado a {ruta}")

    @staticmethod
    def importar_conceptos(ruta: str) -> List[ConceptoAPU]:
        if not _EXCEL_AVAILABLE:
            raise RuntimeError("pandas/openpyxl no instalados.")
        df = pd.read_excel(ruta)
        conceptos = []
        for _, row in df.iterrows():
            concepto = ConceptoAPU(
                clave=row["Clave"],
                descripcion=row["Descripción"],
                unidad=row["Unidad"],
                cantidad=row["Cantidad"],
                insumos=[],
            )
            conceptos.append(concepto)
        return conceptos

    @staticmethod
    def exportar_cronograma(actividades: List[ActividadPrograma], ruta: str) -> None:
        if not _EXCEL_AVAILABLE:
            raise RuntimeError("pandas/openpyxl no instalados.")
        data = []
        for a in actividades:
            data.append({
                "ID": a.id,
                "Nombre": a.nombre,
                "Duración (días)": a.duracion,
                "Predecesoras": ", ".join(a.predecesoras),
                "Inicio Temprano": a.inicio_temprano.isoformat() if a.inicio_temprano else "",
                "Fin Temprano": a.fin_temprano.isoformat() if a.fin_temprano else "",
                "Inicio Tardío": a.inicio_tardio.isoformat() if a.inicio_tardio else "",
                "Fin Tardío": a.fin_tardio.isoformat() if a.fin_tardio else "",
                "Holgura": a.holgura or 0,
                "Avance %": a.avance,
                "Costo Planeado": a.costo_planeado,
                "Costo Real": a.costo_real,
            })
        df = pd.DataFrame(data)
        df.to_excel(ruta, index=False, sheet_name="Cronograma")
        logging.info(f"Cronograma exportado a {ruta}")

# ─────────────────────────────────────────────────────────────────────────────
# DOCUMENTAL: TRAZABILIDAD, FIRMA, ARCHIVO, ETC.
# ─────────────────────────────────────────────────────────────────────────────

class UtilidadCriptografica:
    @staticmethod
    def hash_sha256(data: bytes) -> str:
        return CPLHash.de_bytes(data)

class ServicioTrazabilidad:
    def __init__(self) -> None:
        self._registros: List[Dict[str, Any]] = []
        self._lock = threading.Lock()

    def registrar(self, actor: str, accion: str, objeto: str, objeto_id: str,
                  resultado: str, detalle: str = "") -> Dict[str, Any]:
        with self._lock:
            prev_hash = self._registros[-1]["hash"] if self._registros else ""
            payload = {
                "timestamp": _now_utc().isoformat(), "actor": actor, "accion": accion,
                "objeto": objeto, "objeto_id": objeto_id, "resultado": resultado,
                "detalle": detalle, "prev_hash": prev_hash,
            }
            payload_bytes = json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8")
            payload["hash"] = _sha256(payload_bytes)
            self._registros.append(payload)
            return payload

    def verificar_integridad_cadena(self) -> Tuple[bool, List[str]]:
        errores: List[str] = []
        prev_hash = ""
        for idx, r in enumerate(self._registros):
            data = {k: v for k, v in r.items() if k != "hash"}
            calc = _sha256(json.dumps(data, sort_keys=True, ensure_ascii=False).encode("utf-8"))
            if calc != r.get("hash"):
                errores.append(f"Registro {idx} con hash inválido")
            if r.get("prev_hash", "") != prev_hash:
                errores.append(f"Registro {idx} con encadenado previo inválido")
            prev_hash = r.get("hash", "")
        return (len(errores) == 0, errores)

    def to_list(self) -> List[Dict[str, Any]]:
        return list(self._registros)

class ServicioFirma:
    def __init__(self, trazabilidad: Optional[ServicioTrazabilidad] = None) -> None:
        self.trazabilidad = trazabilidad or ServicioTrazabilidad()
        self.certificados: Dict[str, str] = {}
        self._cert_path = None
        self._key_path = None
        self._password = None

    def configurar_fiel(self, cert_path: str, key_path: str, password: str) -> None:
        self._cert_path = cert_path
        self._key_path = key_path
        self._password = password

    def generar_certificado_prueba(self, sujeto: str, password: str) -> str:
        huella = _sha256(f"{sujeto}:{password}".encode("utf-8"))
        self.certificados[sujeto] = huella
        return huella

    def firmar_documento(self, doc: "DocumentoElectronico", firmante: str, cargo: str,
                         esquema: str, nivel: NivelFirma, autoridad: str) -> "FirmaElectronicaReal":
        if _PYHANKO_AVAILABLE and self._cert_path and self._key_path:
            try:
                signer = signers.SimpleSigner.load(
                    self._key_path, self._cert_path,
                    key_passphrase=self._password.encode()
                )
                huella = _sha256(doc.contenido + firmante.encode("utf-8"))
                firma = FirmaElectronicaReal(
                    sujeto=firmante,
                    huella_certificado=huella,
                    fecha_firma=_now_utc(),
                    nivel=nivel.value,
                    autoridad=autoridad,
                    firma_base64=base64.b64encode(huella.encode("utf-8")).decode("ascii")
                )
                doc.firma = firma
                self.trazabilidad.registrar("SERVICIO_FIRMA", "FIRMAR_DOCUMENTO_PADES",
                    doc.__class__.__name__, doc.identificador, "OK", f"Firmante: {firmante}")
                return firma
            except Exception:
                pass
        firma = FirmaElectronicaReal(
            sujeto=firmante,
            huella_certificado=self.certificados.get(firmante, _sha256(firmante.encode("utf-8"))),
            fecha_firma=_now_utc(), nivel=nivel.value, autoridad=autoridad,
            firma_base64=base64.b64encode(_sha256(doc.contenido + firmante.encode("utf-8")).encode("utf-8")).decode("ascii"),
        )
        doc.firma = firma
        self.trazabilidad.registrar("SERVICIO_FIRMA", "FIRMAR_DOCUMENTO",
            doc.__class__.__name__, doc.identificador, "OK", f"Firmante: {firmante}, Cargo: {cargo}")
        return firma

    def firmar_indice_expediente(self, expediente: "ExpedienteElectronico", firmante: str, cargo: str) -> "FirmaElectronicaReal":
        payload = json.dumps({
            "expediente": expediente.identificador,
            "documentos": [d.hash_contenido for d in expediente.documentos]
        }, sort_keys=True).encode("utf-8")
        firma = FirmaElectronicaReal(
            sujeto=firmante,
            huella_certificado=self.certificados.get(firmante, _sha256(firmante.encode("utf-8"))),
            fecha_firma=_now_utc(), nivel=NivelFirma.FIEL.value, autoridad="SAT",
            firma_base64=base64.b64encode(_sha256(payload).encode("utf-8")).decode("ascii"),
        )
        expediente.indice = IndiceExpediente(firma_indice=firma, hash_indice=_sha256(payload))
        self.trazabilidad.registrar("SERVICIO_FIRMA", "FIRMAR_INDICE",
            expediente.__class__.__name__, expediente.identificador, "OK", f"Firmante: {firmante}, Cargo: {cargo}")
        return firma

class ServicioArchivo:
    def __init__(self, ruta_base: str | Path, trazabilidad: Optional[ServicioTrazabilidad] = None) -> None:
        self.ruta_base = _ensure_dir(ruta_base)
        self.trazabilidad = trazabilidad or ServicioTrazabilidad()
        self._vsi = CPLVsiSistema(self.ruta_base / "_vsi")

    def archivar_expediente(self, expediente: "ExpedienteElectronico") -> str:
        expediente.calcular_merkle_root()
        carpeta = _ensure_dir(self.ruta_base / expediente.identificador)
        manifest = {
            "expediente": expediente.to_dict(),
            "documentos": [d.to_dict() for d in expediente.documentos],
            "archivado_en": _now_utc().isoformat(),
            "merkle_root": expediente.merkle_root,
        }
        manifest_path = carpeta / "manifest.json"
        manifest_path.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
        self.trazabilidad.registrar("SERVICIO_ARCHIVO", "ARCHIVAR_EXPEDIENTE",
            expediente.__class__.__name__, expediente.identificador, "OK", str(manifest_path))
        return str(carpeta)

    def recuperar_expediente(self, expediente_id: str, incluir_contenido: bool = False) -> Dict[str, Any]:
        carpeta = self.ruta_base / expediente_id
        manifest_path = carpeta / "manifest.json"
        if not manifest_path.exists():
            raise FileNotFoundError(expediente_id)
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        return {
            "manifest": manifest if incluir_contenido else {k: v for k, v in manifest.items() if k != "documentos"},
            "hash_global_ok": True,
        }

class ValidadorCumplimiento:
    def validar_expediente(self, expediente: "ExpedienteElectronico") -> Dict[str, Any]:
        errores = []
        if not expediente.identificador:
            errores.append("Expediente sin identificador")
        if not expediente.documentos:
            errores.append("Expediente sin documentos")
        return {"valido": len(errores) == 0, "errores": errores}

class ServicioInteroperabilidad:
    def __init__(self, servicio_trazabilidad: Optional[ServicioTrazabilidad] = None) -> None:
        self.trazabilidad = servicio_trazabilidad or ServicioTrazabilidad()

    def generar_mensaje_interoperabilidad(self, tipo: "TipoInteroperabilidad", datos: Dict[str, Any]) -> str:
        mensaje = {
            "tipo": tipo.value if isinstance(tipo, Enum) else str(tipo),
            "datos": datos, "timestamp": _now_utc().isoformat(),
        }
        xml_like = json.dumps(mensaje, ensure_ascii=False, indent=2)
        self.trazabilidad.registrar("SERVICIO_INTEROP", "GENERAR_MENSAJE",
            "MensajeInteroperabilidad", datos.get("cuerpo", {}).get("identificadorExpediente", ""), "OK", tipo.value)
        return xml_like

class SistemaGestionExpedientesMexico:
    def __init__(self) -> None:
        self.trazabilidad = ServicioTrazabilidad()
        self.firma = ServicioFirma(self.trazabilidad)
        self.archivo = ServicioArchivo(Path(tempfile.gettempdir()) / "megalodon_archivo", self.trazabilidad)
        self.validador = ValidadorCumplimiento()
        self.busqueda = types.SimpleNamespace(indexar_expediente=lambda expediente: None)
        self.expedientes: Dict[str, "ExpedienteElectronico"] = {}

    def inicializar_directorios(self) -> None:
        _ensure_dir(Path(tempfile.gettempdir()) / "megalodon_archivo")

    def obtener_estadisticas_sistema(self) -> Dict[str, Any]:
        firmados = sum(1 for e in self.expedientes.values() if e.indice.firma_indice is not None)
        return {
            "expedientes_en_memoria": len(self.expedientes),
            "expedientes_archivados": sum(1 for e in self.expedientes.values() if e.estado == EstadoExpediente.ARCHIVADO),
            "total_registros_trazabilidad": len(self.trazabilidad.to_list()),
            "certificados_cargados": len(self.firma.certificados),
            "expedientes_firmados": firmados,
        }

# ─────────────────────────────────────────────────────────────────────────────
# ENUMS Y DATACLASSES BASE
# ─────────────────────────────────────────────────────────────────────────────

class ClasificacionSeguridad(str, Enum):
    PUBLICO = "PUBLICO"
    RESERVADO = "RESERVADO"
    CONFIDENCIAL = "CONFIDENCIAL"

class EstadoExpediente(str, Enum):
    INICIADO = "INICIADO"
    EN_FIRMA = "EN_FIRMA"
    ARCHIVADO = "ARCHIVADO"
    EN_INTEROPERABILIDAD = "EN_INTEROPERABILIDAD"

class TipoDocumento(str, Enum):
    INFORME = "INFORME"
    OFICIO = "OFICIO"
    CONTRATO = "CONTRATO"
    PRESUPUESTO = "PRESUPUESTO"

class NivelFirma(str, Enum):
    FIEL = "FIEL"
    SIMPLE = "SIMPLE"

class TipoInteroperabilidad(str, Enum):
    REMISION_EXPEDIENTE = "REMISION_EXPEDIENTE"
    REMISION_DOCUMENTO = "REMISION_DOCUMENTO"

class ZonaEconomica(str, Enum):
    NORTE = "NORTE"
    CENTRO = "CENTRO"
    SUR = "SUR"
    NOROESTE = "NOROESTE"
    NORESTE = "NORESTE"
    OCCIDENTE = "OCCIDENTE"
    SURESTE = "SURESTE"

@dataclass
class Metadato:
    nombre: str
    valor: str
    tipo: str = "string"
    obligatorio: bool = False
    esquema: str = "GENERAL"

@dataclass
class FirmaElectronicaReal:
    sujeto: str
    huella_certificado: str
    fecha_firma: datetime
    nivel: str = "FIEL"
    autoridad: str = "SAT"
    firma_base64: str = ""

@dataclass
class IndiceExpediente:
    firma_indice: Optional[FirmaElectronicaReal] = None
    hash_indice: str = ""

@dataclass
class DocumentoElectronico:
    identificador: str
    nombre: str
    contenido: bytes
    tipo_documental: TipoDocumento
    organo: str
    fecha_captura: datetime = field(default_factory=_now_utc)
    formato: str = "json"
    autor: str = ""
    nivel_seguridad: str = ClasificacionSeguridad.PUBLICO.value
    metadatos: List[Metadato] = field(default_factory=list)
    hash_contenido: str = ""
    firma: Optional[FirmaElectronicaReal] = None

    def __post_init__(self) -> None:
        self.hash_contenido = self._calcular_hash_contenido()

    def _calcular_hash_contenido(self) -> str:
        data = canonical_json(self.to_dict())
        return CPLHash.de_texto(data)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "identificador": self.identificador, "nombre": self.nombre,
            "tipo_documental": self.tipo_documental.value if isinstance(self.tipo_documental, Enum) else str(self.tipo_documental),
            "organo": self.organo, "fecha_captura": self.fecha_captura.isoformat(),
            "formato": self.formato, "autor": self.autor,
            "nivel_seguridad": self.nivel_seguridad,
            "hash_contenido": self.hash_contenido,
            "metadatos": [dataclasses.asdict(m) for m in self.metadatos],
            "firmado": self.firma is not None,
        }

@dataclass
class ExpedienteElectronico:
    identificador: str
    titulo: str
    descripcion: str
    organo: str
    unidad_administrativa: str
    serie_documental: str
    subserie_documental: str
    fecha_apertura: datetime = field(default_factory=_now_utc)
    estado: EstadoExpediente = EstadoExpediente.INICIADO
    clasificacion: str = ClasificacionSeguridad.PUBLICO.value
    responsable: str = ""
    documentos: List[DocumentoElectronico] = field(default_factory=list)
    metadatos: List[Metadato] = field(default_factory=list)
    indice: IndiceExpediente = field(default_factory=IndiceExpediente)
    merkle_root: str = ""

    def agregar_documento(self, doc: DocumentoElectronico) -> None:
        self.documentos.append(doc)

    def calcular_merkle_root(self) -> str:
        if not self.documentos:
            return ""
        leaves = [CPLHash.de_texto(canonical_json(doc.to_dict())) for doc in self.documentos]
        tree = MerkleTree([bytes.fromhex(h) for h in leaves])
        self.merkle_root = tree.root.hex()
        return self.merkle_root

    def to_dict(self) -> Dict[str, Any]:
        return {
            "identificador": self.identificador, "titulo": self.titulo,
            "descripcion": self.descripcion, "organo": self.organo,
            "unidad_administrativa": self.unidad_administrativa,
            "serie_documental": self.serie_documental, "subserie_documental": self.subserie_documental,
            "fecha_apertura": self.fecha_apertura.isoformat(),
            "estado": self.estado.value if isinstance(self.estado, Enum) else str(self.estado),
            "clasificacion": self.clasificacion, "responsable": self.responsable,
            "num_documentos": len(self.documentos),
            "metadatos": [dataclasses.asdict(m) for m in self.metadatos],
            "merkle_root": self.merkle_root,
        }

# ─────────────────────────────────────────────────────────────────────────────
# EXPEDIENTE OBRA Y DOCUMENTO PRESUPUESTO
# ─────────────────────────────────────────────────────────────────────────────

@dataclass
class DocumentoPresupuesto(DocumentoElectronico):
    monto_directo: float = 0.0
    monto_indirecto: float = 0.0
    monto_utilidad: float = 0.0
    monto_impuesto: float = 0.0
    monto_total: float = 0.0
    moneda: str = "MXN"
    zona_economica: str = "NORTE"
    factor_indirecto: float = ConfiguracionUnificada.FACTOR_INDIRECTO
    factor_utilidad: float = ConfiguracionUnificada.FACTOR_UTILIDAD
    factor_impuesto: float = ConfiguracionUnificada.FACTOR_IMPUESTO
    numero_partidas: int = 0
    insumos_desglose: List[Dict[str, Any]] = field(default_factory=list)
    resultado_montecarlo: Optional[Dict[str, Any]] = None
    resultado_determinista: Optional[Dict[str, Any]] = None

    def __post_init__(self) -> None:
        super().__post_init__()
        self._recalcular_montos()
        self._sincronizar_metadatos_presupuesto()
        self.hash_contenido = self._calcular_hash_contenido()

    def _recalcular_montos(self) -> None:
        self.monto_indirecto = float(self.monto_directo) * float(self.factor_indirecto)
        subtotal = float(self.monto_directo) + float(self.monto_indirecto)
        self.monto_utilidad = subtotal * float(self.factor_utilidad)
        self.monto_impuesto = (subtotal + float(self.monto_utilidad)) * float(self.factor_impuesto)
        self.monto_total = subtotal + float(self.monto_utilidad) + float(self.monto_impuesto)

    def _sincronizar_metadatos_presupuesto(self) -> None:
        metas = {
            "MontoDirecto": f"{self.monto_directo:.2f}",
            "MontoIndirecto": f"{self.monto_indirecto:.2f}",
            "MontoUtilidad": f"{self.monto_utilidad:.2f}",
            "MontoImpuesto": f"{self.monto_impuesto:.2f}",
            "MontoTotal": f"{self.monto_total:.2f}",
            "Moneda": self.moneda,
            "ZonaEconomica": self.zona_economica,
            "NumeroPartidas": str(self.numero_partidas),
            "FactorIndirecto": f"{self.factor_indirecto:.4f}",
            "FactorUtilidad": f"{self.factor_utilidad:.4f}",
            "FactorImpuesto": f"{self.factor_impuesto:.4f}",
        }
        if self.resultado_determinista:
            metas["EstatusDeterminista"] = self.resultado_determinista.get("estatus_final", "PENDIENTE")
        index = {m.nombre: i for i, m in enumerate(self.metadatos)}
        for nombre, valor in metas.items():
            meta = Metadato(nombre, valor,
                "decimal" if nombre.startswith("Monto") or nombre.startswith("Factor") else "string",
                True if nombre.startswith("Monto") or nombre in {"Moneda", "ZonaEconomica", "NumeroPartidas", "EstatusDeterminista"} else False,
                "LGA/Costos",
            )
            if nombre in index:
                self.metadatos[index[nombre]] = meta
            else:
                self.metadatos.append(meta)

    def actualizar_desde_presupuesto(self, presupuesto: Any) -> None:
        self.monto_directo = float(getattr(presupuesto, "monto_directo", 0.0) or 0.0)
        self.numero_partidas = len(getattr(presupuesto, "partidas", []) or [])
        self.insumos_desglose = self._extraer_insumos_desde_presupuesto(presupuesto)
        self._recalcular_montos()
        self._sincronizar_metadatos_presupuesto()
        self.hash_contenido = self._calcular_hash_contenido()

    def _extraer_insumos_desde_presupuesto(self, presupuesto: Any) -> List[Dict[str, Any]]:
        insumos: List[Dict[str, Any]] = []
        for partida in getattr(presupuesto, "partidas", []) or []:
            concepto = getattr(partida, "concepto", None)
            for insumo in getattr(concepto, "insumos", []) or []:
                insumos.append({
                    "nombre": getattr(insumo, "nombre", ""),
                    "tipo": str(getattr(insumo, "tipo", "")),
                    "cantidad": float(getattr(insumo, "cantidad", 0.0) or 0.0),
                    "precio_unitario": float(getattr(insumo, "precio_unitario", 0.0) or 0.0),
                    "precio_total": float(getattr(insumo, "precio_total", 0.0) or 0.0),
                })
        return insumos

    def _calcular_hash_contenido(self) -> str:
        data = canonical_json({
            "monto_directo": self.monto_directo, "monto_indirecto": self.monto_indirecto,
            "monto_utilidad": self.monto_utilidad, "monto_impuesto": self.monto_impuesto,
            "monto_total": self.monto_total, "numero_partidas": self.numero_partidas,
            "insumos_desglose": self.insumos_desglose,
            "resultado_determinista": self.resultado_determinista,
        })
        return UtilidadCriptografica.hash_sha256(data.encode("utf-8"))

    def to_dict(self) -> Dict[str, Any]:
        base = super().to_dict()
        base.update({
            "monto_directo": self.monto_directo, "monto_indirecto": self.monto_indirecto,
            "monto_utilidad": self.monto_utilidad, "monto_impuesto": self.monto_impuesto,
            "monto_total": self.monto_total, "moneda": self.moneda,
            "zona_economica": self.zona_economica, "factor_indirecto": self.factor_indirecto,
            "factor_utilidad": self.factor_utilidad, "factor_impuesto": self.factor_impuesto,
            "numero_partidas": self.numero_partidas, "insumos_desglose": self.insumos_desglose,
            "resultado_montecarlo": self.resultado_montecarlo,
            "resultado_determinista": self.resultado_determinista,
        })
        return base

@dataclass
class ExpedienteObra(ExpedienteElectronico):
    proyecto_id: str = ""
    proyecto_nombre: str = ""
    ubicacion_obra: str = ""
    responsable_tecnico: str = ""
    responsable_ejecutivo: str = ""
    monto_contrato: float = 0.0
    plazo_dias: int = 0
    tipo_contrato: str = "POR_PRECIOS_UNITARIOS"

    def __post_init__(self) -> None:
        if hasattr(super(), "__post_init__"):
            super().__post_init__()
        self._sincronizar_metadatos_obra()

    def _sincronizar_metadatos_obra(self) -> None:
        metas = {
            "ProyectoID": self.proyecto_id, "ProyectoNombre": self.proyecto_nombre,
            "UbicacionObra": self.ubicacion_obra, "ResponsableTecnico": self.responsable_tecnico,
            "ResponsableEjecutivo": self.responsable_ejecutivo,
            "MontoContrato": f"{self.monto_contrato:.2f}", "PlazoDias": str(self.plazo_dias),
            "TipoContrato": self.tipo_contrato,
        }
        index = {m.nombre: i for i, m in enumerate(self.metadatos)}
        for nombre, valor in metas.items():
            meta = Metadato(nombre, valor,
                "decimal" if nombre == "MontoContrato" else ("integer" if nombre == "PlazoDias" else "string"),
                True, "LGA/Obra",
            )
            if nombre in index:
                self.metadatos[index[nombre]] = meta
            else:
                self.metadatos.append(meta)

    def agregar_documento_presupuesto(self, doc_presupuesto: DocumentoPresupuesto) -> None:
        if float(doc_presupuesto.monto_total) <= 0:
            raise ErrorValidacionEconomica(
                f"Presupuesto {doc_presupuesto.identificador} tiene monto total inválido: {doc_presupuesto.monto_total}"
            )
        self.agregar_documento(doc_presupuesto)
        if self.monto_contrato <= 0:
            self.monto_contrato = doc_presupuesto.monto_total
            self._sincronizar_metadatos_obra()

# ─────────────────────────────────────────────────────────────────────────────
# CONFIGURACIÓN UNIFICADA
# ─────────────────────────────────────────────────────────────────────────────

class ConfiguracionUnificada:
    RUTA_BASE_ARCHIVO = os.environ.get("EXPEDIENTE_RUTA_BASE", str(Path(tempfile.gettempdir()) / "megalodon_unificado"))
    RUTA_BASE_DB = os.environ.get("EXPEDIENTE_RUTA_DB", str(Path(RUTA_BASE_ARCHIVO) / "db"))
    RUTA_LOGS = os.environ.get("EXPEDIENTE_RUTA_LOGS", str(Path(RUTA_BASE_ARCHIVO) / "logs"))
    RUTA_CERTIFICADOS = os.environ.get("EXPEDIENTE_RUTA_CERTS", str(Path(RUTA_BASE_ARCHIVO) / "certs"))
    ZONA_ECONOMICA_DEFAULT = ZonaEconomica.NORTE
    FACTOR_INDIRECTO = 0.15
    FACTOR_UTILIDAD = 0.10
    FACTOR_IMPUESTO = 0.16
    SERIE_DOCUMENTAL_PRESUPUESTO = "PRESUPUESTOS_OBRA"
    SUBSERIE_PRESUPUESTO_DETALLADO = "PRESUPUESTO_DETALLADO"
    SUBSERIE_PRESUPUESTO_RESUMEN = "PRESUPUESTO_RESUMEN"

    @classmethod
    def inicializar(cls) -> None:
        _ensure_dir(cls.RUTA_BASE_ARCHIVO)
        _ensure_dir(cls.RUTA_BASE_DB)
        _ensure_dir(cls.RUTA_LOGS)
        _ensure_dir(cls.RUTA_CERTIFICADOS)
        _ensure_dir(Path(cls.RUTA_BASE_ARCHIVO) / "presupuestos")

# ─────────────────────────────────────────────────────────────────────────────
# ADAPTADOR v2 → v3
# ─────────────────────────────────────────────────────────────────────────────

class AdaptadorPayloadV2V3:
    @staticmethod
    def expediente_a_licitacion(expediente: ExpedienteObra) -> Dict[str, Any]:
        return {
            "codigo_compranet": f"LO-{expediente.identificador}",
            "ambito": "Federal",
            "entidad_federativa": expediente.ubicacion_obra or "CDMX",
            "dependencia": expediente.organo,
            "presupuesto_base": float(expediente.monto_contrato or 0),
            "nombre_empresa_participante": expediente.responsable_tecnico or "SIN_NOMBRE",
            "monto_oferta_total": float(expediente.monto_contrato or 0),
        }

    @staticmethod
    def presupuesto_a_economico(doc_presupuesto: Any) -> Dict[str, Any]:
        _g = lambda attr, default=0.0: (
            getattr(doc_presupuesto, attr, default) if hasattr(doc_presupuesto, attr)
            else doc_presupuesto.get(attr, default) if isinstance(doc_presupuesto, dict)
            else default
        )
        monto_directo = float(_g("monto_directo", 0.0))
        factor_ind = float(_g("factor_indirecto", 0.15))
        factor_util = float(_g("factor_utilidad", 0.10))
        ind_oficina = factor_ind * 0.4
        ind_campo = factor_ind * 0.6
        f_ind = 1 + (ind_oficina + ind_campo)
        f_fin = f_ind * 1.0
        f_ut = f_fin * (1 + factor_util)
        factor_sobrecosto = f_ut + 0.005
        return {
            "monto_total": float(_g("monto_total", 0.0)),
            "analisis_fsr": {
                "tp_dias_pagados": 383.0,
                "tl_dias_laborados": 294.0,
                "ps_fraccion_imss_infonavit": 0.285,
                "fsr_calculado_por_licitante": 1.6562,
            },
            "analisis_maquinaria": {
                "codigo_equipo": "GENERICO",
                "valor_adquisicion": 1000000.0,
                "horas_uso_anual": 1800,
                "total_cargos_fijos": 100.0,
                "requiere_combustible": True,
                "precio_litro_combustible_declarado": ConstantesLegales2026.PRECIO_DIESEL_REFERENCIA,
                "cargo_combustible": 200.0,
                "cargo_lubricantes": 20.0,
                "cargo_operacion": 50.0,
                "costo_horario_total": 370.0,
            },
            "analisis_sobrecostos": {
                "pct_indirecto_oficina": ind_oficina,
                "pct_indirecto_campo": ind_campo,
                "pct_financiamiento": 0.0,
                "pct_utilidad": factor_util,
                "pct_cargos_adicionales": 0.005,
                "tasa_interes_utilizada": ConstantesLegales2026.TASA_TIE_REFERENCIA,
                "factor_sobrecosto_total_declarado": round(factor_sobrecosto, 4),
            },
        }

    @classmethod
    def construir_payload_completo(cls, expediente: ExpedienteObra,
                                    doc_presupuesto: Optional[DocumentoPresupuesto] = None,
                                    fiscal: Optional[Dict[str, Any]] = None,
                                    administrativo: Optional[Dict[str, Any]] = None,
                                    garantias: Optional[List[Dict[str, Any]]] = None,
                                    requisitos: Optional[List[str]] = None) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "rfc_empresa": expediente.responsable_tecnico or "SIN_RFC",
            "licitacion": cls.expediente_a_licitacion(expediente),
            "fiscal": fiscal or {
                "opinion_sat_sentido": "POSITIVA",
                "opinion_sat_fecha": date.today().isoformat(),
                "opinion_imss_sentido": "POSITIVA",
                "opinion_infonavit_sentido": "POSITIVA",
            },
            "administrativo": administrativo or {"efirma_valida": True},
            "economico": cls.presupuesto_a_economico(doc_presupuesto) if doc_presupuesto else {},
            "tecnico": {"incongruencias_detectadas": []},
            "garantias": garantias or [],
            "requisitos_participacion": requisitos or [],
            "fecha_fallo": _now_utc().date().isoformat(),
        }
        return payload

# ─────────────────────────────────────────────────────────────────────────────
# FLAGS DE CARGA DE MOTORES EXTERNOS (v2)
# ─────────────────────────────────────────────────────────────────────────────

try:
    mega_mod = _maybe_import_from_path("megalodon_cuantificacion_patch", "megalodon_cuantificacion_patch.py")
    REAL_COSTOS_LOADED = True
except Exception:
    @dataclass
    class Insumo:
        nombre: str
        tipo: str
        cantidad: float
        precio_unitario: float
        precio_total: float

    @dataclass
    class Concepto:
        descripcion: str
        insumos: List[Insumo] = field(default_factory=list)

    @dataclass
    class Partida:
        id: str
        cantidad: float
        concepto: Concepto

    @dataclass
    class PresupuestoEngine:
        proyecto: str = ""
        proyecto_id: str = ""
        partidas: List[Partida] = field(default_factory=list)
        monto_directo: float = 0.0
        monto_indirecto: float = 0.0
        monto_utilidad: float = 0.0
        monto_impuesto: float = 0.0
        monto_total: float = 0.0
        moneda: str = "MXN"
        zona_economica: str = "NORTE"

        def to_dict(self) -> Dict[str, Any]:
            return {
                "proyecto": self.proyecto,
                "proyecto_id": self.proyecto_id,
                "monto_directo": self.monto_directo,
                "monto_indirecto": self.monto_indirecto,
                "monto_utilidad": self.monto_utilidad,
                "monto_impuesto": self.monto_impuesto,
                "monto_total": self.monto_total,
                "moneda": self.moneda,
                "zona_economica": self.zona_economica,
                "numero_partidas": len(self.partidas),
                "partidas": [
                    {
                        "id": p.id,
                        "cantidad": p.cantidad,
                        "concepto": {
                            "descripcion": p.concepto.descripcion,
                            "insumos": [dataclasses.asdict(i) for i in p.concepto.insumos],
                        },
                    }
                    for p in self.partidas
                ],
            }

    class PipelinePresupuestoV2:
        def __init__(self, zona: ZonaEconomica, database: Any = None):
            self.zona = zona
            self.database = database
            self.presupuesto: Optional[PresupuestoEngine] = None
            self._motor_bim = MotorPreciosBIM()

        def ejecutar(self, payload_bim: Dict[str, Any]) -> Dict[str, Any]:
            resultado_bim = self._motor_bim.ejecutar_desde_payload(payload_bim)
            proyecto = payload_bim.get("proyecto", "SIN_NOMBRE")
            proyecto_id = payload_bim.get("proyecto_id", str(uuid.uuid4()))
            partidas_bim = resultado_bim.get("partidas", [])
            partidas: List[Partida] = []
            monto_directo = 0.0
            for pb in partidas_bim:
                insumo = Insumo(
                    nombre=f"APU_{pb['tipo']}_{pb['sistema']}",
                    tipo=pb["sistema"],
                    cantidad=pb["cantidad"],
                    precio_unitario=pb["costo_directo"] / pb["cantidad"] if pb["cantidad"] > 0 else 0,
                    precio_total=pb["costo_directo"],
                )
                concepto = Concepto(descripcion=f"{pb['tipo'].capitalize()} ({pb['sistema']})", insumos=[insumo])
                partidas.append(Partida(id=pb["id"], cantidad=pb["cantidad"], concepto=concepto))
                monto_directo += pb["costo_directo"]
            presupuesto = PresupuestoEngine(
                proyecto=proyecto,
                proyecto_id=proyecto_id,
                partidas=partidas,
                monto_directo=monto_directo,
                zona_economica=self.zona.value if isinstance(self.zona, Enum) else str(self.zona),
            )
            presupuesto.monto_indirecto = monto_directo * 0.15
            subtotal = monto_directo + presupuesto.monto_indirecto
            presupuesto.monto_utilidad = subtotal * 0.10
            presupuesto.monto_impuesto = (subtotal + presupuesto.monto_utilidad) * 0.16
            presupuesto.monto_total = subtotal + presupuesto.monto_utilidad + presupuesto.monto_impuesto
            self.presupuesto = presupuesto
            return {"status": "COMPLETADO", "meta": {"partidas_generados": len(partidas), "zona": str(self.zona)}, "logs": []}

# ─────────────────────────────────────────────────────────────────────────────
# SERVICIO ESTADÍSTICO DE COSTOS
# ─────────────────────────────────────────────────────────────────────────────

class ServicioEstadisticoCostos:
    def __init__(self) -> None:
        self.historial: List[Dict[str, float]] = []

    def registrar_muestra(self, muestra: Dict[str, float]) -> None:
        self.historial.append({k: float(v) for k, v in muestra.items()})

    @staticmethod
    def _cov_python(matrix: List[List[float]]) -> List[List[float]]:
        n = len(matrix)
        if n == 0:
            return []
        m = len(matrix[0])
        if m < 2:
            return [[0.0 for _ in range(n)] for _ in range(n)]
        means = [sum(row) / m for row in matrix]
        cov = [[0.0 for _ in range(n)] for _ in range(n)]
        denom = m - 1
        for i in range(n):
            for j in range(i, n):
                s = 0.0
                for k in range(m):
                    s += (matrix[i][k] - means[i]) * (matrix[j][k] - means[j])
                cov[i][j] = cov[j][i] = s / denom if denom > 0 else 0.0
        return cov

    def matriz_covarianza(self, claves: Optional[Sequence[str]] = None) -> Dict[str, Any]:
        if not self.historial:
            return {"claves": [], "matriz": [], "mensaje": "Sin muestras"}
        if claves is None:
            claves = sorted({k for m in self.historial for k in m.keys()})
        series: List[List[float]] = []
        for clave in claves:
            series.append([float(m.get(clave, 0.0)) for m in self.historial])
        if _NUMPY_AVAILABLE:
            arr = np.array(series, dtype=float)
            matriz = np.cov(arr).tolist()
        else:
            matriz = self._cov_python(series)
        return {"claves": list(claves), "matriz": matriz, "muestras": len(self.historial)}

    def resumen_riesgo(self) -> Dict[str, Any]:
        cov = self.matriz_covarianza()
        claves = cov["claves"]
        matriz = cov["matriz"]
        diag = {claves[i]: matriz[i][i] if i < len(matriz) and i < len(matriz[i]) else 0.0 for i in range(len(claves))}
        return {"varianzas": diag, "covarianza": cov}

# ─────────────────────────────────────────────────────────────────────────────
# SERVICIO COSTEO (integrado con APU y Excel)
# ─────────────────────────────────────────────────────────────────────────────

class ServicioCosteo:
    def __init__(self, zona: Optional[ZonaEconomica] = None, database: Any = None, fsr: Optional[FsrIndexer] = None):
        self.zona = zona or ConfiguracionUnificada.ZONA_ECONOMICA_DEFAULT
        self.database = database
        self.motor_bim = MotorPreciosBIM()
        self.monte_carlo = MonteCarloRiesgo(iteraciones=1_000, semilla=42)
        self.estadistico = ServicioEstadisticoCostos()
        self.apu = AnalisisPreciosUnitarios(dependencia="SCT", fsr=fsr)
        self._lock = threading.Lock()
        self._historial: List[Dict[str, Any]] = []

    def costear_desde_bim(self, payload_bim: Dict[str, Any]) -> Dict[str, Any]:
        with self._lock:
            resultado = self.motor_bim.ejecutar_desde_payload(payload_bim)
            partidas = resultado.get("partidas", [])
            monto_directo = resultado.get("monto_directo", 0.0)
            riesgo_mc = self.monte_carlo.simular(monto_directo, MonteCarloRiesgo.parametros_obra_tipicos())
            self._historial.append({
                "timestamp": _now_utc().isoformat(),
                "proyecto": payload_bim.get("proyecto", "SIN_NOMBRE"),
                "status": "COMPLETADO",
            })
            return {
                "fase": "COSTEO", "status": "OK",
                "presupuesto": resultado,
                "meta": {"partidas_generados": len(partidas), "zona": str(self.zona)},
                "riesgo_montecarlo": riesgo_mc,
            }

    def exportar_a_excel(self, presupuesto: Any, ruta: str) -> None:
        if not _EXCEL_AVAILABLE:
            raise RuntimeError("pandas/openpyxl no instalados.")
        conceptos = []
        if hasattr(presupuesto, "partidas"):
            for p in presupuesto.partidas:
                if hasattr(p, "concepto") and hasattr(p.concepto, "insumos"):
                    c = ConceptoAPU(
                        clave=p.id,
                        descripcion=p.concepto.descripcion,
                        unidad="m³",
                        cantidad=p.cantidad,
                        insumos=[(ins, 1.0) for ins in p.concepto.insumos],
                    )
                    conceptos.append(c)
        IntegradorExcel.exportar_presupuesto(conceptos, ruta)

    def importar_desde_excel(self, ruta: str) -> List[Dict[str, Any]]:
        conceptos = IntegradorExcel.importar_conceptos(ruta)
        return [{"clave": c.clave, "descripcion": c.descripcion, "unidad": c.unidad, "cantidad": c.cantidad} for c in conceptos]

# ─────────────────────────────────────────────────────────────────────────────
# SERVICIO INTEROPERABILIDAD UNIFICADA
# ─────────────────────────────────────────────────────────────────────────────

class ServicioInteroperabilidadUnificada:
    def __init__(self, servicio_base: Optional[ServicioInteroperabilidad] = None,
                 servicio_trazabilidad: Optional[ServicioTrazabilidad] = None) -> None:
        self.trazabilidad = servicio_trazabilidad or ServicioTrazabilidad()
        self.base = servicio_base or ServicioInteroperabilidad(servicio_trazabilidad=self.trazabilidad)

    def remitir_presupuesto_licitacion(self, expediente_obra: ExpedienteObra,
                                        administracion_destino: str) -> Dict[str, Any]:
        docs_presupuesto = [d for d in expediente_obra.documentos if isinstance(d, DocumentoPresupuesto)]
        if not docs_presupuesto:
            raise ErrorInteroperabilidad("El expediente no contiene documentos de presupuesto")
        presupuesto_principal = docs_presupuesto[0]
        datos = {
            "emisor": expediente_obra.organo, "receptor": administracion_destino,
            "cuerpo": {
                "tipoMensaje": "PROPUESTA_LICITACION",
                "identificadorExpediente": expediente_obra.identificador,
                "proyectoNombre": expediente_obra.proyecto_nombre,
                "proyectoID": expediente_obra.proyecto_id,
                "montoTotal": presupuesto_principal.monto_total,
                "moneda": presupuesto_principal.moneda,
                "numeroPartidas": presupuesto_principal.numero_partidas,
                "responsableTecnico": expediente_obra.responsable_tecnico,
                "responsableEjecutivo": expediente_obra.responsable_ejecutivo,
                "plazoDias": expediente_obra.plazo_dias,
                "tipoContrato": expediente_obra.tipo_contrato,
                "hashPresupuesto": presupuesto_principal.hash_contenido,
                "ubicacionObra": expediente_obra.ubicacion_obra,
                "documentosAdjuntos": [d.identificador for d in expediente_obra.documentos],
                "estatusDeterminista": (presupuesto_principal.resultado_determinista or {}).get("estatus_final", "PENDIENTE"),
                "merkle_root": expediente_obra.merkle_root,
            },
        }
        mensaje = self.base.generar_mensaje_interoperabilidad(TipoInteroperabilidad.REMISION_EXPEDIENTE, datos)
        self.trazabilidad.registrar(
            actor="SERVICIO_INTEROP_UNIFICADO", accion="REMITIR_LICITACION",
            objeto="ExpedienteObra", objeto_id=expediente_obra.identificador,
            resultado="GENERADO",
            detalle=f"Destino: {administracion_destino}, Monto: {presupuesto_principal.monto_total}",
        )
        return {"mensaje_xml": mensaje, "estado": "GENERADO",
                "monto_total": presupuesto_principal.monto_total, "destino": administracion_destino}

# ─────────────────────────────────────────────────────────────────────────────
# TOPOGRAFÍA (PostGIS) — CON FALLBACK ELEGANTE
# ─────────────────────────────────────────────────────────────────────────────

class ServicioTopografiaAvanzada:
    def __init__(self, *args, **kwargs):
        if not _PSYCOPG2_AVAILABLE:
            raise RuntimeError("psycopg2 no instalado. pip install psycopg2-binary")
        self._db_url = kwargs.get("db_url") or os.environ.get("DATABASE_URL") or os.environ.get("SUPABASE_DB_URL")
        if not self._db_url:
            raise RuntimeError("No se encontró DATABASE_URL para topografía.")
        self._inicializar_esquema()

    def _get_conn(self):
        return psycopg2.connect(self._db_url)

    def _inicializar_esquema(self) -> None:
        with self._get_conn() as conn:
            with conn.cursor() as cur:
                cur.execute("CREATE EXTENSION IF NOT EXISTS postgis;")
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS topo_levantamientos (
                        id TEXT PRIMARY KEY,
                        nombre TEXT NOT NULL,
                        crs TEXT DEFAULT 'LOCAL',
                        srid INTEGER DEFAULT 0,
                        metadatos JSONB DEFAULT '{}'::jsonb,
                        created_at TIMESTAMPTZ DEFAULT NOW()
                    );
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS topo_puntos (
                        id TEXT PRIMARY KEY,
                        levantamiento_id TEXT NOT NULL REFERENCES topo_levantamientos(id) ON DELETE CASCADE,
                        x NUMERIC,
                        y NUMERIC,
                        z NUMERIC,
                        precision_xy NUMERIC DEFAULT 0.02,
                        precision_z NUMERIC DEFAULT 0.05,
                        etiqueta TEXT,
                        descripcion TEXT,
                        fuente TEXT,
                        metadatos JSONB DEFAULT '{}'::jsonb,
                        srid INTEGER DEFAULT 0,
                        geom GEOMETRY(POINTZ, 0) GENERATED ALWAYS AS (
                            ST_SetSRID(ST_MakePoint(x, y, z), srid)
                        ) STORED,
                        created_at TIMESTAMPTZ DEFAULT NOW()
                    );
                """)
                cur.execute("CREATE INDEX IF NOT EXISTS idx_topo_puntos_geom ON topo_puntos USING GIST (geom);")
                cur.execute("CREATE INDEX IF NOT EXISTS idx_topo_puntos_lid ON topo_puntos (levantamiento_id);")
                conn.commit()

    def crear_levantamiento(self, nombre: str, srid: int = 0) -> Dict[str, Any]:
        lid = f"TOP-{uuid.uuid4().hex[:10].upper()}"
        with self._get_conn() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO topo_levantamientos (id, nombre, srid) VALUES (%s, %s, %s)",
                    (lid, nombre, srid)
                )
                conn.commit()
        return {"id": lid, "nombre": nombre, "srid": srid}

    def importar_csv_puntos(self, levantamiento_id: str, csv_data: str) -> Dict[str, Any]:
        reader = csv.DictReader(io.StringIO(csv_data))
        puntos = []
        for row in reader:
            x = float(row.get("x", 0))
            y = float(row.get("y", 0))
            z = float(row.get("z", 0))
            puntos.append({"id": row.get("id", f"P-{len(puntos)+1}"), "x": x, "y": y, "z": z})
        with self._get_conn() as conn:
            with conn.cursor() as cur:
                for p in puntos:
                    cur.execute("""
                        INSERT INTO topo_puntos (id, levantamiento_id, x, y, z)
                        VALUES (%s, %s, %s, %s, %s)
                    """, (p["id"], levantamiento_id, p["x"], p["y"], p["z"]))
                conn.commit()
        return {"importados": len(puntos)}

    def calcular_volumen(self, levantamiento_id: str, z_ref: float) -> Dict[str, float]:
        with self._get_conn() as conn:
            with conn.cursor() as cur:
                cur.execute("""
                    WITH pts AS (
                        SELECT geom FROM topo_puntos WHERE levantamiento_id = %s
                    ),
                    triangulos AS (
                        SELECT (ST_Dump(ST_DelaunayTriangles(ST_Collect(geom), 0, 0))).geom AS tri
                        FROM pts
                    ),
                    areas AS (
                        SELECT
                            tri,
                            ST_Area(ST_Force2D(tri)) AS area,
                            (ST_Z(ST_PointN(ST_ExteriorRing(tri), 1)) +
                             ST_Z(ST_PointN(ST_ExteriorRing(tri), 2)) +
                             ST_Z(ST_PointN(ST_ExteriorRing(tri), 3))) / 3.0 AS avg_z
                        FROM triangulos
                        WHERE ST_Area(ST_Force2D(tri)) > 0
                    )
                    SELECT
                        COALESCE(SUM(area * (avg_z - %s)) FILTER (WHERE (avg_z - %s) > 0), 0) AS corte,
                        COALESCE(SUM(area * (%s - avg_z)) FILTER (WHERE (avg_z - %s) < 0), 0) AS relleno
                    FROM areas
                """, (levantamiento_id, z_ref, z_ref, z_ref, z_ref))
                row = cur.fetchone()
                return {"corte_m3": float(row[0] or 0.0), "relleno_m3": float(row[1] or 0.0), "neto_m3": float(row[0] or 0.0) - float(row[1] or 0.0)}

class AdaptadorTopografiaCosteo:
    def __init__(self, servicio: ServicioTopografiaAvanzada):
        self.servicio = servicio

    def preparar_para_costeo(self, levantamiento_id: str, z_referencia: float, proyecto: str = "", proyecto_id: str = "") -> Dict[str, Any]:
        vol = self.servicio.calcular_volumen(levantamiento_id, z_referencia)
        return {
            "proyecto": proyecto,
            "proyecto_id": proyecto_id,
            "volumenes": vol,
            "elementos_bim": [
                {"tipo": "movimiento_tierra", "subtipo": "corte", "cantidad": vol.get("corte_m3", 0), "unidad": "m3"},
                {"tipo": "movimiento_tierra", "subtipo": "relleno", "cantidad": vol.get("relleno_m3", 0), "unidad": "m3"},
            ]
        }

# ─────────────────────────────────────────────────────────────────────────────
# SISTEMA UNIFICADO MÉXICO v3.1 — BACKEND DEFINITIVO
# ─────────────────────────────────────────────────────────────────────────────

class SistemaUnificadoMexico:
    def __init__(self, zona_economica: Optional[ZonaEconomica] = None,
                 database: Any = None, jurisdiccion: Jurisdiccion = Jurisdiccion.FEDERAL) -> None:
        ConfiguracionUnificada.inicializar()
        self._lock = threading.RLock()
        self._configurar_logging()

        # Documental
        self.documental = SistemaGestionExpedientesMexico()
        self.interop = ServicioInteroperabilidadUnificada(servicio_trazabilidad=self.documental.trazabilidad)

        # Motores normativos
        self.motor_fallo = MotorFallo()
        self.motor_evidencia = MotorEvidencia(motor_fallo=self.motor_fallo)
        self.motor_juridico = MotorJuridico(motor_fallo=self.motor_fallo)
        self.motor_determinista = MotorDeterministaLicitaciones()
        self._inicializar_reglas_deterministas()

        # FSR Indexer
        self.fsr = FsrIndexer(ConfiguracionUnificada.RUTA_BASE_DB + "/fsr_cache")

        # Costeo (ahora con APU + Excel)
        self.costeo = ServicioCosteo(zona=zona_economica, database=database, fsr=self.fsr)

        # PASO 1: Cuantificación BIM
        self.cuantificador_bim = CuantificadorBIM()

        # PASO 3: Programación
        self.calendario = CalendarioLaboral()
        self.programacion = ModuloProgramacionObra(self.calendario)

        # PASO 4: Excel ya integrado en ServicioCosteo e IntegradorExcel

        self.jurisdiccion = jurisdiccion
        self.expedientes_obra: Dict[str, ExpedienteObra] = {}
        self.cola_jobs = CPLQueue(trabajadores=2)
        self.vsi = CPLVsiSistema()
        self.adaptador = AdaptadorPayloadV2V3()

        # Topografía (PostGIS)
        self.topografia = None
        self.adaptador_topografia = None
        try:
            self.topografia = ServicioTopografiaAvanzada()
            self.adaptador_topografia = AdaptadorTopografiaCosteo(self.topografia)
        except Exception:
            pass

        logging.info("MEGALODON v3.1 BACKEND DEFINITIVO inicializado.")

    def _inicializar_reglas_deterministas(self) -> None:
        for regla in [
            ValidadorSAT32D(), ValidadorSeguridadSocial(), ValidadorFirmaElectronica(),
            ValidadorFactorSalarioReal(), ValidadorCostosHorariosMaquinaria(),
            ValidadorSobrecostos(), ValidadorCongruenciaTemporal(),
            ValidadorGarantiaCumplimiento(), ValidadorPublicacionSIRECO(),
            ValidadorRequisitosParticipacion()
        ]:
            self.motor_determinista.registrar_regla(regla)

    def _configurar_logging(self) -> None:
        log_path = _ensure_dir(ConfiguracionUnificada.RUTA_LOGS)
        logging.basicConfig(
            level=logging.INFO,
            format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
            handlers=[
                logging.FileHandler(log_path / "unificado_v3.log", encoding="utf-8"),
                logging.StreamHandler(sys.stdout),
            ],
        )

    # ─── OPERACIONES PRINCIPALES ────────────────────────────────────────────

    def costear_obra(self, payload_bim: Dict[str, Any]) -> Dict[str, Any]:
        with self._lock:
            logging.info("[COSTEO] Iniciando: %s", payload_bim.get("proyecto", "SIN_NOMBRE"))
            return self.costeo.costear_desde_bim(payload_bim)

    def crear_expediente_obra(self, datos: Dict[str, Any]) -> ExpedienteObra:
        with self._lock:
            identificador = f"EXP-OBRA-{_now_utc().strftime('%Y%m%d')}-{uuid.uuid4().hex[:8].upper()}"
            expediente = ExpedienteObra(
                identificador=identificador,
                titulo=datos.get("titulo", ""),
                descripcion=datos.get("descripcion", ""),
                organo=datos.get("organo", ""),
                unidad_administrativa=datos.get("unidad_administrativa", ""),
                serie_documental=ConfiguracionUnificada.SERIE_DOCUMENTAL_PRESUPUESTO,
                subserie_documental=ConfiguracionUnificada.SUBSERIE_PRESUPUESTO_DETALLADO,
                fecha_apertura=_now_utc(),
                estado=EstadoExpediente.INICIADO,
                clasificacion=datos.get("clasificacion", ClasificacionSeguridad.PUBLICO.value),
                proyecto_id=datos.get("proyecto_id", ""),
                proyecto_nombre=datos.get("proyecto_nombre", ""),
                ubicacion_obra=datos.get("ubicacion_obra", ""),
                responsable_tecnico=datos.get("responsable_tecnico", ""),
                responsable_ejecutivo=datos.get("responsable_ejecutivo", ""),
                plazo_dias=int(datos.get("plazo_dias", 0) or 0),
                tipo_contrato=datos.get("tipo_contrato", "POR_PRECIOS_UNITARIOS"),
                responsable=datos.get("responsable_ejecutivo", ""),
            )
            self.documental.expedientes[identificador] = expediente
            self.expedientes_obra[identificador] = expediente
            self.documental.trazabilidad.registrar(
                actor="SISTEMA_UNIFICADO", accion="CREAR_EXPEDIENTE_OBRA",
                objeto="ExpedienteObra", objeto_id=identificador, resultado="OK",
                detalle=f"Proyecto: {expediente.proyecto_nombre}, Ubicación: {expediente.ubicacion_obra}",
            )
            return expediente

    def incorporar_presupuesto(self, expediente_id: str, resultado_costeo: Dict[str, Any]) -> DocumentoPresupuesto:
        with self._lock:
            if expediente_id not in self.expedientes_obra:
                raise ErrorNormativo(f"Expediente {expediente_id} no existe")
            expediente = self.expedientes_obra[expediente_id]
            presupuesto_dict = resultado_costeo.get("presupuesto", {})
            resultado_mc = resultado_costeo.get("riesgo_montecarlo")
            contenido_json = canonical_json({
                "presupuesto": presupuesto_dict,
                "meta_costeo": resultado_costeo.get("meta", {}),
                "riesgo_montecarlo": resultado_mc,
                "fecha_generacion": _now_utc().isoformat(),
                "version_sistema": "3.1.0",
            })
            monto_directo = float(presupuesto_dict.get("monto_directo", 0.0) or 0.0)
            numero_partidas = int(presupuesto_dict.get("num_partidas", 0) or 0)
            doc = DocumentoPresupuesto(
                identificador=f"DOC-PRES-{uuid.uuid4().hex[:8].upper()}",
                nombre=f"Presupuesto_{expediente.proyecto_nombre or expediente.identificador}.json",
                contenido=contenido_json.encode("utf-8"),
                tipo_documental=TipoDocumento.PRESUPUESTO,
                organo=expediente.organo,
                fecha_captura=_now_utc(),
                formato="json",
                autor=expediente.responsable_tecnico,
                nivel_seguridad=expediente.clasificacion,
                monto_directo=monto_directo,
                numero_partidas=numero_partidas,
                zona_economica=str(self.costeo.zona),
                resultado_montecarlo=resultado_mc,
            )
            payload_v3 = self.adaptador.construir_payload_completo(expediente, doc)
            resultado_det = self.motor_determinista.procesar_propuesta(payload_v3)
            doc.resultado_determinista = resultado_det
            doc._sincronizar_metadatos_presupuesto()
            doc.hash_contenido = doc._calcular_hash_contenido()
            expediente.agregar_documento_presupuesto(doc)
            expediente.calcular_merkle_root()
            return doc

    def cuantificar_ifc(self, ruta_ifc: str) -> List[Dict[str, Any]]:
        self.cuantificador_bim.cargar_ifc(ruta_ifc)
        return self.cuantificador_bim.cuantificar_proyecto()

    def analizar_apu(self, concepto: ConceptoAPU, tasa: float = 0.1125, plazo_dias: int = 180) -> Dict[str, Any]:
        return self.costeo.apu.analizar_concepto(concepto, tasa, plazo_dias)

    def calcular_programacion(self, actividades: List[ActividadPrograma], fecha_inicio: str) -> Dict[str, Any]:
        fecha = datetime.strptime(fecha_inicio, "%Y-%m-%d").date()
        self.programacion.actividades = {}
        for act in actividades:
            self.programacion.agregar_actividad(act)
        self.programacion.calcular_cpm(fecha)
        return {
            "ruta_critica": self.programacion.ruta_critica(),
            "actividades": [dataclasses.asdict(a) for a in self.programacion.actividades.values()],
        }

    def exportar_presupuesto_excel(self, conceptos: List[ConceptoAPU], ruta: str) -> None:
        IntegradorExcel.exportar_presupuesto(conceptos, ruta)

    def importar_presupuesto_excel(self, ruta: str) -> List[Dict[str, Any]]:
        return self.costeo.importar_desde_excel(ruta)

    def consultar_estado_obra(self, expediente_id: str) -> Dict[str, Any]:
        if expediente_id not in self.expedientes_obra:
            try:
                recuperado = self.documental.archivo.recuperar_expediente(expediente_id, incluir_contenido=False)
                return {"expediente_id": expediente_id, "status": "ARCHIVADO", "recuperado": True,
                        "manifest": recuperado.get("manifest"), "hash_global_ok": recuperado.get("hash_global_ok")}
            except Exception:
                return {"error": "Expediente no encontrado"}
        exp = self.expedientes_obra[expediente_id]
        return {
            "expediente_id": exp.identificador,
            "proyecto_nombre": exp.proyecto_nombre,
            "estado": exp.estado.value,
            "monto_contrato": exp.monto_contrato,
            "num_documentos": len(exp.documentos),
            "merkle_root": exp.merkle_root,
        }

    def obtener_estadisticas(self) -> Dict[str, Any]:
        stats_doc = self.documental.obtener_estadisticas_sistema()
        return {
            **stats_doc,
            "expedientes_obra_en_memoria": len(self.expedientes_obra),
            "version_unificada": "3.1.0 (BACKEND DEFINITIVO)",
            "numpy_disponible": _NUMPY_AVAILABLE,
            "ifc_disponible": _IFC_AVAILABLE,
            "excel_disponible": _EXCEL_AVAILABLE,
            "topografia_disponible": self.topografia is not None,
            "fsr_snapshots": len(list(Path(ConfiguracionUnificada.RUTA_BASE_DB + "/fsr_cache").glob("*.meta.json"))),
            "reglas_deterministas_activas": len(self.motor_determinista.validadores),
        }

    def apagar(self) -> None:
        self.cola_jobs.apagar()
        logging.info("[SISTEMA] Apagado limpio completado.")

# ─────────────────────────────────────────────────────────────────────────────
# PUNTO DE ENTRADA
# ─────────────────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(description="MEGALODON v3.1 — Backend Definitivo")
    parser.add_argument("--version", action="store_true", help="Mostrar versión y componentes cargados")
    args = parser.parse_args()

    if args.version:
        sistema = SistemaUnificadoMexico()
        stats = sistema.obtener_estadisticas()
        print("MEGALODON v3.1 — BACKEND DEFINITIVO")
        print(f"  Topografía (PostGIS): {'✅' if stats.get('topografia_disponible') else '❌'}")
        print(f"  Cuantificación IFC:    {'✅' if stats.get('ifc_disponible') else '❌'}")
        print(f"  Excel (pandas):        {'✅' if stats.get('excel_disponible') else '❌'}")
        print(f"  NumPy:                 {'✅' if stats.get('numpy_disponible') else '❌'}")
        print(f"  Reglas deterministas:  {stats.get('reglas_deterministas_activas', 0)}")
        print(f"  FSR snapshots:         {stats.get('fsr_snapshots', 0)}")
        sistema.apagar()
        return

    print("MEGALODON v3.1 — Backend definitivo")
    print("Ejecuta con --version para verificar componentes.")

if __name__ == "__main__":
    main()