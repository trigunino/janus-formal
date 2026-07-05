"""Validated active Z2/Sigma BAO input manifest loader."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

import numpy as np

from .z2_sigma_sound_ruler import evaluate_rd_z2sigma_mpc
from .z2_sigma_bao import dimensionless_sound_ruler

FORBIDDEN_PROVENANCE_TOKENS = ["demo", "lcdm", "planck", "z4", "holst_scan"]
REQUIRED_BAO_INPUT_PROVENANCE = [
    "H_Z2Sigma",
    "c_s_Z2Sigma",
    "z_d_Z2Sigma",
    "r_d_Z2Sigma",
]
REQUIRED_SCALE_FREE_BAO_INPUT_PROVENANCE = [
    "E_Z2Sigma",
    "c_s_over_c_Z2Sigma",
    "z_d_Z2Sigma",
    "rhat_d_Z2Sigma",
]
REQUIRED_SCALE_FREE_PRIMITIVE_PROVENANCE = [
    "E_Z2Sigma",
    "c_s_over_c_Z2Sigma",
    "Gamma_drag_over_H0_Z2Sigma",
    "omega_k_Z2Sigma",
]
REQUIRED_SCALE_FREE_BACKGROUND_PRIMITIVE_PROVENANCE = [
    "E_Z2Sigma",
    "omega_k_Z2Sigma",
]
REQUIRED_SCALE_FREE_PLASMA_PRIMITIVE_PROVENANCE = [
    "c_s_over_c_Z2Sigma",
    "Gamma_drag_over_H0_Z2Sigma",
]


@dataclass(frozen=True)
class ActiveZ2SigmaBAOInputs:
    z_grid: np.ndarray
    h_grid: np.ndarray
    cs_grid: np.ndarray
    z_d: float
    z_max: float
    omega_k_z2sigma: float = 0.0

    def h_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.h_grid)

    def cs_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.cs_grid)

    def rd_mpc(self) -> float:
        return evaluate_rd_z2sigma_mpc(
            self.h_z2sigma,
            self.cs_z2sigma,
            self.z_d,
            z_max=self.z_max,
            samples=min(max(len(self.z_grid), 64), 8192),
        )


@dataclass(frozen=True)
class ActiveZ2SigmaScaleFreeBAOInputs:
    z_grid: np.ndarray
    e_grid: np.ndarray
    cs_over_c_grid: np.ndarray
    z_d: float
    rd_hat_z2sigma: float
    z_max: float
    omega_k_z2sigma: float = 0.0
    gamma_drag_over_h0_grid: np.ndarray | None = None

    def e_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.e_grid)

    def cs_over_c_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.cs_over_c_grid)

    def rd_hat(self) -> float:
        return self.rd_hat_z2sigma


@dataclass(frozen=True)
class ActiveZ2SigmaScaleFreePrimitiveInputs:
    z_grid: np.ndarray
    e_grid: np.ndarray
    cs_over_c_grid: np.ndarray
    gamma_drag_over_h0_grid: np.ndarray
    omega_k_z2sigma: float
    z_max: float
    z_d_bracket: tuple[float, float] | None = None

    def e_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.e_grid)

    def cs_over_c_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.cs_over_c_grid)

    def gamma_drag_over_h0_z2sigma(self, z):
        return np.interp(
            np.asarray(z, dtype=float),
            self.z_grid,
            self.gamma_drag_over_h0_grid,
        )


@dataclass(frozen=True)
class ActiveZ2SigmaScaleFreeBackgroundPrimitiveInputs:
    z_grid: np.ndarray
    e_grid: np.ndarray
    omega_k_z2sigma: float
    z_max: float
    z_d_bracket: tuple[float, float] | None = None

    def e_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.e_grid)


@dataclass(frozen=True)
class ActiveZ2SigmaScaleFreePlasmaPrimitiveInputs:
    z_grid: np.ndarray
    cs_over_c_grid: np.ndarray
    gamma_drag_over_h0_grid: np.ndarray
    z_max: float
    z_d_bracket: tuple[float, float] | None = None

    def cs_over_c_z2sigma(self, z):
        return np.interp(np.asarray(z, dtype=float), self.z_grid, self.cs_over_c_grid)

    def gamma_drag_over_h0_z2sigma(self, z):
        return np.interp(
            np.asarray(z, dtype=float),
            self.z_grid,
            self.gamma_drag_over_h0_grid,
        )


def write_active_z2sigma_bao_manifest(
    path: Path,
    z_grid,
    h_z2sigma,
    cs_z2sigma,
    z_d_z2sigma: float,
    z_max: float,
    omega_k_z2sigma: float = 0.0,
    input_provenance: dict[str, str] | None = None,
    source_component_manifest_sha256: str | None = None,
    source_component_manifest_path: str | None = None,
) -> Path:
    """Write the only accepted manifest shape for official ActiveZ2Sigma BAO."""

    provenance = _validate_input_provenance(input_provenance or {})
    source_hash = _validate_source_component_manifest_hash(source_component_manifest_sha256)
    source_path = _validate_source_component_manifest_path(source_component_manifest_path)
    z_values = np.asarray(z_grid, dtype=float)
    h_values = np.asarray(h_z2sigma(z_values), dtype=float)
    cs_values = np.asarray(cs_z2sigma(z_values), dtype=float)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": z_values.tolist(),
        "H_Z2Sigma_km_s_Mpc": h_values.tolist(),
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "c_s_Z2Sigma_km_s": cs_values.tolist(),
        "z_d_Z2Sigma": float(z_d_z2sigma),
        "z_max": float(z_max),
        "input_provenance": provenance,
        "source_component_manifest_path": source_path,
        "source_component_manifest_sha256": source_hash,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_bao_inputs(destination)
    return destination


def write_active_z2sigma_scale_free_bao_manifest(
    path: Path,
    z_grid,
    e_z2sigma,
    cs_over_c_z2sigma,
    z_d_z2sigma: float,
    z_max: float,
    omega_k_z2sigma: float = 0.0,
    gamma_drag_over_h0_z2sigma=None,
    input_provenance: dict[str, str] | None = None,
    source_component_manifest_sha256: str | None = None,
    source_component_manifest_path: str | None = None,
) -> Path:
    """Write a strict scale-free ActiveZ2Sigma BAO manifest."""

    provenance = _validate_scale_free_input_provenance(input_provenance or {})
    source_hash = _validate_source_component_manifest_hash(source_component_manifest_sha256)
    source_path = _validate_source_component_manifest_path(source_component_manifest_path)
    z_values = np.asarray(z_grid, dtype=float)
    e_values = np.asarray(e_z2sigma(z_values), dtype=float)
    cs_values = np.asarray(cs_over_c_z2sigma(z_values), dtype=float)
    gamma_over_h0_values = None
    if gamma_drag_over_h0_z2sigma is not None:
        gamma_over_h0_values = np.asarray(gamma_drag_over_h0_z2sigma(z_values), dtype=float)
        if gamma_over_h0_values.shape != z_values.shape:
            raise ValueError("Gamma_drag/H0 must be aligned with z_grid")
        if np.any(gamma_over_h0_values <= 0.0):
            raise ValueError("Gamma_drag/H0 values must be positive")
    rd_hat = dimensionless_sound_ruler(
        lambda zz: np.interp(np.asarray(zz, dtype=float), z_values, e_values),
        lambda zz: np.interp(np.asarray(zz, dtype=float), z_values, cs_values),
        z_d_z2sigma,
        z_max=z_max,
        samples=min(max(len(z_values), 64), 8192),
    )
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "manifest_kind": "scale_free_bao_inputs",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z_values.tolist(),
        "E_Z2Sigma": e_values.tolist(),
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "c_s_over_c_Z2Sigma": cs_values.tolist(),
        "Gamma_drag_over_H0_Z2Sigma": (
            None if gamma_over_h0_values is None else gamma_over_h0_values.tolist()
        ),
        "z_d_Z2Sigma": float(z_d_z2sigma),
        "rhat_d_Z2Sigma": float(rd_hat),
        "z_max": float(z_max),
        "input_provenance": provenance,
        "source_component_manifest_path": source_path,
        "source_component_manifest_sha256": source_hash,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_scale_free_bao_inputs(destination)
    return destination


def write_active_z2sigma_scale_free_primitive_manifest(
    path: Path,
    z_grid,
    e_z2sigma,
    cs_over_c_z2sigma,
    gamma_drag_over_h0_z2sigma,
    omega_k_z2sigma: float,
    z_max: float,
    primitive_provenance: dict[str, str] | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> Path:
    """Write strict active dimensionless primitives for the scale-free BAO path."""

    provenance = _validate_scale_free_primitive_provenance(primitive_provenance or {})
    z_values = np.asarray(z_grid, dtype=float)
    e_values = np.asarray(e_z2sigma(z_values), dtype=float)
    cs_values = np.asarray(cs_over_c_z2sigma(z_values), dtype=float)
    gamma_values = np.asarray(gamma_drag_over_h0_z2sigma(z_values), dtype=float)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "manifest_kind": "scale_free_primitive_inputs",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z_values.tolist(),
        "E_Z2Sigma": e_values.tolist(),
        "c_s_over_c_Z2Sigma": cs_values.tolist(),
        "Gamma_drag_over_H0_Z2Sigma": gamma_values.tolist(),
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "z_max": float(z_max),
        "z_d_bracket": None if z_d_bracket is None else [float(v) for v in z_d_bracket],
        "primitive_provenance": provenance,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_scale_free_primitive_inputs(destination)
    return destination


def write_active_z2sigma_scale_free_background_primitive_manifest(
    path: Path,
    z_grid,
    e_z2sigma,
    omega_k_z2sigma: float,
    z_max: float,
    primitive_provenance: dict[str, str] | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> Path:
    provenance = _validate_scale_free_background_primitive_provenance(
        primitive_provenance or {}
    )
    z_values = np.asarray(z_grid, dtype=float)
    e_values = np.asarray(e_z2sigma(z_values), dtype=float)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "manifest_kind": "scale_free_background_primitive_inputs",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z_values.tolist(),
        "E_Z2Sigma": e_values.tolist(),
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "z_max": float(z_max),
        "z_d_bracket": None if z_d_bracket is None else [float(v) for v in z_d_bracket],
        "primitive_provenance": provenance,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_scale_free_background_primitive_inputs(destination)
    return destination


def write_active_z2sigma_scale_free_plasma_primitive_manifest(
    path: Path,
    z_grid,
    cs_over_c_z2sigma,
    gamma_drag_over_h0_z2sigma,
    z_max: float,
    primitive_provenance: dict[str, str] | None = None,
    z_d_bracket: list[float] | tuple[float, float] | None = None,
) -> Path:
    provenance = _validate_scale_free_plasma_primitive_provenance(
        primitive_provenance or {}
    )
    z_values = np.asarray(z_grid, dtype=float)
    cs_values = np.asarray(cs_over_c_z2sigma(z_values), dtype=float)
    gamma_values = np.asarray(gamma_drag_over_h0_z2sigma(z_values), dtype=float)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "manifest_kind": "scale_free_plasma_primitive_inputs",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z_values.tolist(),
        "c_s_over_c_Z2Sigma": cs_values.tolist(),
        "Gamma_drag_over_H0_Z2Sigma": gamma_values.tolist(),
        "z_max": float(z_max),
        "z_d_bracket": None if z_d_bracket is None else [float(v) for v in z_d_bracket],
        "primitive_provenance": provenance,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_scale_free_plasma_primitive_inputs(destination)
    return destination


def _validate_input_provenance(provenance: dict[str, str]) -> dict[str, str]:
    return _validate_required_input_provenance(provenance, REQUIRED_BAO_INPUT_PROVENANCE)


def _validate_scale_free_input_provenance(provenance: dict[str, str]) -> dict[str, str]:
    return _validate_required_input_provenance(provenance, REQUIRED_SCALE_FREE_BAO_INPUT_PROVENANCE)


def _validate_scale_free_primitive_provenance(provenance: dict[str, str]) -> dict[str, str]:
    return _validate_required_input_provenance(provenance, REQUIRED_SCALE_FREE_PRIMITIVE_PROVENANCE)


def _validate_scale_free_background_primitive_provenance(provenance: dict[str, str]) -> dict[str, str]:
    return _validate_required_input_provenance(
        provenance,
        REQUIRED_SCALE_FREE_BACKGROUND_PRIMITIVE_PROVENANCE,
    )


def _validate_scale_free_plasma_primitive_provenance(provenance: dict[str, str]) -> dict[str, str]:
    return _validate_required_input_provenance(
        provenance,
        REQUIRED_SCALE_FREE_PLASMA_PRIMITIVE_PROVENANCE,
    )


def _validate_required_input_provenance(
    provenance: dict[str, str],
    required_fields: list[str],
) -> dict[str, str]:
    cleaned: dict[str, str] = {}
    for field in required_fields:
        source = str(provenance.get(field, "")).strip()
        if not source:
            raise ValueError(f"Missing BAO input provenance for {field}")
        lowered = source.lower()
        if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
            raise ValueError(f"Forbidden BAO input provenance for {field}: {source}")
        cleaned[field] = source
    return cleaned


def _validate_source_component_manifest_hash(value: str | None) -> str:
    source_hash = str(value or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", source_hash):
        raise ValueError("source_component_manifest_sha256 must be a 64-character lowercase hex digest")
    return source_hash


def _validate_source_component_manifest_path(value: str | None) -> str:
    source_path = str(value or "").strip()
    if not source_path:
        raise ValueError("source_component_manifest_path is required")
    lowered = source_path.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden source_component_manifest_path: {source_path}")
    return source_path


def load_active_z2sigma_bao_inputs(path: Path) -> ActiveZ2SigmaBAOInputs:
    """Load active BAO inputs and reject forbidden provenance."""

    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    _validate_input_provenance(payload.get("input_provenance", {}))
    _validate_source_component_manifest_path(payload.get("source_component_manifest_path"))
    _validate_source_component_manifest_hash(payload.get("source_component_manifest_sha256"))

    z_grid = np.asarray(payload["z_grid"], dtype=float)
    h_grid = np.asarray(payload["H_Z2Sigma_km_s_Mpc"], dtype=float)
    cs_grid = np.asarray(payload["c_s_Z2Sigma_km_s"], dtype=float)
    if z_grid.ndim != 1 or h_grid.shape != z_grid.shape or cs_grid.shape != z_grid.shape:
        raise ValueError("z_grid, H_Z2Sigma and c_s_Z2Sigma must be one-dimensional and aligned")
    if np.any(np.diff(z_grid) <= 0):
        raise ValueError("z_grid must be strictly increasing")
    if np.any(h_grid <= 0) or np.any(cs_grid <= 0):
        raise ValueError("H_Z2Sigma and c_s_Z2Sigma values must be positive")

    z_d = float(payload["z_d_Z2Sigma"])
    z_max = float(payload.get("z_max", z_grid[-1]))
    omega_k_z2sigma = float(payload.get("omega_k_Z2Sigma", 0.0))
    if z_d < z_grid[0] or z_d >= z_max or z_max > z_grid[-1]:
        raise ValueError("Require z_grid[0] <= z_d < z_max <= z_grid[-1]")

    return ActiveZ2SigmaBAOInputs(
        z_grid=z_grid,
        h_grid=h_grid,
        cs_grid=cs_grid,
        z_d=z_d,
        z_max=z_max,
        omega_k_z2sigma=omega_k_z2sigma,
    )


def load_active_z2sigma_scale_free_primitive_inputs(
    path: Path,
) -> ActiveZ2SigmaScaleFreePrimitiveInputs:
    """Load strict active scale-free primitive inputs."""

    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    if payload.get("manifest_kind") != "scale_free_primitive_inputs":
        raise ValueError("Manifest kind must be scale_free_primitive_inputs")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    _validate_scale_free_primitive_provenance(payload.get("primitive_provenance", {}))

    z_grid = np.asarray(payload["z_grid"], dtype=float)
    e_grid = np.asarray(payload["E_Z2Sigma"], dtype=float)
    cs_grid = np.asarray(payload["c_s_over_c_Z2Sigma"], dtype=float)
    gamma_grid = np.asarray(payload["Gamma_drag_over_H0_Z2Sigma"], dtype=float)
    if (
        z_grid.ndim != 1
        or e_grid.shape != z_grid.shape
        or cs_grid.shape != z_grid.shape
        or gamma_grid.shape != z_grid.shape
    ):
        raise ValueError("Scale-free primitive grids must be one-dimensional and aligned")
    if np.any(np.diff(z_grid) <= 0):
        raise ValueError("z_grid must be strictly increasing")
    if np.any(e_grid <= 0) or np.any(cs_grid <= 0) or np.any(gamma_grid <= 0):
        raise ValueError("Scale-free primitive values must be positive")
    z_max = float(payload.get("z_max", z_grid[-1]))
    if z_max <= z_grid[0] or z_max > z_grid[-1]:
        raise ValueError("Require z_grid[0] < z_max <= z_grid[-1]")
    raw_z_d_bracket = payload.get("z_d_bracket")
    z_d_bracket = None
    if raw_z_d_bracket is not None:
        if not isinstance(raw_z_d_bracket, list) or len(raw_z_d_bracket) != 2:
            raise ValueError("z_d_bracket must be null or a two-element list")
        z_low, z_high = [float(value) for value in raw_z_d_bracket]
        if not (z_grid[0] <= z_low < z_high <= z_max):
            raise ValueError("z_d_bracket must lie inside the primitive z range")
        z_d_bracket = (z_low, z_high)

    return ActiveZ2SigmaScaleFreePrimitiveInputs(
        z_grid=z_grid,
        e_grid=e_grid,
        cs_over_c_grid=cs_grid,
        gamma_drag_over_h0_grid=gamma_grid,
        omega_k_z2sigma=float(payload["omega_k_Z2Sigma"]),
        z_max=z_max,
        z_d_bracket=z_d_bracket,
    )


def _validate_scale_free_z_grid_and_bracket(payload: dict) -> tuple[np.ndarray, float, tuple[float, float] | None]:
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    if z_grid.ndim != 1 or np.any(np.diff(z_grid) <= 0):
        raise ValueError("z_grid must be one-dimensional and strictly increasing")
    z_max = float(payload.get("z_max", z_grid[-1]))
    if z_max <= z_grid[0] or z_max > z_grid[-1]:
        raise ValueError("Require z_grid[0] < z_max <= z_grid[-1]")
    raw_z_d_bracket = payload.get("z_d_bracket")
    z_d_bracket = None
    if raw_z_d_bracket is not None:
        if not isinstance(raw_z_d_bracket, list) or len(raw_z_d_bracket) != 2:
            raise ValueError("z_d_bracket must be null or a two-element list")
        z_low, z_high = [float(value) for value in raw_z_d_bracket]
        if not (z_grid[0] <= z_low < z_high <= z_max):
            raise ValueError("z_d_bracket must lie inside the primitive z range")
        z_d_bracket = (z_low, z_high)
    return z_grid, z_max, z_d_bracket


def _validate_scale_free_split_header(payload: dict, manifest_kind: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    if payload.get("manifest_kind") != manifest_kind:
        raise ValueError(f"Manifest kind must be {manifest_kind}")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def load_active_z2sigma_scale_free_background_primitive_inputs(
    path: Path,
) -> ActiveZ2SigmaScaleFreeBackgroundPrimitiveInputs:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    _validate_scale_free_split_header(payload, "scale_free_background_primitive_inputs")
    _validate_scale_free_background_primitive_provenance(
        payload.get("primitive_provenance", {})
    )
    z_grid, z_max, z_d_bracket = _validate_scale_free_z_grid_and_bracket(payload)
    e_grid = np.asarray(payload["E_Z2Sigma"], dtype=float)
    if e_grid.shape != z_grid.shape or np.any(e_grid <= 0):
        raise ValueError("E_Z2Sigma must be positive and aligned with z_grid")
    return ActiveZ2SigmaScaleFreeBackgroundPrimitiveInputs(
        z_grid=z_grid,
        e_grid=e_grid,
        omega_k_z2sigma=float(payload["omega_k_Z2Sigma"]),
        z_max=z_max,
        z_d_bracket=z_d_bracket,
    )


def load_active_z2sigma_scale_free_plasma_primitive_inputs(
    path: Path,
) -> ActiveZ2SigmaScaleFreePlasmaPrimitiveInputs:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    _validate_scale_free_split_header(payload, "scale_free_plasma_primitive_inputs")
    _validate_scale_free_plasma_primitive_provenance(
        payload.get("primitive_provenance", {})
    )
    z_grid, z_max, z_d_bracket = _validate_scale_free_z_grid_and_bracket(payload)
    cs_grid = np.asarray(payload["c_s_over_c_Z2Sigma"], dtype=float)
    gamma_grid = np.asarray(payload["Gamma_drag_over_H0_Z2Sigma"], dtype=float)
    if cs_grid.shape != z_grid.shape or gamma_grid.shape != z_grid.shape:
        raise ValueError("Plasma primitive arrays must align with z_grid")
    if np.any(cs_grid <= 0) or np.any(gamma_grid <= 0):
        raise ValueError("Plasma primitive values must be positive")
    return ActiveZ2SigmaScaleFreePlasmaPrimitiveInputs(
        z_grid=z_grid,
        cs_over_c_grid=cs_grid,
        gamma_drag_over_h0_grid=gamma_grid,
        z_max=z_max,
        z_d_bracket=z_d_bracket,
    )


def load_active_z2sigma_scale_free_bao_inputs(path: Path) -> ActiveZ2SigmaScaleFreeBAOInputs:
    """Load strict scale-free active BAO inputs and reject forbidden provenance."""

    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    if payload.get("manifest_kind") != "scale_free_bao_inputs":
        raise ValueError("Manifest kind must be scale_free_bao_inputs")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    _validate_scale_free_input_provenance(payload.get("input_provenance", {}))
    _validate_source_component_manifest_path(payload.get("source_component_manifest_path"))
    _validate_source_component_manifest_hash(payload.get("source_component_manifest_sha256"))

    z_grid = np.asarray(payload["z_grid"], dtype=float)
    e_grid = np.asarray(payload["E_Z2Sigma"], dtype=float)
    cs_grid = np.asarray(payload["c_s_over_c_Z2Sigma"], dtype=float)
    gamma_grid = None
    if payload.get("Gamma_drag_over_H0_Z2Sigma") is not None:
        gamma_grid = np.asarray(payload["Gamma_drag_over_H0_Z2Sigma"], dtype=float)
        if gamma_grid.shape != z_grid.shape or np.any(gamma_grid <= 0):
            raise ValueError("Gamma_drag_over_H0_Z2Sigma must be positive and aligned")
    if z_grid.ndim != 1 or e_grid.shape != z_grid.shape or cs_grid.shape != z_grid.shape:
        raise ValueError("z_grid, E_Z2Sigma and c_s/c must be one-dimensional and aligned")
    if np.any(np.diff(z_grid) <= 0):
        raise ValueError("z_grid must be strictly increasing")
    if np.any(e_grid <= 0) or np.any(cs_grid <= 0):
        raise ValueError("E_Z2Sigma and c_s/c values must be positive")

    z_d = float(payload["z_d_Z2Sigma"])
    z_max = float(payload.get("z_max", z_grid[-1]))
    omega_k_z2sigma = float(payload.get("omega_k_Z2Sigma", 0.0))
    if z_d < z_grid[0] or z_d >= z_max or z_max > z_grid[-1]:
        raise ValueError("Require z_grid[0] <= z_d < z_max <= z_grid[-1]")
    rd_hat = float(payload["rhat_d_Z2Sigma"])
    if rd_hat <= 0.0:
        raise ValueError("rhat_d_Z2Sigma must be positive")
    computed_rd_hat = dimensionless_sound_ruler(
        lambda zz: np.interp(np.asarray(zz, dtype=float), z_grid, e_grid),
        lambda zz: np.interp(np.asarray(zz, dtype=float), z_grid, cs_grid),
        z_d,
        z_max=z_max,
        samples=min(max(len(z_grid), 64), 8192),
    )
    if not np.isclose(rd_hat, computed_rd_hat, rtol=1.0e-8, atol=1.0e-12):
        raise ValueError("rhat_d_Z2Sigma must match the scale-free sound-ruler integral")

    return ActiveZ2SigmaScaleFreeBAOInputs(
        z_grid=z_grid,
        e_grid=e_grid,
        cs_over_c_grid=cs_grid,
        z_d=z_d,
        rd_hat_z2sigma=rd_hat,
        z_max=z_max,
        omega_k_z2sigma=omega_k_z2sigma,
        gamma_drag_over_h0_grid=gamma_grid,
    )
