"""Effective scale-free BAO inputs for Janus Z2/Sigma.

This is not the strict active-derived path. It is the controlled effective
branch fed by explicitly declared initial data and effective primitives.
"""

from __future__ import annotations

import json
import math
import re
import hashlib
from dataclasses import dataclass
from pathlib import Path

import numpy as np

FORBIDDEN_TOKENS = ["planck", "lcdm", "z4", "fit", "bao_scan"]
REQUIRED_PRIMITIVE_PROVENANCE = [
    "E_Z2Sigma",
    "c_s_over_c_Z2Sigma",
    "Gamma_drag_over_H0_Z2Sigma",
    "omega_k_Z2Sigma",
]


@dataclass(frozen=True)
class EffectiveScaleFreePrimitiveInputs:
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


def _clean_provenance_map(provenance: dict) -> dict[str, str]:
    cleaned: dict[str, str] = {}
    for field in REQUIRED_PRIMITIVE_PROVENANCE:
        source = str(provenance.get(field, "")).strip()
        if not source:
            raise ValueError(f"Missing effective primitive provenance for {field}")
        lowered = source.lower()
        if any(token in lowered for token in FORBIDDEN_TOKENS):
            raise ValueError(f"Forbidden effective primitive provenance for {field}: {source}")
        cleaned[field] = source
    return cleaned


def _validate_hash(value: object) -> str:
    text = str(value or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", text):
        raise ValueError("source_effective_closure_sha256 must be a 64-character lowercase hex digest")
    return text


def load_effective_scale_free_primitive_inputs(path: Path) -> EffectiveScaleFreePrimitiveInputs:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "effective_primitives":
        raise ValueError("Manifest source must be effective_primitives")
    if payload.get("manifest_kind") != "effective_scale_free_primitive_inputs":
        raise ValueError("Manifest kind must be effective_scale_free_primitive_inputs")
    for key in [
        "compressed_planck_lcdm_used",
        "archived_z4_reuse_used",
        "observational_fit_used",
        "full_no_fit_prediction_ready",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden/false-required flag must be false: {key}")
    _clean_provenance_map(payload.get("primitive_provenance", {}))
    _validate_hash(payload.get("source_effective_closure_sha256"))
    source_path = str(payload.get("source_effective_closure_path", "")).strip()
    if not source_path:
        raise ValueError("source_effective_closure_path is required")

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
        raise ValueError("Effective primitive arrays must be one-dimensional and aligned")
    if np.any(np.diff(z_grid) <= 0.0):
        raise ValueError("z_grid must be strictly increasing")
    if np.any(e_grid <= 0.0) or np.any(cs_grid <= 0.0) or np.any(gamma_grid <= 0.0):
        raise ValueError("Effective primitive values must be positive")
    z_max = float(payload.get("z_max", z_grid[-1]))
    if not math.isfinite(z_max) or z_max <= z_grid[0] or z_max > z_grid[-1]:
        raise ValueError("Require z_grid[0] < z_max <= z_grid[-1]")
    bracket = None
    raw_bracket = payload.get("z_d_bracket")
    if raw_bracket is not None:
        if not isinstance(raw_bracket, list) or len(raw_bracket) != 2:
            raise ValueError("z_d_bracket must be null or a two-element list")
        lo, hi = [float(item) for item in raw_bracket]
        if not (z_grid[0] <= lo < hi <= z_max):
            raise ValueError("z_d_bracket must lie inside the primitive z range")
        bracket = (lo, hi)
    return EffectiveScaleFreePrimitiveInputs(
        z_grid=z_grid,
        e_grid=e_grid,
        cs_over_c_grid=cs_grid,
        gamma_drag_over_h0_grid=gamma_grid,
        omega_k_z2sigma=float(payload["omega_k_Z2Sigma"]),
        z_max=z_max,
        z_d_bracket=bracket,
    )


def write_effective_scale_free_primitive_inputs(
    path: Path,
    *,
    closure_path: Path,
    z_grid,
    e_z2sigma,
    cs_over_c_z2sigma,
    gamma_drag_over_h0_z2sigma,
    omega_k_z2sigma: float,
    primitive_provenance: dict[str, str],
    z_max: float | None = None,
    z_d_bracket: list[float] | None = None,
) -> Path:
    """Write canonical effective scale-free BAO primitives."""

    closure = Path(closure_path)
    if not closure.exists():
        raise ValueError("closure_path must exist before writing effective primitives")
    provenance = _clean_provenance_map(primitive_provenance)
    z_values = np.asarray(z_grid, dtype=float)
    e_values = np.asarray(e_z2sigma(z_values), dtype=float)
    cs_values = np.asarray(cs_over_c_z2sigma(z_values), dtype=float)
    gamma_values = np.asarray(gamma_drag_over_h0_z2sigma(z_values), dtype=float)
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "effective_primitives",
        "manifest_kind": "effective_scale_free_primitive_inputs",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "source_effective_closure_path": str(closure),
        "source_effective_closure_sha256": hashlib.sha256(closure.read_bytes()).hexdigest(),
        "z_grid": z_values.tolist(),
        "E_Z2Sigma": e_values.tolist(),
        "c_s_over_c_Z2Sigma": cs_values.tolist(),
        "Gamma_drag_over_H0_Z2Sigma": gamma_values.tolist(),
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "z_max": float(z_values[-1] if z_max is None else z_max),
        "z_d_bracket": z_d_bracket,
        "primitive_provenance": provenance,
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_effective_scale_free_primitive_inputs(destination)
    return destination
