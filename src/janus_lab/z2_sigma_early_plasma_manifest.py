"""Active Z2/Sigma early-plasma component manifest helpers."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

import numpy as np


ArrayFn = Callable[[np.ndarray], np.ndarray]

EARLY_PLASMA_FIELDS = [
    "rho_baryon_Z2Sigma",
    "rho_photon_Z2Sigma",
    "Gamma_drag_Z2Sigma",
]
FORBIDDEN_PROVENANCE_TOKENS = ["demo", "lcdm", "planck", "z4", "holst_scan"]


@dataclass(frozen=True)
class Z2SigmaEarlyPlasmaComponentFunctions:
    rho_baryon_z2sigma: ArrayFn
    rho_photon_z2sigma: ArrayFn
    gamma_drag_z2sigma: ArrayFn


def _evaluate_on_grid(function: ArrayFn, z_grid: np.ndarray, name: str) -> list[float]:
    values = np.asarray(function(z_grid), dtype=float)
    if values.shape != z_grid.shape:
        raise ValueError(f"{name} must match z_grid shape")
    if np.any(values <= 0.0):
        raise ValueError(f"{name} values must be positive")
    return values.tolist()


def _validate_provenance(component_provenance: dict[str, str]) -> dict[str, str]:
    for field in EARLY_PLASMA_FIELDS:
        source = str(component_provenance.get(field, "")).lower()
        if not source:
            raise ValueError(f"Missing active provenance for {field}")
        if any(token in source for token in FORBIDDEN_PROVENANCE_TOKENS):
            raise ValueError(f"Forbidden provenance for {field}: {source}")
    return dict(component_provenance)


def load_active_z2sigma_early_plasma_manifest(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    if z_grid.ndim != 1 or np.any(z_grid < 0.0) or np.any(np.diff(z_grid) <= 0.0):
        raise ValueError("z_grid must be non-negative and strictly increasing")
    early = payload.get("early_plasma", {})
    for field in EARLY_PLASMA_FIELDS:
        values = np.asarray(early.get(field), dtype=float)
        if values.shape != z_grid.shape or np.any(values <= 0.0):
            raise ValueError(f"{field} must be positive and aligned with z_grid")
    _validate_provenance(payload.get("component_provenance", {}))
    return payload


def write_active_z2sigma_early_plasma_manifest(
    path: Path,
    z_grid,
    components: Z2SigmaEarlyPlasmaComponentFunctions,
    component_provenance: dict[str, str],
    *,
    z_d_bracket: tuple[float, float] | None = None,
) -> Path:
    z_values = np.asarray(z_grid, dtype=float)
    if z_values.ndim != 1 or np.any(z_values < 0.0) or np.any(np.diff(z_values) <= 0.0):
        raise ValueError("z_grid must be non-negative and strictly increasing")
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "z_grid": z_values.tolist(),
        "z_d_bracket": None if z_d_bracket is None else [float(z_d_bracket[0]), float(z_d_bracket[1])],
        "early_plasma": {
            "rho_baryon_Z2Sigma": _evaluate_on_grid(components.rho_baryon_z2sigma, z_values, "rho_baryon_Z2Sigma"),
            "rho_photon_Z2Sigma": _evaluate_on_grid(components.rho_photon_z2sigma, z_values, "rho_photon_Z2Sigma"),
            "Gamma_drag_Z2Sigma": _evaluate_on_grid(components.gamma_drag_z2sigma, z_values, "Gamma_drag_Z2Sigma"),
        },
        "component_provenance": _validate_provenance(component_provenance),
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_early_plasma_manifest(destination)
    return destination
