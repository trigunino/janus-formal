"""Measure transport factors for Janus Z2 cover projections."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np


REQUIRED_FALSE_FLAGS = [
    "compressed_planck_lcdm_used",
    "archived_z4_reuse_used",
    "observational_fit_used",
    "rho_eff_shortcut_used",
    "negative_thermodynamic_density_postulated",
    "full_no_fit_prediction_ready",
]


def _array(payload: dict, key: str) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.ndim != 1:
        raise ValueError(f"{key} must be a 1D array")
    if not np.all(np.isfinite(values)) or np.any(values <= 0.0):
        raise ValueError(f"{key} must be positive and finite")
    return values


def derive_measure_transport(payload: dict) -> dict:
    if payload.get("active_core") != "JanusZ2CoverMasterAction":
        raise ValueError("active_core must be JanusZ2CoverMasterAction")
    if payload.get("source") != "active_cover_metric_determinants":
        raise ValueError("source must be active_cover_metric_determinants")
    for flag in REQUIRED_FALSE_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"{flag} must be false")

    grid = _array(payload, "parameter_grid")
    sqrt_plus = _array(payload, "sqrt_abs_g_plus")
    sqrt_minus = _array(payload, "sqrt_abs_g_minus")
    jac_minus_to_plus = _array(payload, "tau_jacobian_abs_minus_to_plus")
    jac_plus_to_minus = _array(payload, "tau_jacobian_abs_plus_to_minus")
    for name, values in {
        "sqrt_abs_g_plus": sqrt_plus,
        "sqrt_abs_g_minus": sqrt_minus,
        "tau_jacobian_abs_minus_to_plus": jac_minus_to_plus,
        "tau_jacobian_abs_plus_to_minus": jac_plus_to_minus,
    }.items():
        if values.shape != grid.shape:
            raise ValueError(f"{name} must align with parameter_grid")

    b_minus_to_plus = jac_minus_to_plus * sqrt_minus / sqrt_plus
    b_plus_to_minus = jac_plus_to_minus * sqrt_plus / sqrt_minus
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "measure_transport_from_cover_determinants",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": grid.tolist(),
        "B_minus_to_plus": b_minus_to_plus.tolist(),
        "B_plus_to_minus": b_plus_to_minus.tolist(),
        "measure_transport_ready": True,
        "formula": {
            "B_minus_to_plus": "|J_tau(-,+)| sqrt|g_minus| / sqrt|g_plus|",
            "B_plus_to_minus": "|J_tau(+,-)| sqrt|g_plus| / sqrt|g_minus|",
        },
    }


def load_and_derive_measure_transport(path: Path) -> dict:
    return derive_measure_transport(json.loads(Path(path).read_text(encoding="utf-8")))
