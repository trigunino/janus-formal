"""Sigma source extraction from a master-action boundary variation."""

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
    "two_independent_actions_used",
    "full_no_fit_prediction_ready",
]


def _array(payload: dict, key: str) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.ndim != 1:
        raise ValueError(f"{key} must be one-dimensional")
    if not np.all(np.isfinite(values)):
        raise ValueError(f"{key} contains non-finite values")
    return values


def derive_sigma_source_from_alpha_h(payload: dict) -> dict:
    """Use T_Sigma^ab = -2 alpha_h^ab as the metric-variation source."""
    if payload.get("active_core") != "JanusZ2CoverMasterAction":
        raise ValueError("active_core must be JanusZ2CoverMasterAction")
    if payload.get("source") != "master_boundary_variation_alpha_h":
        raise ValueError("source must be master_boundary_variation_alpha_h")
    for flag in REQUIRED_FALSE_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"{flag} must be false")
    grid = _array(payload, "parameter_grid")
    alpha_tau = _array(payload, "alpha_h_tau")
    alpha_s = _array(payload, "alpha_h_s")
    orientation_plus = _array(payload, "sigma_orientation_plus")
    orientation_minus = _array(payload, "sigma_orientation_minus")
    for key, values in {
        "alpha_h_tau": alpha_tau,
        "alpha_h_s": alpha_s,
        "sigma_orientation_plus": orientation_plus,
        "sigma_orientation_minus": orientation_minus,
    }.items():
        if values.shape != grid.shape:
            raise ValueError(f"{key} must align with parameter_grid")
    if not np.all(np.isin(orientation_plus, [-1.0, 1.0])):
        raise ValueError("sigma_orientation_plus must contain only +/-1")
    if not np.all(np.isin(orientation_minus, [-1.0, 1.0])):
        raise ValueError("sigma_orientation_minus must contain only +/-1")

    surface_tau = -2.0 * alpha_tau
    surface_s = -2.0 * alpha_s
    return {
        "active_core": "JanusZ2CoverMasterAction",
        "source": "sigma_source_from_master_boundary_alpha_h",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "rho_eff_shortcut_used": False,
        "negative_thermodynamic_density_postulated": False,
        "two_independent_actions_used": False,
        "full_no_fit_prediction_ready": False,
        "parameter_grid": grid.tolist(),
        "J_Sigma_plus_tau": (orientation_plus * surface_tau).tolist(),
        "J_Sigma_plus_s": (orientation_plus * surface_s).tolist(),
        "J_Sigma_minus_tau": (orientation_minus * surface_tau).tolist(),
        "J_Sigma_minus_s": (orientation_minus * surface_s).tolist(),
        "surface_stress_tau": surface_tau.tolist(),
        "surface_stress_s": surface_s.tolist(),
        "sigma_source_ready": True,
        "formula": "J_Sigma^ab = orientation * T_Sigma^ab, T_Sigma^ab = -2 alpha_h^ab",
        "sigma_junction_derived": True,
        "bending_moment_alpha_K_carried_separately": True,
    }


def load_and_derive_sigma_source(path: Path) -> dict:
    return derive_sigma_source_from_alpha_h(json.loads(Path(path).read_text(encoding="utf-8")))
