"""Validated effective parameter-entry manifest for Janus Z2/Sigma BAO."""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np

from .z2_sigma_effective_bao import _clean_provenance_map
from .z2_sigma_effective_closure import validate_effective_closure_payload


def _array(payload: dict, key: str) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.ndim != 1 or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be a finite one-dimensional array")
    return values


def validate_effective_bao_parameter_inputs(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("parameter input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "effective_parameter_inputs":
        raise ValueError("parameter input source must be effective_parameter_inputs")
    for key in [
        "compressed_planck_lcdm_used",
        "archived_z4_reuse_used",
        "observational_fit_used",
        "full_no_fit_prediction_ready",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden/false-required flag must be false: {key}")

    closure = validate_effective_closure_payload(
        {
            "active_core": "Z2_tunnel_Sigma",
            "source": "effective_initial_data",
            "compressed_planck_lcdm_used": False,
            "archived_z4_reuse_used": False,
            "observational_fit_used": False,
            "full_no_fit_prediction_ready": False,
            "effective_initial_data": payload.get("effective_initial_data", {}),
            "effective_initial_data_provenance": payload.get(
                "effective_initial_data_provenance", {}
            ),
        }
    )
    z = _array(payload, "z_grid")
    e_values = _array(payload, "E_Z2Sigma")
    cs_values = _array(payload, "c_s_over_c_Z2Sigma")
    gamma_values = _array(payload, "Gamma_drag_over_H0_Z2Sigma")
    if e_values.shape != z.shape or cs_values.shape != z.shape or gamma_values.shape != z.shape:
        raise ValueError("effective primitive arrays must align with z_grid")
    if np.any(np.diff(z) <= 0.0):
        raise ValueError("z_grid must be strictly increasing")
    if np.any(e_values <= 0.0) or np.any(cs_values <= 0.0) or np.any(gamma_values <= 0.0):
        raise ValueError("effective primitive values must be positive")
    z_max = float(payload.get("z_max", z[-1]))
    if not math.isfinite(z_max) or z_max <= z[0] or z_max > z[-1]:
        raise ValueError("Require z_grid[0] < z_max <= z_grid[-1]")
    raw_bracket = payload.get("z_d_bracket")
    if raw_bracket is not None:
        if not isinstance(raw_bracket, list) or len(raw_bracket) != 2:
            raise ValueError("z_d_bracket must be null or a two-element list")
        lo, hi = [float(item) for item in raw_bracket]
        if not (z[0] <= lo < hi <= z_max):
            raise ValueError("z_d_bracket must lie inside the primitive z range")

    provenance = _clean_provenance_map(payload.get("primitive_provenance", {}))
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "effective_parameter_inputs",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "effective_initial_data": closure["effective_initial_data"],
        "effective_initial_data_provenance": closure[
            "effective_initial_data_provenance"
        ],
        "z_grid": z.tolist(),
        "E_Z2Sigma": e_values.tolist(),
        "c_s_over_c_Z2Sigma": cs_values.tolist(),
        "Gamma_drag_over_H0_Z2Sigma": gamma_values.tolist(),
        "omega_k_Z2Sigma": float(payload["omega_k_Z2Sigma"]),
        "z_max": z_max,
        "z_d_bracket": raw_bracket,
        "primitive_provenance": provenance,
    }


def load_effective_bao_parameter_inputs(path: Path) -> dict:
    return validate_effective_bao_parameter_inputs(
        json.loads(Path(path).read_text(encoding="utf-8"))
    )
