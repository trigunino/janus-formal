"""Global regularity functional for the active Z2/Sigma tunnel route."""

from __future__ import annotations

import json
import math
from pathlib import Path

import numpy as np


FORBIDDEN_PROVENANCE = ("planck", "lcdm", "z4", "fit", "bao_scan")


def _array(payload: dict, key: str) -> np.ndarray:
    values = np.asarray(payload[key], dtype=float)
    if values.ndim != 1 or not np.all(np.isfinite(values)):
        raise ValueError(f"{key} must be a finite one-dimensional array")
    return values


def _clean_source(text: object, name: str) -> str:
    value = str(text).strip()
    if not value:
        raise ValueError(f"{name} provenance must be nonempty")
    lowered = value.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE):
        raise ValueError(f"Forbidden {name} provenance: {value}")
    return value


def regularity_roots(lambda_grid: np.ndarray, f_reg: np.ndarray, tolerance: float) -> list[float]:
    roots: list[float] = []
    for left_lam, right_lam, left_f, right_f in zip(
        lambda_grid[:-1],
        lambda_grid[1:],
        f_reg[:-1],
        f_reg[1:],
        strict=False,
    ):
        if abs(left_f) <= tolerance:
            roots.append(float(left_lam))
        if left_f == right_f:
            continue
        if left_f * right_f < 0.0:
            fraction = abs(left_f) / (abs(left_f) + abs(right_f))
            roots.append(float(left_lam + fraction * (right_lam - left_lam)))
    if abs(f_reg[-1]) <= tolerance:
        roots.append(float(lambda_grid[-1]))
    deduped: list[float] = []
    for root in roots:
        if not deduped or abs(root - deduped[-1]) > tolerance:
            deduped.append(root)
    return deduped


def validate_global_regular_component_payload(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("global regularity active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_global_regularity_components":
        raise ValueError("source must be active_global_regularity_components")
    for flag in [
        "compressed_planck_lcdm_used",
        "archived_z4_reuse_used",
        "observational_fit_used",
        "torus_replacement_used",
        "full_no_fit_prediction_ready",
    ]:
        if payload.get(flag) is not False:
            raise ValueError(f"{flag} must be false")

    lambdas = _array(payload, "lambda_grid")
    holonomy = _array(payload, "normal_frame_holonomy_defect")
    endpoint = _array(payload, "collar_endpoint_mismatch")
    bianchi = _array(payload, "junction_bianchi_defect")
    if np.any(lambdas <= 0.0) or np.any(np.diff(lambdas) <= 0.0):
        raise ValueError("lambda_grid must be positive and strictly increasing")
    if holonomy.shape != lambdas.shape or endpoint.shape != lambdas.shape or bianchi.shape != lambdas.shape:
        raise ValueError("F_reg component arrays must align with lambda_grid")
    if np.any(holonomy < 0.0) or np.any(endpoint < 0.0) or np.any(bianchi < 0.0):
        raise ValueError("F_reg component arrays must be nonnegative")
    tolerance = float(payload.get("root_tolerance", 1.0e-10))
    if not math.isfinite(tolerance) or tolerance <= 0.0:
        raise ValueError("root_tolerance must be positive and finite")
    provenance = payload.get("component_provenance", {})
    clean_provenance = {
        "normal_frame_holonomy_defect": _clean_source(
            provenance.get("normal_frame_holonomy_defect", ""),
            "normal_frame_holonomy_defect",
        ),
        "collar_endpoint_mismatch": _clean_source(
            provenance.get("collar_endpoint_mismatch", ""),
            "collar_endpoint_mismatch",
        ),
        "junction_bianchi_defect": _clean_source(
            provenance.get("junction_bianchi_defect", ""),
            "junction_bianchi_defect",
        ),
    }

    f_reg = holonomy + endpoint + bianchi
    roots = regularity_roots(lambdas, f_reg, tolerance)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_global_regularity_components",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "torus_replacement_used": False,
        "full_no_fit_prediction_ready": False,
        "lambda_grid": lambdas.tolist(),
        "F_reg_components": {
            "normal_frame_holonomy_defect": holonomy.tolist(),
            "collar_endpoint_mismatch": endpoint.tolist(),
            "junction_bianchi_defect": bianchi.tolist(),
        },
        "F_reg": f_reg.tolist(),
        "F_reg_min": float(np.min(f_reg)),
        "root_tolerance": tolerance,
        "regularity_roots": roots,
        "R_Sigma_over_ell_collar_selected": len(roots) == 1,
        "component_provenance": clean_provenance,
    }


def load_global_regular_component_payload(path: Path) -> dict:
    return validate_global_regular_component_payload(
        json.loads(Path(path).read_text(encoding="utf-8"))
    )
