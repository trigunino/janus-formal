"""Strict active Z2/Sigma R_Sigma solution certificate validation."""

from __future__ import annotations

import json
import math
from pathlib import Path


REQUIRED_RSIGMA_CERTIFICATE_FIELDS = [
    "effective_RSigma_equation",
    "R_Sigma_solution_certificate_type",
    "R_Sigma_solution_residual_max_abs",
    "a_grid",
    "R_Sigma_of_a",
    "X_plus_of_a",
    "X_minus_of_a",
    "R_curv_Z2Sigma_Mpc",
    "k_Z2Sigma",
    "H0_Z2Sigma_km_s_Mpc",
    "tangent_frames_plus",
    "tangent_frames_minus",
    "unit_normals_plus",
    "unit_normals_minus",
    "christoffels_plus",
    "christoffels_minus",
    "spatial_inverse_metric",
    "z2_orientation_sign",
    "rsigma_solution_provenance",
]

OPTIONAL_RSIGMA_CERTIFICATE_EMBEDDING_FIELDS = [
    "second_embedding_plus",
    "second_embedding_minus",
    "tau_index",
    "spatial_indices",
]

ACCEPTED_RSIGMA_CERTIFICATE_TYPES = {
    "active_no_fit_solution",
    "conditional_closed_frontier_solution",
}

FORBIDDEN_RSIGMA_PROVENANCE_FLAGS = [
    "compressed_planck_lcdm_background_used",
    "archived_z4_background_reuse_used",
    "observational_H0_fit_used",
    "observational_curvature_fit_used",
    "phenomenological_holst_bao_scan_used",
]


def _finite_tree(value) -> bool:
    if isinstance(value, (int, float)):
        return math.isfinite(float(value))
    if isinstance(value, list):
        return bool(value) and all(_finite_tree(item) for item in value)
    return False


def _require_series_matches_grid(payload: dict, key: str, a_grid_len: int) -> None:
    series = payload.get(key)
    if not isinstance(series, list) or len(series) != a_grid_len or not _finite_tree(series):
        raise ValueError(f"Certificate field {key} must be finite and match a_grid length")


def validate_active_z2sigma_rsigma_solution_certificate(payload: dict) -> dict:
    missing = [field for field in REQUIRED_RSIGMA_CERTIFICATE_FIELDS if field not in payload]
    if missing:
        raise ValueError(f"R_Sigma certificate missing fields: {missing}")
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("R_Sigma certificate active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("R_Sigma certificate source must be active_derived")
    equation = payload.get("effective_RSigma_equation")
    if not isinstance(equation, str) or "E_RSigma" not in equation:
        raise ValueError("effective_RSigma_equation must explicitly define E_RSigma")
    if payload.get("R_Sigma_solution_certificate_type") not in ACCEPTED_RSIGMA_CERTIFICATE_TYPES:
        raise ValueError("R_Sigma_solution_certificate_type is not accepted")
    residual = float(payload.get("R_Sigma_solution_residual_max_abs"))
    if not math.isfinite(residual) or residual > 1.0e-8:
        raise ValueError("R_Sigma_solution_residual_max_abs must be finite and <= 1e-8")
    for flag in FORBIDDEN_RSIGMA_PROVENANCE_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {flag}")
    a_grid = payload.get("a_grid")
    if not isinstance(a_grid, list) or not a_grid or not _finite_tree(a_grid):
        raise ValueError("Certificate field a_grid must be a nonempty finite list")
    for key in [
        "R_Sigma_of_a",
        "X_plus_of_a",
        "X_minus_of_a",
        "tangent_frames_plus",
        "tangent_frames_minus",
        "unit_normals_plus",
        "unit_normals_minus",
        "christoffels_plus",
        "christoffels_minus",
        "spatial_inverse_metric",
    ]:
        _require_series_matches_grid(payload, key, len(a_grid))
    for key in ["second_embedding_plus", "second_embedding_minus"]:
        if key in payload:
            _require_series_matches_grid(payload, key, len(a_grid))
    if "tau_index" in payload:
        tau_index = int(payload["tau_index"])
        if tau_index < 0:
            raise ValueError("tau_index must be nonnegative")
    if "spatial_indices" in payload:
        spatial_indices = payload["spatial_indices"]
        if (
            not isinstance(spatial_indices, list)
            or len(spatial_indices) != 3
            or any(int(index) < 0 for index in spatial_indices)
        ):
            raise ValueError("spatial_indices must be a list of three nonnegative indices")
    h0 = float(payload.get("H0_Z2Sigma_km_s_Mpc"))
    r_curv = float(payload.get("R_curv_Z2Sigma_Mpc"))
    if not math.isfinite(h0) or h0 <= 0.0:
        raise ValueError("H0_Z2Sigma_km_s_Mpc must be positive and finite")
    if not math.isfinite(r_curv) or r_curv <= 0.0:
        raise ValueError("R_curv_Z2Sigma_Mpc must be positive and finite")
    if int(payload.get("k_Z2Sigma")) not in [-1, 0, 1]:
        raise ValueError("k_Z2Sigma must be -1, 0, or 1")
    if not isinstance(payload.get("rsigma_solution_provenance"), str) or not payload[
        "rsigma_solution_provenance"
    ].strip():
        raise ValueError("rsigma_solution_provenance must be nonempty")
    return payload


def load_active_z2sigma_rsigma_solution_certificate(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    return validate_active_z2sigma_rsigma_solution_certificate(payload)


def write_active_z2sigma_rsigma_solution_certificate(path: Path, payload: dict) -> Path:
    validated = validate_active_z2sigma_rsigma_solution_certificate(dict(payload))
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(validated, indent=2), encoding="utf-8")
    return destination
