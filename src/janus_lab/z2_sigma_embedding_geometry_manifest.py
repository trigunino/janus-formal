"""Strict active Z2/Sigma embedding geometry manifest validation."""

from __future__ import annotations

import json
import math
from pathlib import Path

REQUIRED_EMBEDDING_GEOMETRY_FIELDS = [
    "a_grid",
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
    "z2_orientation_sign",
    "embedding_provenance",
]

OPTIONAL_FLRW_EXTRINSIC_CURVATURE_FIELDS = [
    "K_s_plus_Z2Sigma",
    "K_s_minus_Z2Sigma",
    "K_tau_plus_Z2Sigma",
    "K_tau_minus_Z2Sigma",
    "K_provenance",
]

FORBIDDEN_EMBEDDING_PROVENANCE_FLAGS = [
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
        raise ValueError(f"Embedding field {key} must be finite and match a_grid length")


def load_active_z2sigma_embedding_geometry_manifest(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    missing = [field for field in REQUIRED_EMBEDDING_GEOMETRY_FIELDS if field not in payload]
    if missing:
        raise ValueError(f"Embedding manifest missing fields: {missing}")
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Embedding manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Embedding manifest source must be active_derived")
    for flag in FORBIDDEN_EMBEDDING_PROVENANCE_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {flag}")
    a_grid = payload.get("a_grid")
    if not isinstance(a_grid, list) or not a_grid or not _finite_tree(a_grid):
        raise ValueError("Embedding field a_grid must be a nonempty finite list")
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
    if not math.isfinite(float(payload["z2_orientation_sign"])):
        raise ValueError("z2_orientation_sign must be finite")
    if not isinstance(payload.get("embedding_provenance"), str) or not payload[
        "embedding_provenance"
    ].strip():
        raise ValueError("embedding_provenance must be nonempty")
    return payload


def validate_optional_flrw_extrinsic_curvature_fields(payload: dict) -> list[str]:
    """Return missing optional K-grid fields, validating them when present."""

    missing = [field for field in OPTIONAL_FLRW_EXTRINSIC_CURVATURE_FIELDS if field not in payload]
    if missing:
        return missing
    a_grid = payload["a_grid"]
    for key in [
        "K_s_plus_Z2Sigma",
        "K_s_minus_Z2Sigma",
        "K_tau_plus_Z2Sigma",
        "K_tau_minus_Z2Sigma",
    ]:
        _require_series_matches_grid(payload, key, len(a_grid))
    provenance = str(payload.get("K_provenance", "")).strip()
    if not provenance:
        raise ValueError("K_provenance must be nonempty")
    lowered = provenance.lower()
    if any(token in lowered for token in ["planck", "lcdm", "z4", "fit", "bao_scan"]):
        raise ValueError(f"Forbidden provenance for K_provenance: {provenance}")
    return []
