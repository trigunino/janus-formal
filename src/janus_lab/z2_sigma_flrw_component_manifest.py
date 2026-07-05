"""Active Z2/Sigma FLRW stress-component manifest helpers."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np


FLRW_COMPONENT_FIELDS = [
    "cartan_ghy_rho",
    "cartan_ghy_p",
    "holst_nieh_yan_rho",
    "holst_nieh_yan_p",
    "matter_flux_rho",
    "matter_flux_p",
    "counterterm_rho",
    "counterterm_p",
]
FORBIDDEN_PROVENANCE_TOKENS = ["demo", "lcdm", "planck", "z4", "holst_scan"]


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def validate_active_z2sigma_flrw_component_provenance(provenance: dict[str, str]) -> dict[str, str]:
    return {field: _clean_source(provenance.get(field, ""), field) for field in FLRW_COMPONENT_FIELDS}


def _validate_grid(values, name: str) -> np.ndarray:
    grid = np.asarray(values, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError(f"{name} must be a one-dimensional grid with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError(f"{name} must be positive and strictly increasing")
    return grid


def load_active_z2sigma_flrw_component_manifest(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    a_grid = _validate_grid(payload["a_grid"], "a_grid")
    components = payload.get("flrw_components_over_rho_crit0", {})
    for field in FLRW_COMPONENT_FIELDS:
        values = np.asarray(components.get(field), dtype=float)
        if values.shape != a_grid.shape or not np.all(np.isfinite(values)):
            raise ValueError(f"{field} must be finite and aligned with a_grid")
    validate_active_z2sigma_flrw_component_provenance(payload.get("component_provenance", {}))
    return payload


def write_active_z2sigma_flrw_component_manifest(
    path: Path,
    *,
    a_grid,
    flrw_components_over_rho_crit0: dict[str, object],
    component_provenance: dict[str, str],
) -> Path:
    a_values = _validate_grid(a_grid, "a_grid")
    components: dict[str, list[float]] = {}
    for field in FLRW_COMPONENT_FIELDS:
        values = np.asarray(flrw_components_over_rho_crit0.get(field), dtype=float)
        if values.shape != a_values.shape or not np.all(np.isfinite(values)):
            raise ValueError(f"{field} must be finite and aligned with a_grid")
        components[field] = [float(value) for value in values]
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "a_grid": [float(value) for value in a_values],
        "flrw_components_over_rho_crit0": components,
        "component_provenance": validate_active_z2sigma_flrw_component_provenance(component_provenance),
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_flrw_component_manifest(destination)
    return destination
