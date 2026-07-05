"""Strict active Z2/Sigma FLRW component input manifest."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .z2_sigma_flrw_component_manifest import (
    FLRW_COMPONENT_FIELDS,
    FORBIDDEN_PROVENANCE_TOKENS,
)

MATTER_FLUX_FIELDS = ["matter_flux_rho", "matter_flux_p"]
NON_MATTER_FLUX_FIELDS = [field for field in FLRW_COMPONENT_FIELDS if field not in MATTER_FLUX_FIELDS]


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def load_active_z2sigma_flrw_component_input_manifest(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    a_grid = np.asarray(payload["a_grid"], dtype=float)
    if a_grid.ndim != 1 or len(a_grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    components = payload.get("flrw_components_over_rho_crit0", {})
    for field in FLRW_COMPONENT_FIELDS:
        values = np.asarray(components.get(field), dtype=float)
        if values.shape != a_grid.shape or not np.all(np.isfinite(values)):
            raise ValueError(f"{field} must be finite and aligned with a_grid")
        _clean_source(payload.get("component_provenance", {}).get(field, ""), field)
    return payload


def merge_active_flrw_components_with_matter_flux(
    partial_payload: dict,
    matter_flux_payload: dict,
) -> dict:
    if partial_payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Partial manifest active_core must be Z2_tunnel_Sigma")
    if partial_payload.get("source") != "active_derived":
        raise ValueError("Partial manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if partial_payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if matter_flux_payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Matter-flux payload active_core must be Z2_tunnel_Sigma")
    if matter_flux_payload.get("source") != "active_derived":
        raise ValueError("Matter-flux payload source must be active_derived")
    if matter_flux_payload.get("active_sigma_transparency_derived") is not True:
        raise ValueError("Matter-flux payload must derive active Sigma transparency")

    a_grid = np.asarray(partial_payload["a_grid"], dtype=float)
    matter_grid = np.asarray(matter_flux_payload["a_grid"], dtype=float)
    if a_grid.ndim != 1 or len(a_grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if matter_grid.shape != a_grid.shape or not np.allclose(matter_grid, a_grid):
        raise ValueError("Matter-flux a_grid must match partial FLRW a_grid")

    partial_components = partial_payload.get("flrw_components_over_rho_crit0", {})
    partial_provenance = partial_payload.get("component_provenance", {})
    matter_components = matter_flux_payload.get("flrw_components_over_rho_crit0", {})
    matter_provenance = matter_flux_payload.get("component_provenance", {})
    merged_components: dict[str, list[float]] = {}
    merged_provenance: dict[str, str] = {}

    for field in NON_MATTER_FLUX_FIELDS:
        values = np.asarray(partial_components.get(field), dtype=float)
        if values.shape != a_grid.shape or not np.all(np.isfinite(values)):
            raise ValueError(f"{field} must be finite and aligned with a_grid")
        merged_components[field] = values.tolist()
        merged_provenance[field] = _clean_source(partial_provenance.get(field, ""), field)
    for field in MATTER_FLUX_FIELDS:
        values = np.asarray(matter_components.get(field), dtype=float)
        if values.shape != a_grid.shape or not np.all(np.isfinite(values)):
            raise ValueError(f"{field} must be finite and aligned with a_grid")
        merged_components[field] = values.tolist()
        merged_provenance[field] = _clean_source(matter_provenance.get(field, ""), field)

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": a_grid.tolist(),
        "flrw_components_over_rho_crit0": merged_components,
        "component_provenance": merged_provenance,
    }


def merge_active_non_matter_flrw_component_payloads(
    *,
    cartan_ghy_payload: dict,
    holst_nieh_yan_payload: dict,
    counterterm_payload: dict,
) -> dict:
    payloads = [cartan_ghy_payload, holst_nieh_yan_payload, counterterm_payload]
    for payload in payloads:
        if payload.get("active_core") != "Z2_tunnel_Sigma":
            raise ValueError("Component payload active_core must be Z2_tunnel_Sigma")
        if payload.get("source") != "active_derived":
            raise ValueError("Component payload source must be active_derived")
        for key in [
            "compressed_planck_lcdm_background_used",
            "archived_z4_reuse_used",
            "phenomenological_holst_bao_scan_used",
        ]:
            if payload.get(key) is not False:
                raise ValueError(f"Forbidden provenance flag must be false: {key}")

    a_grid = np.asarray(cartan_ghy_payload["a_grid"], dtype=float)
    if a_grid.ndim != 1 or len(a_grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    for payload in [holst_nieh_yan_payload, counterterm_payload]:
        other_grid = np.asarray(payload["a_grid"], dtype=float)
        if other_grid.shape != a_grid.shape or not np.allclose(other_grid, a_grid):
            raise ValueError("All component a_grids must match")

    source_by_field = {
        "cartan_ghy_rho": cartan_ghy_payload,
        "cartan_ghy_p": cartan_ghy_payload,
        "holst_nieh_yan_rho": holst_nieh_yan_payload,
        "holst_nieh_yan_p": holst_nieh_yan_payload,
        "counterterm_rho": counterterm_payload,
        "counterterm_p": counterterm_payload,
    }
    merged_components: dict[str, list[float]] = {}
    merged_provenance: dict[str, str] = {}
    for field, payload in source_by_field.items():
        components = payload.get("flrw_components_over_rho_crit0", {})
        provenance = payload.get("component_provenance", {})
        values = np.asarray(components.get(field), dtype=float)
        if values.shape != a_grid.shape or not np.all(np.isfinite(values)):
            raise ValueError(f"{field} must be finite and aligned with a_grid")
        merged_components[field] = values.tolist()
        merged_provenance[field] = _clean_source(provenance.get(field, ""), field)

    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": a_grid.tolist(),
        "flrw_components_over_rho_crit0": merged_components,
        "component_provenance": merged_provenance,
    }


def build_active_flrw_component_pair_payload(
    *,
    a_grid: list[float] | np.ndarray,
    rho_field: str,
    pressure_field: str,
    rho_values: list[float] | np.ndarray,
    pressure_values: list[float] | np.ndarray,
    component_route: str,
    component_provenance: str,
) -> dict:
    if rho_field not in FLRW_COMPONENT_FIELDS or pressure_field not in FLRW_COMPONENT_FIELDS:
        raise ValueError("Component fields must belong to the FLRW component schema")
    grid = np.asarray(a_grid, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    rho = np.asarray(rho_values, dtype=float)
    pressure = np.asarray(pressure_values, dtype=float)
    if rho.shape != grid.shape or not np.all(np.isfinite(rho)):
        raise ValueError(f"{rho_field} must be finite and aligned with a_grid")
    if pressure.shape != grid.shape or not np.all(np.isfinite(pressure)):
        raise ValueError(f"{pressure_field} must be finite and aligned with a_grid")
    provenance = _clean_source(component_provenance, component_route)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "component_route": component_route,
        "a_grid": grid.tolist(),
        "flrw_components_over_rho_crit0": {
            rho_field: rho.tolist(),
            pressure_field: pressure.tolist(),
        },
        "component_provenance": {
            rho_field: provenance,
            pressure_field: provenance,
        },
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
    }
