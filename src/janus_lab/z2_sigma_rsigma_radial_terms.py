"""Strict active Z2/Sigma R_Sigma radial-term manifests."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .z2_sigma_rsigma_equation import _clean_term_provenance


RADIAL_TERM_FIELDS = {
    "E_CartanGHY",
    "E_HolstNiehYan",
    "E_matterFlux",
    "E_counterterm",
}


def _validate_header(payload: dict) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Radial term active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Radial term source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def load_active_z2sigma_rsigma_radial_term_manifest(
    path: Path,
    *,
    expected_term_name: str | None = None,
) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    _validate_header(payload)
    term_name = str(payload.get("term_name", ""))
    if term_name not in RADIAL_TERM_FIELDS:
        raise ValueError("Unsupported radial term_name")
    if expected_term_name is not None and term_name != expected_term_name:
        raise ValueError(f"Expected radial term {expected_term_name}")
    a_grid = np.asarray(payload.get("a_grid"), dtype=float)
    values = np.asarray(payload.get("term_values"), dtype=float)
    if a_grid.ndim != 1 or len(a_grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(a_grid <= 0.0) or np.any(np.diff(a_grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if values.shape != a_grid.shape or not np.all(np.isfinite(values)):
        raise ValueError("term_values must be finite and aligned with a_grid")
    provenance = _clean_term_provenance(payload.get("term_provenance", ""), term_name)
    return {
        **payload,
        "term_name": term_name,
        "a_grid": a_grid.tolist(),
        "term_values": values.tolist(),
        "term_provenance": provenance,
    }


def build_active_z2sigma_rsigma_radial_term_payload(
    *,
    term_name: str,
    a_grid,
    term_values,
    term_provenance: str,
) -> dict:
    if term_name not in RADIAL_TERM_FIELDS:
        raise ValueError("Unsupported radial term_name")
    grid = np.asarray(a_grid, dtype=float)
    values = np.asarray(term_values, dtype=float)
    if grid.ndim != 1 or len(grid) < 2:
        raise ValueError("a_grid must be one-dimensional with at least two points")
    if np.any(grid <= 0.0) or np.any(np.diff(grid) <= 0.0):
        raise ValueError("a_grid must be positive and strictly increasing")
    if values.shape != grid.shape or not np.all(np.isfinite(values)):
        raise ValueError("term_values must be finite and aligned with a_grid")
    provenance = _clean_term_provenance(term_provenance, term_name)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "term_name": term_name,
        "a_grid": grid.tolist(),
        "term_values": values.tolist(),
        "term_provenance": provenance,
    }


def write_active_z2sigma_rsigma_radial_term_manifest(path: Path, payload: dict) -> Path:
    validated = load_active_z2sigma_rsigma_radial_term_manifest_from_payload(payload)
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(validated, indent=2), encoding="utf-8")
    return destination


def load_active_z2sigma_rsigma_radial_term_manifest_from_payload(payload: dict) -> dict:
    _validate_header(payload)
    term_name = str(payload.get("term_name", ""))
    if term_name not in RADIAL_TERM_FIELDS:
        raise ValueError("Unsupported radial term_name")
    return build_active_z2sigma_rsigma_radial_term_payload(
        term_name=term_name,
        a_grid=payload.get("a_grid"),
        term_values=payload.get("term_values"),
        term_provenance=payload.get("term_provenance", ""),
    )


def merge_active_z2sigma_rsigma_radial_terms(
    *,
    cartan_ghy_payload: dict,
    holst_nieh_yan_payload: dict,
    matter_flux_payload: dict,
    counterterm_payload: dict,
    certificate_payload: dict,
) -> dict:
    payloads = {
        "E_CartanGHY": cartan_ghy_payload,
        "E_HolstNiehYan": holst_nieh_yan_payload,
        "E_matterFlux": matter_flux_payload,
        "E_counterterm": counterterm_payload,
    }
    grids = []
    terms = {}
    provenance = {}
    for term_name, payload in payloads.items():
        if payload.get("term_name") != term_name:
            raise ValueError(f"Payload term_name must be {term_name}")
        grid = np.asarray(payload["a_grid"], dtype=float)
        values = np.asarray(payload["term_values"], dtype=float)
        grids.append(grid)
        terms[term_name] = values
        provenance[term_name] = _clean_term_provenance(
            payload.get("term_provenance", ""),
            term_name,
        )
    a_grid = grids[0]
    for grid in grids[1:]:
        if grid.shape != a_grid.shape or not np.allclose(grid, a_grid):
            raise ValueError("All radial term a_grids must match")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": a_grid.tolist(),
        "E_CartanGHY": terms["E_CartanGHY"].tolist(),
        "E_HolstNiehYan": terms["E_HolstNiehYan"].tolist(),
        "E_matterFlux": terms["E_matterFlux"].tolist(),
        "E_counterterm": terms["E_counterterm"].tolist(),
        "term_provenance": provenance,
        "certificate_payload": certificate_payload,
    }


def write_active_z2sigma_rsigma_radial_terms_input_manifest(
    path: Path,
    payload: dict,
) -> Path:
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return destination
