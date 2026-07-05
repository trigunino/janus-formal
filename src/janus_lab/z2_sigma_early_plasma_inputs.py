"""Strict active Z2/Sigma early-plasma input manifest."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .z2_sigma_early_plasma_manifest import FORBIDDEN_PROVENANCE_TOKENS


REQUIRED_NORMALIZATIONS = [
    "rho_baryon0_Z2Sigma",
    "photon_temperature0_Z2Sigma",
    "radiation_constant_J_m3_K4",
    "baryon_mass_kg",
    "baryon_number_density0_m3_Z2Sigma",
    "ionization_fraction_Z2Sigma",
    "electrons_per_baryon",
    "sigma_thomson_m2",
]

COMMON_EARLY_PLASMA_NORMALIZATIONS = [
    "rho_baryon0_Z2Sigma",
    "photon_temperature0_Z2Sigma",
    "radiation_constant_J_m3_K4",
    "baryon_mass_kg",
    "baryon_number_density0_m3_Z2Sigma",
    "electrons_per_baryon",
    "sigma_thomson_m2",
]

BARYON_PHOTON_NORMALIZATIONS = [
    "rho_baryon0_Z2Sigma",
    "photon_temperature0_Z2Sigma",
    "radiation_constant_J_m3_K4",
    "baryon_mass_kg",
    "baryon_number_density0_m3_Z2Sigma",
]

IONIZATION_THOMSON_NORMALIZATIONS = [
    "ionization_fraction_Z2Sigma",
    "electrons_per_baryon",
    "sigma_thomson_m2",
]

IONIZATION_THOMSON_COMMON_NORMALIZATIONS = [
    "electrons_per_baryon",
    "sigma_thomson_m2",
]


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def _validate_provenance(provenance: dict[str, str]) -> dict[str, str]:
    return {field: _clean_source(provenance.get(field, ""), field) for field in REQUIRED_NORMALIZATIONS}


def _validate_ionization_history(payload: dict, z_grid: np.ndarray) -> dict | None:
    history = payload.get("ionization_history")
    if history is None:
        return None
    history_grid = np.asarray(history["z_grid"], dtype=float)
    values = np.asarray(history["ionization_fraction_Z2Sigma"], dtype=float)
    if history_grid.shape != z_grid.shape or not np.allclose(history_grid, z_grid):
        raise ValueError("ionization_history z_grid must match manifest z_grid")
    if values.shape != z_grid.shape:
        raise ValueError("ionization history values must match z_grid shape")
    if np.any(values < 0.0) or np.any(values > 1.0):
        raise ValueError("ionization history values must be in [0,1]")
    provenance = _clean_source(history.get("provenance", ""), "ionization_history")
    return {
        "z_grid": history_grid.tolist(),
        "ionization_fraction_Z2Sigma": values.tolist(),
        "provenance": provenance,
    }


def _validate_active_partial_payload(payload: dict, required_fields: list[str]) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input payload source must be active_derived")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    if z_grid.ndim != 1 or np.any(z_grid < 0.0) or np.any(np.diff(z_grid) <= 0.0):
        raise ValueError("z_grid must be non-negative and strictly increasing")
    normalizations = payload.get("normalizations", {})
    provenance = payload.get("normalization_provenance", {})
    for field in required_fields:
        value = float(normalizations[field])
        if value <= 0.0:
            raise ValueError(f"{field} must be positive")
        _clean_source(provenance.get(field, ""), field)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": z_grid.tolist(),
        "normalizations": {field: float(normalizations[field]) for field in required_fields},
        "normalization_provenance": {
            field: _clean_source(provenance.get(field, ""), field) for field in required_fields
        },
    }


def build_active_z2sigma_baryon_photon_input_payload(payload: dict) -> dict:
    built = _validate_active_partial_payload(payload, BARYON_PHOTON_NORMALIZATIONS)
    rho_from_number = (
        float(built["normalizations"]["baryon_number_density0_m3_Z2Sigma"])
        * float(built["normalizations"]["baryon_mass_kg"])
    )
    if not np.isclose(
        float(built["normalizations"]["rho_baryon0_Z2Sigma"]),
        rho_from_number,
        rtol=1.0e-9,
        atol=0.0,
    ):
        raise ValueError("rho_baryon0_Z2Sigma must match n_b0*baryon_mass")
    return built


def build_active_z2sigma_ionization_thomson_input_payload(payload: dict) -> dict:
    normalizations = payload.get("normalizations", {})
    if "ionization_fraction_Z2Sigma" in normalizations:
        return _validate_active_partial_payload(payload, IONIZATION_THOMSON_NORMALIZATIONS)
    built = _validate_active_partial_payload(payload, IONIZATION_THOMSON_COMMON_NORMALIZATIONS)
    history = _validate_ionization_history(payload, np.asarray(built["z_grid"], dtype=float))
    if history is None:
        raise ValueError("Require ionization_fraction_Z2Sigma or ionization_history")
    built["ionization_history"] = history
    return built


def load_active_z2sigma_early_plasma_input_manifest(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_rd_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    z_grid = np.asarray(payload["z_grid"], dtype=float)
    if z_grid.ndim != 1 or np.any(z_grid < 0.0) or np.any(np.diff(z_grid) <= 0.0):
        raise ValueError("z_grid must be non-negative and strictly increasing")
    normalizations = payload.get("normalizations", {})
    for field in COMMON_EARLY_PLASMA_NORMALIZATIONS:
        value = float(normalizations[field])
        if value <= 0.0:
            raise ValueError(f"{field} must be positive")
    rho_from_number = (
        float(normalizations["baryon_number_density0_m3_Z2Sigma"])
        * float(normalizations["baryon_mass_kg"])
    )
    if not np.isclose(
        float(normalizations["rho_baryon0_Z2Sigma"]),
        rho_from_number,
        rtol=1.0e-9,
        atol=0.0,
    ):
        raise ValueError("rho_baryon0_Z2Sigma must match n_b0*baryon_mass")
    provenance = payload.get("normalization_provenance", {})
    for field in COMMON_EARLY_PLASMA_NORMALIZATIONS:
        _clean_source(provenance.get(field, ""), field)
    if "ionization_fraction_Z2Sigma" in normalizations:
        if float(normalizations["ionization_fraction_Z2Sigma"]) <= 0.0:
            raise ValueError("ionization_fraction_Z2Sigma must be positive")
        _clean_source(provenance.get("ionization_fraction_Z2Sigma", ""), "ionization_fraction_Z2Sigma")
    else:
        history = _validate_ionization_history(payload, z_grid)
        if history is None:
            raise ValueError("Require ionization_fraction_Z2Sigma or ionization_history")
    return payload


def assemble_active_z2sigma_early_plasma_input_manifest(
    *,
    baryon_photon_payload: dict,
    ionization_thomson_payload: dict,
) -> dict:
    for payload in [baryon_photon_payload, ionization_thomson_payload]:
        if payload.get("active_core") != "Z2_tunnel_Sigma":
            raise ValueError("Input payload active_core must be Z2_tunnel_Sigma")
        if payload.get("source") != "active_derived":
            raise ValueError("Input payload source must be active_derived")
        for key in [
            "compressed_planck_lcdm_rd_used",
            "archived_z4_reuse_used",
            "phenomenological_holst_bao_scan_used",
        ]:
            if payload.get(key) is not False:
                raise ValueError(f"Forbidden provenance flag must be false: {key}")

    z_grid = np.asarray(baryon_photon_payload["z_grid"], dtype=float)
    other_grid = np.asarray(ionization_thomson_payload["z_grid"], dtype=float)
    if z_grid.ndim != 1 or np.any(z_grid < 0.0) or np.any(np.diff(z_grid) <= 0.0):
        raise ValueError("z_grid must be non-negative and strictly increasing")
    if other_grid.shape != z_grid.shape or not np.allclose(other_grid, z_grid):
        raise ValueError("Early-plasma z_grids must match")

    normalizations = {}
    provenance = {}
    for payload in [baryon_photon_payload, ionization_thomson_payload]:
        normalizations.update(payload.get("normalizations", {}))
        provenance.update(payload.get("normalization_provenance", {}))
    candidate = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "z_grid": z_grid.tolist(),
        "normalizations": normalizations,
        "normalization_provenance": provenance,
    }
    if "ionization_history" in ionization_thomson_payload:
        candidate["ionization_history"] = ionization_thomson_payload["ionization_history"]

    for field in COMMON_EARLY_PLASMA_NORMALIZATIONS:
        value = float(candidate["normalizations"][field])
        if value <= 0.0:
            raise ValueError(f"{field} must be positive")
    if "ionization_fraction_Z2Sigma" in candidate["normalizations"]:
        value = float(candidate["normalizations"]["ionization_fraction_Z2Sigma"])
        if value <= 0.0:
            raise ValueError("ionization_fraction_Z2Sigma must be positive")
    else:
        history = _validate_ionization_history(candidate, z_grid)
        if history is None:
            raise ValueError("Require ionization_fraction_Z2Sigma or ionization_history")
    rho_from_number = (
        float(candidate["normalizations"]["baryon_number_density0_m3_Z2Sigma"])
        * float(candidate["normalizations"]["baryon_mass_kg"])
    )
    if not np.isclose(
        float(candidate["normalizations"]["rho_baryon0_Z2Sigma"]),
        rho_from_number,
        rtol=1.0e-9,
        atol=0.0,
    ):
        raise ValueError("rho_baryon0_Z2Sigma must match n_b0*baryon_mass")
    for field in COMMON_EARLY_PLASMA_NORMALIZATIONS:
        _clean_source(candidate["normalization_provenance"].get(field, ""), field)
    if "ionization_fraction_Z2Sigma" in candidate["normalization_provenance"]:
        _clean_source(
            candidate["normalization_provenance"].get("ionization_fraction_Z2Sigma", ""),
            "ionization_fraction_Z2Sigma",
        )
    return candidate
