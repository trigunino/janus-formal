"""Strict active Z2/Sigma background scalar input manifest."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from .z2_sigma_background import omega_k_from_flrw_curvature_radius
from .z2_sigma_background_manifest import FORBIDDEN_PROVENANCE_TOKENS


REQUIRED_SCALARS = [
    "H0_Z2Sigma_km_s_Mpc",
    "omega_k_Z2Sigma",
    "gravitational_constant_si_Z2Sigma",
]

SCALAR_PROVENANCE_KEYS = {
    "H0_Z2Sigma_km_s_Mpc": "H0_Z2Sigma",
    "omega_k_Z2Sigma": "omega_k_Z2Sigma",
    "gravitational_constant_si_Z2Sigma": "G_Z2Sigma",
    "R_curv_Z2Sigma_Mpc": "R_curv_Z2Sigma",
}


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def load_active_z2sigma_background_scalar_input_manifest(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    scalars = payload.get("scalars", {})
    h0 = float(scalars["H0_Z2Sigma_km_s_Mpc"])
    omega_k = float(scalars["omega_k_Z2Sigma"])
    g_si = float(scalars["gravitational_constant_si_Z2Sigma"])
    if h0 <= 0.0:
        raise ValueError("H0_Z2Sigma_km_s_Mpc must be positive")
    if not np.isfinite(omega_k):
        raise ValueError("omega_k_Z2Sigma must be finite")
    if g_si <= 0.0:
        raise ValueError("gravitational_constant_si_Z2Sigma must be positive")
    provenance = payload.get("scalar_provenance", {})
    for field in ["H0_Z2Sigma", "omega_k_Z2Sigma", "G_Z2Sigma"]:
        _clean_source(provenance.get(field, ""), field)
    return payload


def _validate_active_scalar_payload(payload: dict, scalar_field: str) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Scalar payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Scalar payload source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    value = float(payload.get("scalars", {})[scalar_field])
    if scalar_field in [
        "H0_Z2Sigma_km_s_Mpc",
        "gravitational_constant_si_Z2Sigma",
        "R_curv_Z2Sigma_Mpc",
    ]:
        if value <= 0.0:
            raise ValueError(f"{scalar_field} must be positive")
    elif not np.isfinite(value):
        raise ValueError(f"{scalar_field} must be finite")
    provenance_key = SCALAR_PROVENANCE_KEYS[scalar_field]
    provenance = _clean_source(
        payload.get("scalar_provenance", {}).get(provenance_key, ""),
        provenance_key,
    )
    return {
        "value": value,
        "provenance_key": provenance_key,
        "provenance": provenance,
    }


def build_active_z2sigma_background_scalar_payload(payload: dict, scalar_field: str) -> dict:
    built = _validate_active_scalar_payload(payload, scalar_field)
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {scalar_field: built["value"]},
        "scalar_provenance": {built["provenance_key"]: built["provenance"]},
    }


def build_active_z2sigma_curvature_payload_from_flrw_branch(payload: dict) -> dict:
    """Build the strict omega_k scalar payload from active FLRW branch data."""

    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Curvature branch payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Curvature branch payload source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")

    scalars = payload.get("scalars", {})
    h0 = float(scalars["H0_Z2Sigma_km_s_Mpc"])
    radius = float(scalars["R_curv_Z2Sigma_Mpc"])
    sign = int(scalars["k_Z2Sigma"])
    if float(scalars["k_Z2Sigma"]) != float(sign):
        raise ValueError("k_Z2Sigma must be an integer -1, 0 or 1")
    omega_k = omega_k_from_flrw_curvature_radius(h0, radius, sign)

    provenance = payload.get("scalar_provenance", {})
    h0_provenance = _clean_source(provenance.get("H0_Z2Sigma", ""), "H0_Z2Sigma")
    sign_provenance = _clean_source(provenance.get("k_Z2Sigma", ""), "k_Z2Sigma")
    radius_provenance = _clean_source(
        provenance.get("R_curv_Z2Sigma", ""),
        "R_curv_Z2Sigma",
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {"omega_k_Z2Sigma": omega_k},
        "scalar_provenance": {
            "omega_k_Z2Sigma": (
                "active_flrw_spatial_metric_branch:"
                f"k=({sign_provenance});R_curv=({radius_provenance});"
                f"H0=({h0_provenance})"
            )
        },
    }


def assemble_active_z2sigma_background_scalar_input_manifest(
    *,
    h0_payload: dict,
    curvature_payload: dict,
    gravity_payload: dict,
) -> dict:
    h0 = _validate_active_scalar_payload(h0_payload, "H0_Z2Sigma_km_s_Mpc")
    curvature = _validate_active_scalar_payload(curvature_payload, "omega_k_Z2Sigma")
    gravity = _validate_active_scalar_payload(
        gravity_payload,
        "gravitational_constant_si_Z2Sigma",
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "scalars": {
            "H0_Z2Sigma_km_s_Mpc": h0["value"],
            "omega_k_Z2Sigma": curvature["value"],
            "gravitational_constant_si_Z2Sigma": gravity["value"],
        },
        "scalar_provenance": {
            h0["provenance_key"]: h0["provenance"],
            curvature["provenance_key"]: curvature["provenance"],
            gravity["provenance_key"]: gravity["provenance"],
        },
    }
