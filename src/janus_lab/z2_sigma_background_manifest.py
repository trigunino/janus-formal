"""Active Z2/Sigma background scalar manifest helpers."""

from __future__ import annotations

import json
from pathlib import Path

from .z2_sigma_normalization import make_active_z2sigma_critical_normalization


FORBIDDEN_PROVENANCE_TOKENS = ["demo", "lcdm", "planck", "z4", "holst_scan"]


def validate_active_z2sigma_scalar_provenance(scalar_provenance: dict[str, str]) -> dict[str, str]:
    return {
        "H0_Z2Sigma": _clean_source(scalar_provenance.get("H0_Z2Sigma", ""), "H0_Z2Sigma"),
        "omega_k_Z2Sigma": _clean_source(
            scalar_provenance.get("omega_k_Z2Sigma", ""), "omega_k_Z2Sigma"
        ),
        "G_Z2Sigma": _clean_source(scalar_provenance.get("G_Z2Sigma", ""), "G_Z2Sigma"),
    }


def _clean_source(source: str, field: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError(f"Missing active provenance for {field}")
    lowered = cleaned.lower()
    if any(token in lowered for token in FORBIDDEN_PROVENANCE_TOKENS):
        raise ValueError(f"Forbidden provenance for {field}: {cleaned}")
    return cleaned


def load_active_z2sigma_background_scalar_manifest(path: Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Manifest active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Manifest source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    if float(payload["H0_Z2Sigma_km_s_Mpc"]) <= 0.0:
        raise ValueError("H0_Z2Sigma_km_s_Mpc must be positive")
    if float(payload["gravitational_constant_si_Z2Sigma"]) <= 0.0:
        raise ValueError("gravitational_constant_si_Z2Sigma must be positive")
    validate_active_z2sigma_scalar_provenance(payload.get("scalar_provenance", {}))
    return payload


def write_active_z2sigma_background_scalar_manifest(
    path: Path,
    *,
    h0_z2sigma_km_s_mpc: float,
    omega_k_z2sigma: float,
    gravitational_constant_si_z2sigma: float,
    scalar_provenance: dict[str, str],
) -> Path:
    normalization = make_active_z2sigma_critical_normalization(
        h0_z2sigma_km_s_mpc,
        gravitational_constant_si_z2sigma=gravitational_constant_si_z2sigma,
    )
    payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_background_reuse_used": False,
        "observational_H0_fit_used": False,
        "H0_Z2Sigma_km_s_Mpc": normalization.h0_z2sigma_km_s_mpc,
        "omega_k_Z2Sigma": float(omega_k_z2sigma),
        "gravitational_constant_si_Z2Sigma": normalization.gravitational_constant_si_z2sigma,
        "critical_normalization": {
            "rho_crit0_Z2Sigma_kg_m3": normalization.rho_crit0_kg_m3,
            "kappa_Z2Sigma_SI": normalization.kappa_si,
            "kappa_rho_crit0_Z2Sigma_SI": normalization.kappa_rho_crit0_si,
            "gravitational_constant_source": _clean_source(
                scalar_provenance.get("G_Z2Sigma", ""), "G_Z2Sigma"
            ),
        },
        "scalar_provenance": validate_active_z2sigma_scalar_provenance(scalar_provenance),
    }
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    load_active_z2sigma_background_scalar_manifest(destination)
    return destination
