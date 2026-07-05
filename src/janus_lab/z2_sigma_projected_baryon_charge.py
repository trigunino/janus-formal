"""Strict active Z2/Sigma projected baryon Noether charge manifest validation."""

from __future__ import annotations

import json
import math
from pathlib import Path

FORBIDDEN_PROJECTED_BARYON_CHARGE_FLAGS = [
    "compressed_planck_lcdm_rd_used",
    "archived_z4_reuse_used",
    "phenomenological_holst_bao_scan_used",
    "observational_baryon_fit_used",
]


def clean_projected_baryon_charge_source(source: str) -> str:
    cleaned = str(source).strip()
    if not cleaned:
        raise ValueError("Missing projected baryon charge provenance")
    lowered = cleaned.lower()
    for token in ["planck", "lcdm", "z4", "fit", "bao_scan"]:
        if token in lowered:
            raise ValueError(f"Forbidden projected baryon charge provenance: {cleaned}")
    return cleaned


def validate_active_projected_baryon_charge_payload(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Projected baryon charge active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Projected baryon charge source must be active_derived")
    for flag in FORBIDDEN_PROJECTED_BARYON_CHARGE_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {flag}")
    normalizations = payload.get("normalizations", {})
    provenance = payload.get("normalization_provenance", {})
    charge = float(normalizations["projected_baryon_number_charge_Z2Sigma"])
    if not math.isfinite(charge) or charge <= 0.0:
        raise ValueError("projected_baryon_number_charge_Z2Sigma must be positive and finite")
    source = clean_projected_baryon_charge_source(
        provenance.get("projected_baryon_number_charge_Z2Sigma", "")
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_baryon_fit_used": False,
        "normalizations": {
            "projected_baryon_number_charge_Z2Sigma": charge,
        },
        "normalization_provenance": {
            "projected_baryon_number_charge_Z2Sigma": source,
        },
    }


def load_active_projected_baryon_charge_manifest(path: Path) -> dict:
    return validate_active_projected_baryon_charge_payload(
        json.loads(Path(path).read_text(encoding="utf-8"))
    )
