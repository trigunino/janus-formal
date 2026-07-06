"""Effective Janus Z2/Sigma closure manifests.

This module is intentionally separate from the strict active-derived validators.
It allows controlled initial data for the two quantities that the no-extension
audit leaves open: throat scale and projected baryon charge.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_used",
    "archived_z4_reuse_used",
    "observational_fit_used",
]


def _finite_positive(value: object, name: str) -> float:
    if value is None:
        raise ValueError(f"{name} must be provided")
    number = float(value)
    if not math.isfinite(number) or number <= 0.0:
        raise ValueError(f"{name} must be positive and finite")
    return number


def _clean_provenance(value: object, name: str) -> str:
    text = str(value).strip()
    if not text:
        raise ValueError(f"{name} provenance must be nonempty")
    lowered = text.lower()
    if any(token in lowered for token in ["planck", "lcdm", "z4", "fit", "bao_scan"]):
        raise ValueError(f"Forbidden {name} provenance: {text}")
    return text


def validate_effective_closure_payload(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("effective closure active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "effective_initial_data":
        raise ValueError("effective closure source must be effective_initial_data")
    for flag in FORBIDDEN_FLAGS:
        if payload.get(flag) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {flag}")
    if payload.get("full_no_fit_prediction_ready") is not False:
        raise ValueError("effective closure must keep full_no_fit_prediction_ready=false")
    data = payload.get("effective_initial_data", {})
    provenance = payload.get("effective_initial_data_provenance", {})
    ratio_key = "R_Sigma_over_ell_collar_Z2Sigma"
    ratio = _finite_positive(data.get(ratio_key), ratio_key)
    charge = _finite_positive(
        data.get("projected_baryon_number_charge_Z2Sigma"),
        "projected_baryon_number_charge_Z2Sigma",
    )
    ratio_source = _clean_provenance(provenance.get(ratio_key, ""), ratio_key)
    charge_source = _clean_provenance(
        provenance.get("projected_baryon_number_charge_Z2Sigma", ""),
        "projected_baryon_number_charge_Z2Sigma",
    )
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "effective_initial_data",
        "compressed_planck_lcdm_used": False,
        "archived_z4_reuse_used": False,
        "observational_fit_used": False,
        "full_no_fit_prediction_ready": False,
        "effective_closure_ready": True,
        "effective_initial_data": {
            "R_Sigma_over_ell_collar_Z2Sigma": ratio,
            "projected_baryon_number_charge_Z2Sigma": charge,
        },
        "effective_initial_data_provenance": {
            "R_Sigma_over_ell_collar_Z2Sigma": ratio_source,
            "projected_baryon_number_charge_Z2Sigma": charge_source,
        },
    }


def load_effective_closure_payload(path: Path) -> dict:
    return validate_effective_closure_payload(
        json.loads(Path(path).read_text(encoding="utf-8"))
    )


def write_effective_closure_payload(path: Path, payload: dict) -> Path:
    validated = validate_effective_closure_payload(dict(payload))
    destination = Path(path)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(validated, indent=2), encoding="utf-8")
    return destination
