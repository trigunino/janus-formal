"""Strict projected occupation-state input validation for Z2/Sigma."""

from __future__ import annotations

import json
import math
from pathlib import Path


FORBIDDEN_OCCUPATION_PROVENANCE = ("planck", "lcdm", "z4", "fit", "bao_scan")


def clean_occupation_provenance(source: object) -> str:
    text = str(source).strip()
    if not text:
        raise ValueError("N_occ provenance must be nonempty")
    lowered = text.lower()
    if any(token in lowered for token in FORBIDDEN_OCCUPATION_PROVENANCE):
        raise ValueError(f"Forbidden N_occ provenance: {text}")
    return text


def validate_projected_occupation_state_payload(payload: dict) -> dict:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("occupation active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "explicit_state_initial_data":
        raise ValueError("occupation source must be explicit_state_initial_data")
    if payload.get("full_no_fit_prediction_ready") is not False:
        raise ValueError("occupation input must keep full_no_fit_prediction_ready false")
    occupation = float(payload["N_occ_Z2Sigma"])
    if not math.isfinite(occupation) or occupation <= 0.0:
        raise ValueError("N_occ_Z2Sigma must be positive and finite")
    provenance = clean_occupation_provenance(payload.get("N_occ_provenance", ""))
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "explicit_state_initial_data",
        "full_no_fit_prediction_ready": False,
        "N_occ_Z2Sigma": occupation,
        "N_occ_provenance": provenance,
    }


def load_projected_occupation_state_payload(path: Path) -> dict:
    return validate_projected_occupation_state_payload(
        json.loads(Path(path).read_text(encoding="utf-8"))
    )
