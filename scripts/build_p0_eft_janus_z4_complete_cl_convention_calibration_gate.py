from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
    sys.path.insert(0, str(ROOT / "src"))

from janus_lab.z4_regenerative_camb_provider import CosmologyPoint, generate_camb_gr_rows
from scripts.build_p0_eft_janus_z4_complete_likelihood_ready_theory_vector_gate import (
    THEORY_VECTOR_PATH,
    build_payload as theory_vector_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_cl_convention_calibration_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_cl_convention_calibration_gate.json")
CALIBRATED_VECTOR_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_cl_convention_calibrated_theory_vector.json")


def _scale(raw: list[float], reference: list[float]) -> float:
    x = np.asarray(raw, dtype=float)
    y = np.asarray(reference, dtype=float)
    denom = float(np.dot(x, x))
    return 0.0 if denom == 0.0 else float(np.dot(x, y) / denom)


def build_payload() -> dict:
    base_gate = theory_vector_payload()
    vector = json.loads(THEORY_VECTOR_PATH.read_text(encoding="utf-8"))
    ells = [int(ell) for ell in vector["ell"]]
    reference_rows = generate_camb_gr_rows(CosmologyPoint(), ells=ells)
    reference = {
        "cl_tt": [row["cl_tt"] for row in reference_rows],
        "cl_te": [row["cl_te"] for row in reference_rows],
        "cl_ee": [row["cl_ee"] for row in reference_rows],
        "cl_phiphi": [row["cl_pp"] for row in reference_rows],
    }
    scales = {channel: _scale(vector[channel], reference[channel]) for channel in reference}
    calibrated = {
        "kind": "janus_z4_complete_cmb_theory_vector",
        "units": "dimensionless_Cl_CAMB_convention_calibrated",
        "calibration_policy": "least_squares_channel_scale_to_CAMB_GR_reference",
        "ell": vector["ell"],
        "cl_tt": [float(value * scales["cl_tt"]) for value in vector["cl_tt"]],
        "cl_te": [float(value * scales["cl_te"]) for value in vector["cl_te"]],
        "cl_ee": [float(value * scales["cl_ee"]) for value in vector["cl_ee"]],
        "cl_phiphi": [float(value * scales["cl_phiphi"]) for value in vector["cl_phiphi"]],
        "reference_convention": "janus_lab.z4_regenerative_camb_provider raw dimensionless C_l",
        "provenance": {
            **vector["provenance"],
            "raw_theory_vector_path": str(THEORY_VECTOR_PATH),
            "channel_scales": scales,
            "observed_planck_validation": False,
        },
    }
    CALIBRATED_VECTOR_PATH.write_text(json.dumps(calibrated, indent=2), encoding="utf-8")
    finite = all(np.isfinite(list(scales.values())))
    return {
        "status": "janus-z4-complete-cl-convention-calibration-gate",
        "input_theory_vector_available": base_gate["likelihood_ready_theory_vector_available"],
        "raw_units": vector["units"],
        "calibrated_theory_vector_path": str(CALIBRATED_VECTOR_PATH),
        "calibrated_units": calibrated["units"],
        "channel_scales": scales,
        "channel_scales_finite": bool(finite),
        "cl_convention_calibration_passed": bool(finite and base_gate["likelihood_ready_theory_vector_available"]),
        "calibration_is_physical_validation": False,
        "observed_likelihood_diagnostic_allowed": bool(finite),
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4CompleteGRReferenceConventionHandshakeGate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete C_l Convention Calibration Gate",
            "",
            f"Calibration passed: `{payload['cl_convention_calibration_passed']}`",
            f"Calibrated units: `{payload['calibrated_units']}`",
            f"Observed Planck validation: `{payload['observed_planck_validation']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
