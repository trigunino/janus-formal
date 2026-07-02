from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_complete_cl_convention_calibration_gate import (
    CALIBRATED_VECTOR_PATH,
    build_payload as calibration_payload,
)

REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_gr_reference_convention_handshake_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_gr_reference_convention_handshake_gate.json")


def build_payload() -> dict:
    calibration = calibration_payload()
    vector = json.loads(CALIBRATED_VECTOR_PATH.read_text(encoding="utf-8"))
    ell = vector["ell"]
    required = {"cl_tt", "cl_te", "cl_ee", "cl_phiphi"}
    lengths_ok = all(len(vector[key]) == len(ell) for key in required)
    ell_order_ok = all(ell[i] < ell[i + 1] for i in range(len(ell) - 1))
    units_ok = vector["units"] == "dimensionless_Cl_CAMB_convention_calibrated"
    handshake = bool(calibration["cl_convention_calibration_passed"] and lengths_ok and ell_order_ok and units_ok)
    return {
        "status": "janus-z4-complete-gr-reference-convention-handshake-gate",
        "calibration_gate_passed": calibration["cl_convention_calibration_passed"],
        "calibrated_theory_vector_path": str(CALIBRATED_VECTOR_PATH),
        "cl_vs_dl_convention": "C_l",
        "units": vector["units"],
        "ell_indexing_increasing": ell_order_ok,
        "channel_lengths_match": lengths_ok,
        "contains_tt_te_ee_phiphi": required.issubset(vector.keys()),
        "gr_reference_convention_handshake_passed": handshake,
        "observed_likelihood_diagnostic_allowed": handshake,
        "observed_planck_validation": False,
        "candidate_promotion_allowed": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete GR Reference Convention Handshake Gate",
            "",
            f"Handshake passed: `{payload['gr_reference_convention_handshake_passed']}`",
            f"Units: `{payload['units']}`",
            f"Observed Planck validation: `{payload['observed_planck_validation']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
