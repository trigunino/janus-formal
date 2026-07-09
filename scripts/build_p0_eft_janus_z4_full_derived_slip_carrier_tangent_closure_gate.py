from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_derived_slip_carrier_tangent_projection_gate import build_payload as tangent_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_full_derived_slip_carrier_tangent_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_full_derived_slip_carrier_tangent_closure_gate.json")
CARRIER_TANGENT_THRESHOLD = 0.85


def build_payload() -> dict:
    tangent = tangent_payload()
    parallel = float(tangent["derived_slip_parallel_fraction"])
    closure = parallel >= CARRIER_TANGENT_THRESHOLD
    return {
        "status": "janus-z4-full-derived-slip-carrier-tangent-closure-gate",
        "full_derived_slip_parallel_fraction": parallel,
        "full_derived_slip_perpendicular_fraction": float(tangent["derived_slip_perpendicular_fraction"]),
        "old_no_slip_parallel_fraction": float(tangent["old_no_slip_parallel_fraction"]),
        "dominant_tangent_direction": tangent["dominant_tangent_direction"],
        "full_derived_slip_carrier_tangent": closure,
        "closure_recommended": closure,
        "candidate_promotion_allowed": False,
        "Planck_trial_allowed": False,
        "no_lambda_retuning": True,
        "no_free_slip_parameter": True,
        "no_free_eta_ratio": True,
        "no_direct_Cl_patch": True,
        "raw_toy_LOS_forbidden": True,
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Full Derived Slip Carrier-Tangent Closure Gate",
        "",
        f"Closure recommended: `{payload['closure_recommended']}`",
        f"Parallel fraction: `{payload['full_derived_slip_parallel_fraction']}`",
        f"Dominant tangent: `{payload['dominant_tangent_direction']}`",
        f"Planck trial allowed: `{payload['Planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
