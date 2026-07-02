from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_diagnostic_shape_report_gate import build_payload as shape_payload


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_pre_likelihood_lock_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_pre_likelihood_lock_gate.json")


def build_payload() -> dict:
    shape = shape_payload()
    zero_artifacts = {
        channel: row["zero_count_delta"]
        for channel, row in shape["shape_rows"].items()
        if row["zero_count_delta"] != 0
    }
    lock = bool(zero_artifacts or shape["max_abs_fractional_deviation"] > 1.0)
    return {
        "status": "janus-z4-master-pre-likelihood-lock-gate",
        "shape_report_gate_passed": True,
        "phase_guard_passed": shape["phase_guard_passed"],
        "amplitude_guard_passed": shape["amplitude_guard_passed"],
        "zero_crossing_artifacts": zero_artifacts,
        "max_abs_fractional_deviation": shape["max_abs_fractional_deviation"],
        "pre_likelihood_lock_active": lock,
        "lock_reason": "zero_crossing_or_large_fractional_shape_artifact" if lock else "none",
        "diagnostic_spectra_remain_available": True,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "revise_master_shape_regularization" if lock else "P0EFTJanusZ4MasterLikelihoodHandshakeGate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Pre-Likelihood Lock Gate",
        "",
        f"Pre-likelihood lock active: `{payload['pre_likelihood_lock_active']}`",
        f"Lock reason: `{payload['lock_reason']}`",
        f"Zero artifacts: `{payload['zero_crossing_artifacts']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
