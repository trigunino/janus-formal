from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_master_diagnostic_shape_report_v2_gate import (
    build_payload as shape_v2_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_pre_likelihood_lock_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_pre_likelihood_lock_v2_gate.json")


def build_payload() -> dict:
    shape = shape_v2_payload()
    lock_reasons = []
    if not shape["phase_guard_passed"]:
        lock_reasons.append("phase_guard_failed")
    if not shape["amplitude_guard_passed"]:
        lock_reasons.append("amplitude_guard_failed")
    if not shape["zero_artifact_guard_passed"]:
        lock_reasons.append("zero_artifacts_present")
    if not shape["nonoverlap_accounting_basis_declared"]:
        lock_reasons.append("nonoverlap_basis_missing")
    if not shape["overlapping_sum_forbidden"]:
        lock_reasons.append("overlapping_sum_not_forbidden")
    if not shape["reported_total_uses_one_highl_basis_only"]:
        lock_reasons.append("ambiguous_highl_basis")

    lock_active = bool(lock_reasons)
    return {
        "status": "janus-z4-master-pre-likelihood-lock-v2-gate",
        "shape_report_v2_gate_passed": shape["shape_report_v2_generated"],
        "phase_guard_passed": shape["phase_guard_passed"],
        "amplitude_guard_passed": shape["amplitude_guard_passed"],
        "zero_artifact_guard_passed": shape["zero_artifact_guard_passed"],
        "nonoverlap_accounting_basis_declared": shape["nonoverlap_accounting_basis_declared"],
        "overlapping_sum_forbidden": shape["overlapping_sum_forbidden"],
        "reported_total_uses_one_highl_basis_only": shape["reported_total_uses_one_highl_basis_only"],
        "max_abs_fractional_deviation": shape["max_abs_fractional_deviation"],
        "max_abs_peak_shift": shape["max_abs_peak_shift"],
        "zero_crossing_artifacts": shape["zero_crossing_artifacts"],
        "pre_likelihood_lock_active": lock_active,
        "pre_likelihood_lock_cleared": not lock_active,
        "lock_reasons": lock_reasons,
        "diagnostic_spectra_remain_available": True,
        "likelihood_handshake_allowed": not lock_active,
        "official_planck_trial_allowed": False,
        "likelihood_evaluation_allowed": False,
        "candidate_promotion_allowed": False,
        "next_required_gate": "P0EFTJanusZ4MasterActionNormalizationV2Gate"
        if not lock_active
        else "revise_master_v2_shape",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Pre-Likelihood Lock V2 Gate",
        "",
        f"Pre-likelihood lock active: `{payload['pre_likelihood_lock_active']}`",
        f"Pre-likelihood lock cleared: `{payload['pre_likelihood_lock_cleared']}`",
        f"Lock reasons: `{payload['lock_reasons']}`",
        f"Likelihood handshake allowed: `{payload['likelihood_handshake_allowed']}`",
        f"Official Planck allowed: `{payload['official_planck_trial_allowed']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
