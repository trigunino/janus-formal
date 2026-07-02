from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_nonoverlap_accounting_v2_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_master_observed_nonoverlap_accounting_v2_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_master_observed_planck_diagnostic_trial_v2_gate.json")


def _load_trial() -> dict:
    return json.loads(TRIAL_JSON.read_text(encoding="utf-8")) if TRIAL_JSON.exists() else {}


def build_payload() -> dict:
    trial = _load_trial()
    executed = bool(trial.get("run_observed_executed"))
    deltas = trial.get("delta_chi2_by_channel", {})
    combined = trial.get("nonoverlapping_total_combined_highl")
    decomposed = trial.get("nonoverlapping_total_decomposed_highl")
    clean = bool(executed and combined is not None and decomposed is not None and combined < 0.0 and decomposed < 0.0)
    rejected = bool(executed and combined is not None and decomposed is not None and not clean)
    return {
        "status": "janus-z4-master-observed-nonoverlap-accounting-v2-gate",
        "source_trial": str(TRIAL_JSON),
        "observed_trial_executed": executed,
        "delta_chi2_by_channel": deltas,
        "legacy_overlapping_total": trial.get("legacy_overlapping_total"),
        "nonoverlapping_total_combined_highl": combined,
        "nonoverlapping_total_decomposed_highl": decomposed,
        "nonoverlap_accounting_performed": executed,
        "clean_nonoverlap_result": clean,
        "observed_master_v2_branch_rejected": rejected,
        "rejection_reason": "positive_nonoverlap_chi2" if rejected else "none" if clean else "observed_trial_not_executed",
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "P0EFTJanusZ4MasterObservedFailureMapV2Gate"
        if rejected
        else "run_observed_diagnostic_trial_v2"
        if not executed
        else "P0EFTJanusZ4MasterCandidateStabilityV2Gate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Master Observed Non-Overlap Accounting V2 Gate",
        "",
        f"Observed trial executed: `{payload['observed_trial_executed']}`",
        f"Combined non-overlap: `{payload['nonoverlapping_total_combined_highl']}`",
        f"Decomposed non-overlap: `{payload['nonoverlapping_total_decomposed_highl']}`",
        f"Branch rejected: `{payload['observed_master_v2_branch_rejected']}`",
        f"Reason: `{payload['rejection_reason']}`",
        f"Next gate: `{payload['next_required_gate']}`",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
