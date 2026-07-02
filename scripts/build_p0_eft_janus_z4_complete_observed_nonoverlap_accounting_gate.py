from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_observed_nonoverlap_accounting_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_complete_observed_nonoverlap_accounting_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_complete_observed_planck_diagnostic_gate.json")


def _load_trial() -> dict:
    return json.loads(TRIAL_JSON.read_text(encoding="utf-8")) if TRIAL_JSON.exists() else {}


def build_payload() -> dict:
    trial = _load_trial()
    executed = bool(trial.get("run_observed_executed"))
    combined = trial.get("nonoverlapping_total_combined_highl")
    decomposed = trial.get("nonoverlapping_total_decomposed_highl")
    available_combined = trial.get("available_nonoverlap_highl_lensing_combined")
    available_decomposed = trial.get("available_nonoverlap_highl_lensing_decomposed")
    low_l_nonfinite = bool(trial.get("low_l_rejected_or_nonfinite"))
    clean = bool(executed and combined is not None and decomposed is not None and combined < 0.0 and decomposed < 0.0)
    finite_available_rejected = bool(
        executed
        and available_combined is not None
        and available_decomposed is not None
        and (available_combined > 0.0 or available_decomposed > 0.0)
    )
    rejected = bool(executed and (low_l_nonfinite or finite_available_rejected or (combined is not None and decomposed is not None and not clean)))
    return {
        "status": "janus-z4-complete-observed-nonoverlap-accounting-gate",
        "source_trial": str(TRIAL_JSON),
        "observed_trial_executed": executed,
        "delta_chi2_by_channel": trial.get("delta_chi2_by_channel", {}),
        "legacy_overlapping_total": trial.get("legacy_overlapping_total"),
        "legacy_overlapping_total_diagnostic_only": True,
        "nonoverlapping_total_combined_highl": combined,
        "nonoverlapping_total_decomposed_highl": decomposed,
        "available_nonoverlap_highl_lensing_combined": available_combined,
        "available_nonoverlap_highl_lensing_decomposed": available_decomposed,
        "low_l_rejected_or_nonfinite": low_l_nonfinite,
        "finite_available_highl_lensing_rejected": finite_available_rejected,
        "nonoverlap_accounting_performed": executed,
        "clean_nonoverlap_result": clean,
        "observed_complete_solver_branch_rejected": rejected,
        "candidate_promotion_allowed": False,
        "observational_claim_allowed": False,
        "full_planck_validation": False,
        "next_required_gate": "complete_observed_failure_map" if rejected else "run_observed_diagnostic_trial" if not executed else "stability_gate",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join([
            "# Janus Z4 Complete Observed Non-Overlap Accounting Gate",
            "",
            f"Observed trial executed: `{payload['observed_trial_executed']}`",
            f"Combined non-overlap: `{payload['nonoverlapping_total_combined_highl']}`",
            f"Decomposed non-overlap: `{payload['nonoverlapping_total_decomposed_highl']}`",
            f"Available high-l+lensing combined: `{payload['available_nonoverlap_highl_lensing_combined']}`",
            f"Available high-l+lensing decomposed: `{payload['available_nonoverlap_highl_lensing_decomposed']}`",
            f"Low-l non-finite: `{payload['low_l_rejected_or_nonfinite']}`",
            f"Branch rejected: `{payload['observed_complete_solver_branch_rejected']}`",
            f"Full Planck validation: `{payload['full_planck_validation']}`",
            "",
        ]),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
