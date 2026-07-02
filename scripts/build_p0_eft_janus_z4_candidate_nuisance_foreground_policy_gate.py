from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_nuisance_foreground_policy_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_candidate_nuisance_foreground_policy_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.json")
PROMOTION_JSON = Path("outputs/reports/p0_eft_janus_z4_highl_decomposed_candidate_promotion_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _nuisance_counts(trial: dict, branch: str) -> dict:
    channels = trial.get(branch, {}).get("channels", {})
    return {name: row.get("sampled_nuisance_count") for name, row in channels.items()}


def build_payload() -> dict:
    trial = _load(TRIAL_JSON)
    promotion = _load(PROMOTION_JSON)
    baseline_counts = _nuisance_counts(trial, "baseline")
    candidate_counts = _nuisance_counts(trial, "candidate")
    same_counts = baseline_counts == candidate_counts and bool(baseline_counts)
    highl_counts_present = all(name in baseline_counts for name in ("highl_TT", "highl_TE", "highl_EE", "highl_TTTEEE"))
    return {
        "status": "janus-z4-candidate-nuisance-foreground-policy-gate",
        "source_trial": str(TRIAL_JSON),
        "source_promotion": str(PROMOTION_JSON),
        "planck_highl_decomposed_effective_candidate": bool(
            promotion.get("planck_highl_decomposed_effective_candidate")
        ),
        "same_nuisance_vector_for_GR_and_candidate": same_counts,
        "baseline_sampled_nuisance_counts": baseline_counts,
        "candidate_sampled_nuisance_counts": candidate_counts,
        "foreground_parameters_declared_by_clik_wrappers": highl_counts_present,
        "calibration_parameters_declared_by_clik_wrappers": highl_counts_present,
        "foreground_parameters_fixed": False,
        "calibration_parameters_fixed": False,
        "component_reference_nuisance_used": True,
        "global_nuisance_profiling_performed": False,
        "candidate_result_conditional_on_component_reference_nuisance": True,
        "candidate_status": "fixed_nuisance_effective_candidate",
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "policy_gate_passed": bool(
            promotion.get("planck_highl_decomposed_effective_candidate")
            and same_counts
            and highl_counts_present
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Candidate Nuisance/Foreground Policy Gate",
        "",
        f"Gate passed: `{payload['policy_gate_passed']}`",
        f"Candidate status: `{payload['candidate_status']}`",
        f"Profiled Planck candidate: `{payload['profiled_planck_candidate']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
        "The candidate is conditional on component reference nuisance handling.",
        "No global nuisance profiling has been performed.",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
