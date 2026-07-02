from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_candidate_local_nuisance_profiling_gate import (
    BASES,
    SENSITIVITY_JSON,
    TRIAL_JSON,
    _load,
    _profile,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_safe_nuisance_profiling_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_safe_nuisance_profiling_gate.json")
PROBLEM_NUISANCES = {"calib_217T", "gal545_A_217"}


def _basis_profile(
    components: tuple[str, ...],
    baseline_path: str,
    candidate_path: str,
    **kwargs,
) -> dict:
    gr = _profile(components, baseline_path, **kwargs)
    cand = _profile(components, candidate_path, **kwargs)
    delta = float(cand["chi2"] - gr["chi2"])
    return {
        "GR_profile": gr,
        "candidate_profile": cand,
        "delta_chi2": delta,
        "GR_boundary_hits": gr["nuisance_boundary_hits"],
        "candidate_boundary_hits": cand["nuisance_boundary_hits"],
        "same_boundary_hits": sorted(gr["nuisance_boundary_hits"]) == sorted(cand["nuisance_boundary_hits"]),
        "boundary_safe": not gr["nuisance_boundary_hits"] and not cand["nuisance_boundary_hits"],
        "gain_survives": delta < 0.0,
    }


def _run_policy(policy: str, baseline_path: str, candidate_path: str) -> dict:
    if policy == "profile_all_nuisances":
        kwargs = {}
    elif policy == "boundary_guarded":
        kwargs = {"boundary_guard_epsilon": 1.0e-2}
    elif policy == "problem_nuisances_fixed":
        kwargs = {"fixed_names": PROBLEM_NUISANCES}
    elif policy == "prior_penalized":
        kwargs = {"prior_penalty_weight": 1.0}
    else:
        raise ValueError(policy)
    rows = {
        basis: _basis_profile(components, baseline_path, candidate_path, **kwargs)
        for basis, components in BASES.items()
    }
    return {
        "policy": policy,
        "rows": rows,
        "combined_gain": rows["combined_highl"]["delta_chi2"],
        "decomposed_gain": rows["decomposed_highl"]["delta_chi2"],
        "combined_gain_survives": rows["combined_highl"]["gain_survives"],
        "decomposed_gain_survives": rows["decomposed_highl"]["gain_survives"],
        "boundary_safe_profile_found": all(row["boundary_safe"] for row in rows.values()),
    }


def build_payload(run_official: bool = False) -> dict:
    trial = _load(TRIAL_JSON)
    sensitivity = _load(SENSITIVITY_JSON)
    baseline_path = trial.get("baseline_spectra_path", "")
    candidate_path = trial.get("candidate_spectra_path", "")
    policies = (
        "profile_all_nuisances",
        "boundary_guarded",
        "problem_nuisances_fixed",
        "prior_penalized",
    )
    policy_rows = {policy: _run_policy(policy, baseline_path, candidate_path) for policy in policies} if run_official else {}
    robust_policies = [
        name
        for name, row in policy_rows.items()
        if row["boundary_safe_profile_found"]
        and row["combined_gain_survives"]
        and row["decomposed_gain_survives"]
    ]
    return {
        "status": "janus-z4-boundary-safe-nuisance-profiling-gate",
        "source_trial": str(TRIAL_JSON),
        "source_sensitivity": str(SENSITIVITY_JSON),
        "run_official_requested": run_official,
        "lambda_T": trial.get("lambda_T"),
        "lambda_E": trial.get("lambda_E"),
        "lambda_frozen": trial.get("lambda_T") == -8.0e-3 and trial.get("lambda_E") == -2.0e-2,
        "no_new_physics": bool(trial.get("no_new_z4_physics")),
        "non_overlap_accounting_only": True,
        "same_nuisance_rule_for_GR_and_candidate": True,
        "requires_sensitivity_gate": bool(sensitivity.get("gate_passed")),
        "problem_nuisances": sorted(PROBLEM_NUISANCES),
        "policy_rows": policy_rows,
        "robust_boundary_safe_policies": robust_policies,
        "boundary_safe_local_profiled_candidate": bool(robust_policies),
        "profiled_planck_candidate": False,
        "full_planck_validation": False,
        "gate_passed": bool(
            run_official
            and trial.get("lambda_T") == -8.0e-3
            and trial.get("lambda_E") == -2.0e-2
            and trial.get("no_new_z4_physics")
            and bool(robust_policies)
        ),
    }


def write_reports(run_official: bool = True) -> dict:
    payload = build_payload(run_official=run_official)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Boundary-Safe Nuisance Profiling Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Boundary-safe local profiled candidate: `{payload['boundary_safe_local_profiled_candidate']}`",
        f"Robust policies: `{payload['robust_boundary_safe_policies']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
    ]
    for name, row in payload["policy_rows"].items():
        lines.append(
            f"- `{name}`: combined `{row['combined_gain']}`, decomposed `{row['decomposed_gain']}`, "
            f"boundary safe `{row['boundary_safe_profile_found']}`"
        )
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(run_official=True), indent=2))
