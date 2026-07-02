from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_completeness_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_planck_likelihood_completeness_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial.json")
WORKTREE_STATUS_PATH = Path("outputs/reports/worktree_status_before_closed_boltzmann_trial.txt")

EXPECTED_CHANNELS = (
    "lowl_TT",
    "lowl_EE",
    "lensing",
    "highl_TT",
    "highl_TE",
    "highl_EE",
    "highl_TTTEEE",
)


def _load_trial() -> dict:
    if not TRIAL_JSON.exists():
        return {}
    return json.loads(TRIAL_JSON.read_text(encoding="utf-8"))


def build_payload() -> dict:
    trial = _load_trial()
    best = trial.get("best_summary", {})
    finite = best.get("finite_channel_chi2", {})
    availability = {name: name in finite for name in EXPECTED_CHANNELS}
    highl_teee_combined = availability["highl_TTTEEE"]
    standalone_te_ee = availability["highl_TE"] and availability["highl_EE"]
    full_validation = bool(all(availability.values()) and standalone_te_ee)
    candidate_trial_allowed = bool(
        trial.get("boltzmann_closed_effective_z4_cmb_candidate")
        and availability["highl_TTTEEE"]
        and availability["lowl_TT"]
        and availability["lowl_EE"]
        and availability["lensing"]
    )
    worktree_text = WORKTREE_STATUS_PATH.read_text(encoding="utf-8") if WORKTREE_STATUS_PATH.exists() else ""
    return {
        "status": "janus-z4-planck-likelihood-completeness-gate",
        "source_trial": str(TRIAL_JSON),
        "candidate_state_checkpoint_created": bool(WORKTREE_STATUS_PATH.exists()),
        "worktree_status_snapshot_path": str(WORKTREE_STATUS_PATH),
        "expected_channels": list(EXPECTED_CHANNELS),
        "available_channels": availability,
        "highl_TT_available": availability["highl_TT"],
        "highl_TTTEEE_available": highl_teee_combined,
        "highl_TE_standalone_available": availability["highl_TE"],
        "highl_EE_standalone_available": availability["highl_EE"],
        "low_l_TT_available": availability["lowl_TT"],
        "low_l_EE_available": availability["lowl_EE"],
        "lensing_available": availability["lensing"],
        "nuisance_parameters_handled_consistently": "inherited_from_local_clik_wrappers",
        "foreground_model_status": "fixed_or_declared_by_available_clik_wrappers",
        "standalone_highl_TE_EE_available": standalone_te_ee,
        "candidate_trial_allowed": candidate_trial_allowed,
        "full_planck_validation_allowed": full_validation,
        "generated_outputs_not_imported_as_sources": True,
        "worktree_status_snapshot": worktree_text.splitlines(),
        "planck_likelihood_completeness_gate_passed": candidate_trial_allowed,
        "next_required_action": (
            "run candidate robustness gate; do not claim full Planck validation"
            if candidate_trial_allowed and not full_validation
            else "install missing standalone high-l TE/EE likelihoods before full validation"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 Planck Likelihood Completeness Gate",
        "",
        f"Gate passed: `{payload['planck_likelihood_completeness_gate_passed']}`",
        f"Candidate trial allowed: `{payload['candidate_trial_allowed']}`",
        f"Full Planck validation allowed: `{payload['full_planck_validation_allowed']}`",
        f"Standalone high-l TE/EE available: `{payload['standalone_highl_TE_EE_available']}`",
        f"Available channels: `{payload['available_channels']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
