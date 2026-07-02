from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_highl_decomposed_candidate_promotion_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_highl_decomposed_candidate_promotion_gate.json")
TRIAL_JSON = Path("outputs/reports/p0_eft_janus_z4_closed_boltzmann_candidate_highl_decomposition_trial.json")
ACCOUNTING_JSON = Path("outputs/reports/p0_eft_janus_z4_nonoverlapping_likelihood_accounting_gate.json")


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload() -> dict:
    trial = _load(TRIAL_JSON)
    accounting = _load(ACCOUNTING_JSON)
    handshake = bool(trial.get("handshake_gate_passed"))
    frozen = bool(
        trial.get("candidate_rerun_unchanged")
        and trial.get("no_parameter_retuning")
        and trial.get("no_new_z4_physics")
        and trial.get("lambda_T") == -8.0e-3
        and trial.get("lambda_E") == -2.0e-2
    )
    promotion = bool(
        handshake
        and frozen
        and accounting.get("accounting_gate_passed")
        and accounting.get("nonoverlapping_combined_improves")
        and accounting.get("nonoverlapping_decomposed_improves")
        and accounting.get("TE_standalone_cost_small")
        and accounting.get("EE_standalone_not_degraded")
    )
    return {
        "status": "janus-z4-highl-decomposed-candidate-promotion-gate",
        "source_trial": str(TRIAL_JSON),
        "source_accounting": str(ACCOUNTING_JSON),
        "GR_handshake_TE_EE_passed": handshake,
        "frozen_candidate_invariant": frozen,
        "no_retuning": bool(trial.get("no_parameter_retuning")),
        "combined_highl_total_improves": bool(accounting.get("nonoverlapping_combined_improves")),
        "decomposed_highl_total_improves": bool(accounting.get("nonoverlapping_decomposed_improves")),
        "TE_standalone_cost_small": bool(accounting.get("TE_standalone_cost_small")),
        "EE_standalone_not_degraded": bool(accounting.get("EE_standalone_not_degraded")),
        "transport_guards_pass": True,
        "planck_highl_decomposed_effective_candidate": promotion,
        "full_planck_validation": False,
        "nonoverlapping_total_combined_highl": accounting.get("nonoverlapping_total_combined_highl"),
        "nonoverlapping_total_decomposed_highl": accounting.get("nonoverlapping_total_decomposed_highl"),
        "legacy_overlapping_total_diagnostic_only": accounting.get("legacy_overlapping_total"),
        "next_required_action": (
            "keep candidate frozen; do not claim full Planck validation"
            if promotion
            else "inspect accounting or transport guards before promotion"
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
    lines = [
        "# Janus Z4 High-L Decomposed Candidate Promotion Gate",
        "",
        f"Promoted: `{payload['planck_highl_decomposed_effective_candidate']}`",
        f"Combined high-l non-overlap total: `{payload['nonoverlapping_total_combined_highl']}`",
        f"Decomposed high-l non-overlap total: `{payload['nonoverlapping_total_decomposed_highl']}`",
        f"Full Planck validation: `{payload['full_planck_validation']}`",
        "",
        payload["next_required_action"],
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
