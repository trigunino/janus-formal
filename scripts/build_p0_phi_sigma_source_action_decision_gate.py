from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_cartan_bf_gl_strain_selector_gate import (
    build_payload as build_cartan_bf_gate,
)
from scripts.build_p0_h_strain_action_variation_gate import (
    build_payload as build_h_strain_gate,
)
from scripts.build_p0_relative_metric_nonmetricity_sigma_dh_gate import (
    build_payload as build_nonmetricity_gate,
)
from scripts.build_p0_sigma_source_traceability_gap_gate import (
    build_payload as build_source_gap_gate,
)


REPORT_PATH = Path("outputs/reports/p0_phi_sigma_source_action_decision_gate.md")
JSON_PATH = Path("outputs/reports/p0_phi_sigma_source_action_decision_gate.json")


def build_payload() -> dict:
    source_gap = build_source_gap_gate()
    nonmetricity = build_nonmetricity_gate()
    cartan_bf = build_cartan_bf_gate()
    h_strain = build_h_strain_gate()
    source_phi_sigma_found = bool(source_gap["published_phi_sigma_source_found"])
    action_phi_sigma_found = bool(h_strain["source_derived_target_n_supplied"])
    return {
        "description": (
            "Bounded P0 decision gate for whether Phi_Sigma/N_alpha is source-derived, "
            "action-derived, or must be treated as a new axiom."
        ),
        "status": "phi-sigma-source-action-decision-open",
        "depends_on": [
            "p0_sigma_source_traceability_gap_gate",
            "p0_relative_metric_nonmetricity_sigma_dh_gate",
            "p0_cartan_bf_gl_strain_selector_gate",
            "p0_h_strain_action_variation_gate",
        ],
        "dependency_status": {
            "p0_sigma_source_traceability_gap_gate": source_gap["status"],
            "p0_relative_metric_nonmetricity_sigma_dh_gate": nonmetricity["status"],
            "p0_cartan_bf_gl_strain_selector_gate": cartan_bf["status"],
            "p0_h_strain_action_variation_gate": h_strain["status"],
        },
        "decision_branches": [
            {
                "branch": "source_derived_phi_sigma_or_n_alpha",
                "accepted": source_phi_sigma_found,
                "requires": "published/source-local equation explicitly gives Phi_Sigma or N_alpha before residual substitution",
                "current_blocker": "source traceability gate has not found published Phi_Sigma/N_alpha",
            },
            {
                "branch": "action_derived_phi_sigma_or_n_alpha",
                "accepted": action_phi_sigma_found,
                "requires": "accepted strain action varies H/L_geom and returns Phi_Sigma or N_alpha as an EL equation",
                "current_blocker": "H-strain action gate supplies no source-derived target N_alpha/Phi_Sigma",
            },
            {
                "branch": "new_axiom",
                "accepted": False,
                "requires": "explicit no-fit axiom with acceptance tests, scope limits, and no prediction release",
                "current_blocker": "new axiom risk is flagged but not adopted by this gate",
            },
        ],
        "source_phi_sigma_found": source_phi_sigma_found,
        "action_phi_sigma_found": action_phi_sigma_found,
        "any_branch_accepted": source_phi_sigma_found or action_phi_sigma_found,
        "new_axiom_risk": not (source_phi_sigma_found or action_phi_sigma_found),
        "new_axiom_adopted": False,
        "residual_cancellation_target_allowed": False,
        "observational_fit_allowed": False,
        "guardrails": [
            "do not use Phi_Sigma or N_alpha as a residual-cancel target",
            "do not fit Phi_Sigma/N_alpha to lensing, power, or other observations",
            "do not treat nonmetricity definition N_alpha := D_alpha H as source selection",
            "do not release predictions until source/action derivation or explicit axiom adoption is complete",
        ],
        "closure_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "No accepted source or action branch currently gives Phi_Sigma/N_alpha. "
            "The only remaining route is a clearly labeled new axiom, still risky and not adopted here."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Phi Sigma Source Action Decision Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source Phi_Sigma found: {payload['source_phi_sigma_found']}",
        f"Action Phi_Sigma found: {payload['action_phi_sigma_found']}",
        f"Any branch accepted: {payload['any_branch_accepted']}",
        f"New axiom risk: {payload['new_axiom_risk']}",
        f"New axiom adopted: {payload['new_axiom_adopted']}",
        f"Residual cancellation target allowed: {payload['residual_cancellation_target_allowed']}",
        f"Observational fit allowed: {payload['observational_fit_allowed']}",
        f"Closure allowed: {payload['closure_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Dependency Status",
        "",
    ]
    for name, status in payload["dependency_status"].items():
        lines.append(f"- {name}: {status}")
    lines.extend(["", "## Decision Branches", ""])
    lines.extend(
        (
            f"- {row['branch']}: accepted={row['accepted']}; "
            f"requires={row['requires']}; blocker={row['current_blocker']}"
        )
        for row in payload["decision_branches"]
    )
    lines.extend(["", "## Guardrails", ""])
    lines.extend(f"- {item}" for item in payload["guardrails"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
