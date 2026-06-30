from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_tracefree_h_frechet_log_adjoint_gate import (
    build_payload as build_frechet_log_adjoint,
)
from scripts.build_p0_tracefree_h_action_measure_variation_gate import (
    build_payload as build_action_measure_variation,
)
from scripts.build_p0_tracefree_h_projector_variation_dependency_gate import (
    build_payload as build_projector_variation_dependency,
)


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_quadratic_qtf_h_el_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_quadratic_qtf_h_el_gate.json")


def build_payload() -> dict:
    frechet = build_frechet_log_adjoint()
    measure = build_action_measure_variation()
    projector = build_projector_variation_dependency()
    derivation_steps = [
        {
            "step": "candidate_density",
            "formula": "L_Q2 = Tr(Q_TF^2)",
            "status": "formal candidate only",
        },
        {
            "step": "qtf_variation",
            "formula": "delta L_Q2 = 2 <Q_TF, delta Q_TF>",
            "status": "formal",
        },
        {
            "step": "h_chain",
            "formula": "delta Q_TF = P_STF(1/2 L_log,H[delta H]) + deltaP_STF terms",
            "status": "requires chain-rule gates",
        },
        {
            "step": "base_h_gradient",
            "formula": "G_H^base = L_log,H^*[P_STF(Q_TF)]",
            "status": "formal, up to measure/projector dependencies",
        },
        {
            "step": "homogeneous_el",
            "formula": "G_H^base + deltaP_STF + delta_mu terms = 0",
            "status": "not a Janus source equation",
        },
    ]
    blockers = [
        "Janus source/action provenance for L_Q2 is missing",
        "measure variation delta_mu must be fixed by B4vol/J/lapse branch",
        "projector variation terms remain open",
        "pure quadratic term is homogeneous and does not select nonzero S_TF^Janus",
        "coefficient/sign cannot be chosen by observational fit",
    ]
    return {
        "description": "Bounded P0 gate for the formal H Euler term induced by Tr(Q_TF^2).",
        "status": "tracefree-h-quadratic-qtf-h-el-gate-open",
        "target_channel": "H_TF/Q_TF",
        "candidate_density": "Tr(Q_TF^2)",
        "frechet_log_adjoint_ready": bool(frechet["source_provenance_closed"]),
        "action_measure_variation_closed": bool(measure["measure_variation_closed"]),
        "projector_dependency_closed": bool(projector["projector_dependency_closed"]),
        "formal_h_gradient_recorded": True,
        "homogeneous_only": True,
        "janus_source_action_provenance": False,
        "nonzero_source_selected": False,
        "accepted_as_closure": False,
        "coefficient_fit_allowed": False,
        "derivation_steps": derivation_steps,
        "blockers": blockers,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The quadratic Q_TF action now has a formal H-gradient, "
            "G_H^base=L_log,H^*[P_STF(Q_TF)]. This is algebraic progress, "
            "but the branch is homogeneous and not accepted as a Janus source."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Quadratic Q_TF H EL Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Candidate density: `{payload['candidate_density']}`",
        f"FrechetLog adjoint ready: {payload['frechet_log_adjoint_ready']}",
        f"Action measure variation closed: {payload['action_measure_variation_closed']}",
        f"Projector dependency closed: {payload['projector_dependency_closed']}",
        f"Formal H gradient recorded: {payload['formal_h_gradient_recorded']}",
        f"Homogeneous only: {payload['homogeneous_only']}",
        f"Janus source/action provenance: {payload['janus_source_action_provenance']}",
        f"Nonzero source selected: {payload['nonzero_source_selected']}",
        f"Accepted as closure: {payload['accepted_as_closure']}",
        f"Coefficient fit allowed: {payload['coefficient_fit_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Steps",
        "",
        "| step | formula | status |",
        "|---|---|---|",
    ]
    for row in payload["derivation_steps"]:
        lines.append(f"| {row['step']} | `{row['formula']}` | {row['status']} |")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
