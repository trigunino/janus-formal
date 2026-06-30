from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_relative_strain_action_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_relative_strain_action_gate.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_h_components = dimension * (dimension + 1) // 2
    determinant_trace_rank = 1
    tracefree_rank = symmetric_h_components - determinant_trace_rank

    derivative_requirements = [
        "Janus source/action provenance for the D H or D Q term",
        "boundary and gauge conditions for the variational problem",
        "curl integrability for the derivative strain connection",
        "mirror inverse compatibility",
        "same-L transport as the rest of the Janus stack",
        "ghost/stability acceptance for the quadratic branch",
    ]

    return {
        "description": (
            "Bounded P0 gate for a relative metric strain action as a trace-free "
            "H_TF/Q_TF source candidate."
        ),
        "status": "tracefree-h-relative-strain-action-gate-open",
        "depends_on": [
            "p0_tracefree_h_projector_gate",
            "p0_h_strain_action_variation_gate",
            "p0_relative_strain_q_derivative_omega_gate",
            "p0_action_ghost_stability_gate",
        ],
        "component_count": {
            "symmetric_h_components": symmetric_h_components,
            "determinant_trace_rank": determinant_trace_rank,
            "tracefree_h_rank": tracefree_rank,
        },
        "candidate": "relative H or Q action for the trace-free H_TF/Q_TF branch",
        "selection_rule": (
            "A relative H or Q action can select H_TF/Q_TF only if the Janus "
            "source/action gives an Euler-Lagrange equation projected onto the "
            "trace-free branch."
        ),
        "janus_tracefree_el_supplied": False,
        "source_action_selects_tracefree_branch": False,
        "ultralocal_vh": {
            "action_class": "ultralocal potential V(H)",
            "el_equation_type": "algebraic",
            "sufficient_for_tracefree_branch": False,
            "reason": "no D H or D Q provenance, boundary data, curl closure, or wave operator",
        },
        "derivative_action": {
            "action_classes": ["D H strain action", "D Q Frechet action"],
            "can_select_tracefree_branch": "conditional",
            "requirements": derivative_requirements,
            "requirements_closed": False,
        },
        "forbidden_routes": [
            "insert a fitted residual target for H_TF/Q_TF",
            "absorb trace-free dynamics into determinant trace or log det(H)",
        ],
        "residual_target_allowed": False,
        "determinant_trace_absorption_allowed": False,
        "accepted_as_prediction_input": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The trace-free relative strain action remains a candidate, not a "
            "selector. Ultralocal V(H) is algebraic and insufficient; derivative "
            "D H/D Q actions must first close source provenance, boundary/gauge, "
            "curl integrability, mirror inverse, same-L, and ghost/stability."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Relative Strain Action Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Candidate: {payload['candidate']}",
        f"Janus trace-free EL supplied: {payload['janus_tracefree_el_supplied']}",
        (
            "Source/action selects trace-free branch: "
            f"{payload['source_action_selects_tracefree_branch']}"
        ),
        f"Residual target allowed: {payload['residual_target_allowed']}",
        (
            "Determinant trace absorption allowed: "
            f"{payload['determinant_trace_absorption_allowed']}"
        ),
        f"Accepted as prediction input: {payload['accepted_as_prediction_input']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Component Count",
        "",
    ]
    for key, value in payload["component_count"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Selection Rule",
            "",
            payload["selection_rule"],
            "",
            "## Ultralocal V(H)",
            "",
        ]
    )
    for key, value in payload["ultralocal_vh"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Derivative Action Requirements", ""])
    lines.append(
        "- action classes: "
        f"`{', '.join(payload['derivative_action']['action_classes'])}`"
    )
    lines.append(
        "- can select trace-free branch: "
        f"`{payload['derivative_action']['can_select_tracefree_branch']}`"
    )
    lines.append(
        "- requirements closed: "
        f"`{payload['derivative_action']['requirements_closed']}`"
    )
    lines.extend(f"- {item}" for item in payload["derivative_action"]["requirements"])
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_routes"])
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
