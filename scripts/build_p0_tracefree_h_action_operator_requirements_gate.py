from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_action_operator_requirements_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_action_operator_requirements_gate.json")


def build_payload() -> dict:
    operator_requirements = [
        "source/action provenance for every H_TF/Q_TF operator term",
        "Euler-Lagrange operator explicitly projected with P_STF onto H_TF/Q_TF",
        "principal symbol and stability/ghost acceptance for physical modes",
        "boundary and gauge conditions for the variational problem",
        "curl/integrability closure for D H or D Q data",
        "mirror inverse compatibility under plus/minus exchange",
        "same-L transport compatibility with the Janus stack",
    ]
    rejected_shortcuts = [
        "fit or declare a target residual operator for H_TF/Q_TF",
        "absorb trace-free dynamics into determinant trace or log det(H)",
        "accept an ultralocal algebraic V(H) as the trace-free action operator",
    ]
    return {
        "description": (
            "Bounded P0 gate for trace-free H/Q_TF action-operator acceptance."
        ),
        "status": "tracefree-h-action-operator-requirements-open",
        "depends_on": [
            "p0_tracefree_h_projector_gate",
            "p0_tracefree_h_relative_strain_action_gate",
            "p0_action_ghost_stability_gate",
            "p0_janus_same_l_transport_stack_gate",
            "p0_nonmetricity_integrability_curl_gate",
            "p0_nonmetricity_mirror_inverse_gate",
        ],
        "accepted_route_rule": (
            "An accepted action route must derive an Euler-Lagrange operator and "
            "then project it with P_STF to the symmetric trace-free H_TF/Q_TF channel."
        ),
        "accepted_action_route_supplied": False,
        "stf_el_operator_required": True,
        "stf_el_operator_supplied": False,
        "operator_requirements": operator_requirements,
        "requirements_closed": False,
        "ultralocal_vh": {
            "action_class": "ultralocal algebraic V(H)",
            "operator_type": "algebraic",
            "sufficient_for_h_tf_q_tf": False,
            "reason": "no principal symbol, curl/integrability, boundary/gauge, or transport provenance",
        },
        "derivative_action": {
            "action_classes": ["D H action", "D Q action"],
            "acceptance": "conditional",
            "condition": "all operator requirements must close before use as an H_TF/Q_TF selector",
        },
        "rejected_shortcuts": rejected_shortcuts,
        "target_residual_operator_allowed": False,
        "determinant_trace_absorption_allowed": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "No trace-free H/Q_TF action operator is accepted yet. A derivative "
            "D H/D Q route remains conditional; ultralocal V(H), target residual "
            "operators, and determinant trace absorption are rejected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Action Operator Requirements Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Accepted action route supplied: {payload['accepted_action_route_supplied']}",
        f"STF EL operator required: {payload['stf_el_operator_required']}",
        f"STF EL operator supplied: {payload['stf_el_operator_supplied']}",
        f"Requirements closed: {payload['requirements_closed']}",
        f"Target residual operator allowed: {payload['target_residual_operator_allowed']}",
        (
            "Determinant trace absorption allowed: "
            f"{payload['determinant_trace_absorption_allowed']}"
        ),
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Accepted Route Rule",
        "",
        payload["accepted_route_rule"],
        "",
        "## Operator Requirements",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["operator_requirements"])
    lines.extend(["", "## Ultralocal V(H)", ""])
    for key, value in payload["ultralocal_vh"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Derivative Action", ""])
    derivative = payload["derivative_action"]
    lines.append(f"- action classes: `{', '.join(derivative['action_classes'])}`")
    lines.append(f"- acceptance: `{derivative['acceptance']}`")
    lines.append(f"- condition: {derivative['condition']}")
    lines.extend(["", "## Rejected Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["rejected_shortcuts"])
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
