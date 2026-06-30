from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_scalar_vector_no_go_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_scalar_vector_no_go_gate.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_rank2_components = dimension * (dimension + 1) // 2
    trace_components = 1
    stf_rank2_components = symmetric_rank2_components - trace_components

    scalar_sources = [
        {
            "source": "rho",
            "metric_term": "rho g_ab",
            "stf_projection": "P_STF(rho g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
        {
            "source": "p",
            "metric_term": "p g_ab",
            "stf_projection": "P_STF(p g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
        {
            "source": "B4vol",
            "metric_term": "B4vol g_ab",
            "stf_projection": "P_STF(B4vol g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
        {
            "source": "Q_det",
            "metric_term": "Q_det g_ab",
            "stf_projection": "P_STF(Q_det g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
    ]
    vector_gradient_routes = [
        {
            "route": "single_vector",
            "candidate": "v_a",
            "blocker": (
                "one vector cannot covariantly select a symmetric trace-free "
                "rank-2 source without extra metric/projector/gauge/action law"
            ),
            "selects_h_tf_q_tf": False,
        },
        {
            "route": "single_gradient",
            "candidate": "nabla_a phi",
            "blocker": (
                "one gradient cannot covariantly select a symmetric trace-free "
                "rank-2 source without extra metric/projector/gauge/action law"
            ),
            "selects_h_tf_q_tf": False,
        },
    ]
    derivative_ansatz_routes = [
        {
            "route": "hessian_stf",
            "candidate": "P_STF(nabla_a nabla_b phi)",
            "classification": "derivative ansatz",
            "requirement": "Janus source/action plus boundary/gauge",
            "accepted": False,
        },
        {
            "route": "gradient_square_stf",
            "candidate": "P_STF(nabla_a phi nabla_b phi)",
            "classification": "derivative ansatz",
            "requirement": "Janus source/action plus boundary/gauge",
            "accepted": False,
        },
    ]

    return {
        "description": (
            "Bounded P0 scalar/vector low-derivative no-go gate for "
            "H_TF/Q_TF source selection."
        ),
        "status": "tracefree-h-scalar-vector-low-derivative-no-go-open",
        "dimension": dimension,
        "component_count": {
            "symmetric_rank2_components": symmetric_rank2_components,
            "trace_components": trace_components,
            "stf_rank2_components": stf_rank2_components,
        },
        "target_source": "symmetric trace-free rank-2 H_TF/Q_TF source",
        "scalar_sources": scalar_sources,
        "vector_gradient_routes": vector_gradient_routes,
        "derivative_ansatz_routes": derivative_ansatz_routes,
        "local_scalars_produce_trace_only_metric_terms": True,
        "scalar_stf_projection_zero": True,
        "single_vector_gradient_covariant_stf_selector": False,
        "derivative_ansatz_accepted": False,
        "janus_source_action_required_for_derivative_ansatz": True,
        "boundary_gauge_required_for_derivative_ansatz": True,
        "residual_fit_allowed": False,
        "residual_fit_used": False,
        "determinant_trace_absorption_allowed": False,
        "source_selection_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not promote rho, p, B4vol, or Q_det trace terms into H_TF/Q_TF",
            "do not absorb the determinant trace into the trace-free source",
            "do not use a single vector or gradient as a covariant STF rank-2 selector",
            "do not accept Hessian or gradient-square ansatz without Janus source/action plus boundary/gauge",
            "do not use residual fitting as source selection",
        ],
        "verdict": (
            "Local scalar sources are trace-only and have zero STF projection. "
            "Single vectors/gradients underselect a covariant STF rank-2 source, "
            "while Hessian and gradient-square constructions remain unaccepted "
            "derivative ansatze until a Janus source/action and boundary/gauge "
            "law are supplied."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Scalar/Vector Low-Derivative No-Go Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Target source: {payload['target_source']}",
        (
            "Local scalars produce trace-only metric terms: "
            f"{payload['local_scalars_produce_trace_only_metric_terms']}"
        ),
        f"Scalar STF projection zero: {payload['scalar_stf_projection_zero']}",
        (
            "Single vector/gradient covariant STF selector: "
            f"{payload['single_vector_gradient_covariant_stf_selector']}"
        ),
        f"Derivative ansatz accepted: {payload['derivative_ansatz_accepted']}",
        f"Residual fit allowed: {payload['residual_fit_allowed']}",
        (
            "Determinant trace absorption allowed: "
            f"{payload['determinant_trace_absorption_allowed']}"
        ),
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
            "## Scalar Sources",
            "",
            "| source | metric term | STF projection | selects H_TF/Q_TF |",
            "|---|---|---|---:|",
        ]
    )
    for row in payload["scalar_sources"]:
        lines.append(
            f"| {row['source']} | `{row['metric_term']}` | "
            f"`{row['stf_projection']}` | {row['selects_h_tf_q_tf']} |"
        )
    lines.extend(
        [
            "",
            "## Single Vector/Gradient Routes",
            "",
            "| route | candidate | blocker | selects H_TF/Q_TF |",
            "|---|---|---|---:|",
        ]
    )
    for row in payload["vector_gradient_routes"]:
        lines.append(
            f"| {row['route']} | `{row['candidate']}` | "
            f"{row['blocker']} | {row['selects_h_tf_q_tf']} |"
        )
    lines.extend(
        [
            "",
            "## Derivative Ansatz Routes",
            "",
            "| route | candidate | classification | requirement | accepted |",
            "|---|---|---|---|---:|",
        ]
    )
    for row in payload["derivative_ansatz_routes"]:
        lines.append(
            f"| {row['route']} | `{row['candidate']}` | "
            f"{row['classification']} | {row['requirement']} | {row['accepted']} |"
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
