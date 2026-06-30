from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_irrep_source_requirements_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_irrep_source_requirements_gate.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_rank2_components = dimension * (dimension + 1) // 2
    trace_components = 1
    stf_rank2_components = symmetric_rank2_components - trace_components

    scalar_routes = [
        {
            "source": "rho",
            "type": "scalar density",
            "stf_projection": "P_STF(rho g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
        {
            "source": "p",
            "type": "scalar pressure",
            "stf_projection": "P_STF(p g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
        {
            "source": "B4vol",
            "type": "4-volume scalar",
            "stf_projection": "P_STF(B4vol g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
        {
            "source": "Q_det",
            "type": "determinant scalar",
            "stf_projection": "P_STF(Q_det g_ab)=0",
            "selects_h_tf_q_tf": False,
        },
    ]
    non_tensor_routes = [
        {
            "source": "vectors",
            "blocker": "do not select a covariant STF rank-2 tensor without a derivative/gauge/action law",
            "selects_h_tf_q_tf": False,
        },
        {
            "source": "gradients",
            "blocker": "do not select a covariant STF rank-2 tensor without a derivative/gauge/action law",
            "selects_h_tf_q_tf": False,
        },
    ]
    conditional_routes = [
        {
            "source": "spatial_Pi_TF",
            "status": "conditional",
            "requirement": "requires congruence and gauge before it selects a 4D bridge tensor",
        },
        {
            "source": "Weyl_shear",
            "status": "conditional",
            "requirement": "requires source/field equation plus gauge and boundary branch",
        },
        {
            "source": "Vlasov_quadrupole",
            "status": "conditional",
            "requirement": "requires closed Janus kinetic action/source and moment hierarchy",
        },
        {
            "source": "relative_H_Q_action",
            "status": "conditional",
            "requirement": "requires accepted action whose EL equation projects to H_TF/Q_TF",
        },
        {
            "source": "BF_GL_Phi_Sigma",
            "status": "conditional",
            "requirement": "requires Janus BF/GL source equation, gauge, integrability, and stability",
        },
    ]

    return {
        "description": (
            "Bounded P0 gate for irreducible source requirements of the "
            "trace-free H_TF/Q_TF channel."
        ),
        "status": "tracefree-h-irrep-source-requirements-open",
        "dimension": dimension,
        "component_count": {
            "symmetric_rank2_components": symmetric_rank2_components,
            "trace_components": trace_components,
            "stf_rank2_components": stf_rank2_components,
        },
        "irreducible_source_requirement": (
            "A 4D H_TF/Q_TF source must be a symmetric trace-free rank-2 "
            "tensor in the same receiver/source bridge."
        ),
        "same_receiver_source_bridge_required": True,
        "covariant_stf_rank2_required": True,
        "scalar_routes": scalar_routes,
        "non_tensor_routes": non_tensor_routes,
        "conditional_routes": conditional_routes,
        "scalar_stf_projection_zero": True,
        "vectors_gradients_select_covariant_stf_without_law": False,
        "spatial_pi_tf_selects_only_after_congruence_gauge": True,
        "conditional_routes_closed": False,
        "residual_fit_allowed": False,
        "residual_fit_used": False,
        "source_selection_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not promote scalar trace data rho, p, B4vol, or Q_det into H_TF/Q_TF",
            "do not promote vectors or gradients without a derivative/gauge/action law",
            "do not accept spatial Pi_TF without congruence and gauge bridge data",
            "do not use residual fitting as source selection",
        ],
        "verdict": (
            "No irreducible trace-free source is accepted. Scalars project to "
            "zero in the STF channel, vectors/gradients underselect the tensor, "
            "and all tensor-looking routes remain conditional."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Irrep Source Requirements Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Dimension: {payload['dimension']}",
        f"Same receiver/source bridge required: {payload['same_receiver_source_bridge_required']}",
        f"Covariant STF rank-2 required: {payload['covariant_stf_rank2_required']}",
        f"Scalar STF projection zero: {payload['scalar_stf_projection_zero']}",
        (
            "Vectors/gradients select covariant STF without law: "
            f"{payload['vectors_gradients_select_covariant_stf_without_law']}"
        ),
        (
            "Spatial Pi_TF selects only after congruence/gauge: "
            f"{payload['spatial_pi_tf_selects_only_after_congruence_gauge']}"
        ),
        f"Residual fit allowed: {payload['residual_fit_allowed']}",
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
            "## Requirement",
            "",
            payload["irreducible_source_requirement"],
            "",
            "## Scalar Routes",
            "",
            "| source | type | STF projection | selects H_TF/Q_TF |",
            "|---|---|---|---:|",
        ]
    )
    for row in payload["scalar_routes"]:
        lines.append(
            f"| {row['source']} | {row['type']} | `{row['stf_projection']}` | "
            f"{row['selects_h_tf_q_tf']} |"
        )
    lines.extend(
        [
            "",
            "## Vectors And Gradients",
            "",
            "| source | blocker | selects H_TF/Q_TF |",
            "|---|---|---:|",
        ]
    )
    for row in payload["non_tensor_routes"]:
        lines.append(f"| {row['source']} | {row['blocker']} | {row['selects_h_tf_q_tf']} |")
    lines.extend(
        [
            "",
            "## Conditional Tensor Routes",
            "",
            "| source | status | requirement |",
            "|---|---|---|",
        ]
    )
    for row in payload["conditional_routes"]:
        lines.append(f"| {row['source']} | {row['status']} | {row['requirement']} |")
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
