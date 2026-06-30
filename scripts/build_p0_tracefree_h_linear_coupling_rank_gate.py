from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_linear_coupling_rank_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_linear_coupling_rank_gate.json")


def build_payload() -> dict:
    dimension = 4
    symmetric_rank = dimension * (dimension + 1) // 2
    trace_rank = 1
    covariant_stf_rank = symmetric_rank - trace_rank
    spatial_dimension = dimension - 1
    spatial_stf_rank = spatial_dimension * (spatial_dimension + 1) // 2 - 1

    candidates = [
        {
            "candidate": "Pi_TF",
            "role": "anisotropic stress tensor",
            "rank_source_status": "spatial/conditional",
            "covariant_stf_rank2_same_bridge": False,
            "source_derived": "conditional",
            "can_source_h_tf": "conditional",
            "blocker": "spatial STF after choosing u; needs source-derived bridge lift",
        },
        {
            "candidate": "Weyl_shear",
            "role": "Weyl/shear diagnostic",
            "rank_source_status": "diagnostic/conditional",
            "covariant_stf_rank2_same_bridge": "conditional",
            "source_derived": False,
            "can_source_h_tf": "conditional",
            "blocker": "diagnostic trace-free data is not a Janus source law",
        },
        {
            "candidate": "Vlasov_quadrupole",
            "role": "kinetic quadrupole moment",
            "rank_source_status": "hierarchy/conditional",
            "covariant_stf_rank2_same_bridge": "conditional",
            "source_derived": "conditional",
            "can_source_h_tf": "conditional",
            "blocker": "quadrupole evolution needs a closed Vlasov hierarchy",
        },
        {
            "candidate": "Phi_Sigma",
            "role": "BF/GL symmetric strain source",
            "rank_source_status": "source/action/conditional",
            "covariant_stf_rank2_same_bridge": "conditional",
            "source_derived": "conditional",
            "can_source_h_tf": "conditional",
            "blocker": "Janus source/action and same-bridge coupling are not closed",
        },
    ]
    rejected_routes = [
        {
            "route": "density_or_pressure_scalar",
            "accepted": False,
            "reason": "scalar data cannot contract with rank-2 Q_TF to source H_TF",
        },
        {
            "route": "determinant_trace",
            "accepted": False,
            "reason": "determinant/log-det trace is rank-1 trace data, not STF rank-2 data",
        },
        {
            "route": "residual_x_tf",
            "accepted": False,
            "reason": "X_TF must be source-derived, not introduced as a residual target",
        },
    ]
    return {
        "description": (
            "Bounded P0 gate for trace-free H/Q_TF linear action coupling rank "
            "and source requirements."
        ),
        "status": "tracefree-h-linear-coupling-rank-source-gate-open",
        "linear_coupling": "int Q_TF^{ab} X_TF_ab",
        "acceptance_rule": (
            "The coupling can source H_TF only if X_TF is covariant symmetric "
            "trace-free rank-2 data in the same bridge and source-derived."
        ),
        "dimension": dimension,
        "rank_count": {
            "symmetric_rank_4d": symmetric_rank,
            "trace_rank": trace_rank,
            "covariant_stf_rank_4d": covariant_stf_rank,
            "spatial_stf_rank_after_u_choice": spatial_stf_rank,
        },
        "x_tf_requirements": {
            "covariant": True,
            "symmetric_trace_free": True,
            "rank_2": True,
            "same_bridge": True,
            "source_derived": True,
            "residual_target_allowed": False,
        },
        "candidates": candidates,
        "rejected_routes": rejected_routes,
        "all_requirements_closed": False,
        "any_candidate_accepted": False,
        "scalars_can_source_h_tf": False,
        "determinant_trace_can_source_h_tf": False,
        "residual_x_tf_allowed": False,
        "source_selection_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not couple Q_TF to scalars or determinant trace as X_TF",
            "do not promote spatial Pi_TF to full covariant H_TF without a bridge lift",
            "do not treat Weyl/shear diagnostics as source equations",
            "do not close Vlasov quadrupole without its hierarchy",
            "do not insert residual X_TF to cancel the missing source",
        ],
        "verdict": (
            "The linear Q_TF X_TF action has the right form only after X_TF "
            "is a covariant STF rank-2, same-bridge, source-derived tensor. "
            "All listed routes remain conditional or rejected, so no prediction follows."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Linear Coupling Rank Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Linear coupling: `{payload['linear_coupling']}`",
        f"Acceptance rule: {payload['acceptance_rule']}",
        f"All requirements closed: {payload['all_requirements_closed']}",
        f"Any candidate accepted: {payload['any_candidate_accepted']}",
        f"Scalars can source H_TF: {payload['scalars_can_source_h_tf']}",
        f"Determinant trace can source H_TF: {payload['determinant_trace_can_source_h_tf']}",
        f"Residual X_TF allowed: {payload['residual_x_tf_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rank Count",
        "",
    ]
    for key, value in payload["rank_count"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## X_TF Requirements", ""])
    for key, value in payload["x_tf_requirements"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Candidates",
            "",
            "| candidate | rank/source status | same bridge rank-2 STF | source-derived | can source H_TF | blocker |",
            "|---|---|---:|---:|---:|---|",
        ]
    )
    for row in payload["candidates"]:
        lines.append(
            f"| {row['candidate']} | {row['rank_source_status']} | "
            f"{row['covariant_stf_rank2_same_bridge']} | {row['source_derived']} | "
            f"{row['can_source_h_tf']} | {row['blocker']} |"
        )
    lines.extend(
        [
            "",
            "## Rejected Routes",
            "",
            "| route | accepted | reason |",
            "|---|---:|---|",
        ]
    )
    for row in payload["rejected_routes"]:
        lines.append(f"| {row['route']} | {row['accepted']} | {row['reason']} |")
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
