from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_linear_xtf_provenance_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_linear_xtf_provenance_gate.json")


def build_payload() -> dict:
    candidates = [
        {
            "candidate": "Janus coupled stress STF",
            "role": "STF projection of verified coupled source tensor",
            "source_derived_covariant_stf_rank2_same_bridge": False,
            "accepted": False,
            "blocker": "M15/M30 give coupled tensor source, but not same-bridge H-variation/X_TF derivation",
        },
        {
            "candidate": "Pi_TF",
            "role": "anisotropic stress candidate",
            "source_derived_covariant_stf_rank2_same_bridge": False,
            "accepted": False,
            "blocker": "needs matter variation plus congruence lift to the same bridge",
        },
        {
            "candidate": "Weyl/shear",
            "role": "trace-free curvature/kinematic diagnostic",
            "source_derived_covariant_stf_rank2_same_bridge": False,
            "accepted": False,
            "blocker": "diagnostic unless a Janus field equation makes it the source",
        },
        {
            "candidate": "Vlasov quadrupole",
            "role": "kinetic trace-free second moment",
            "source_derived_covariant_stf_rank2_same_bridge": False,
            "accepted": False,
            "blocker": "needs closed Janus Vlasov moment hierarchy",
        },
        {
            "candidate": "Phi_Sigma/N_alpha",
            "role": "Janus strain/connection source candidate",
            "source_derived_covariant_stf_rank2_same_bridge": False,
            "accepted": False,
            "blocker": "needs Janus action/source equation",
        },
        {
            "candidate": "BF/GL multiplier",
            "role": "constraint multiplier candidate",
            "source_derived_covariant_stf_rank2_same_bridge": False,
            "accepted": False,
            "blocker": "needs a constraint action that derives the multiplier source",
        },
    ]
    dependency_terms = [
        {
            "dependency": "H",
            "term": "int Q_TF^{ab} (delta X_TF_ab / delta H_cd) delta H_cd",
            "include_if": "X_TF depends on H",
        },
        {
            "dependency": "L",
            "term": "int Q_TF^{ab} (delta X_TF_ab / delta L^c_d) delta L^c_d",
            "include_if": "X_TF depends on L",
        },
        {
            "dependency": "phi",
            "term": "int Q_TF^{ab} (delta X_TF_ab / delta phi^c) delta phi^c",
            "include_if": "X_TF depends on phi",
        },
        {
            "dependency": "matter",
            "term": "int Q_TF^{ab} delta_matter X_TF_ab",
            "include_if": "X_TF depends on matter variables",
        },
    ]
    rejected_routes = [
        {
            "route": "residual_X_TF",
            "accepted": False,
            "reason": "X_TF must be source-derived, not a residual cancellation target",
        },
        {
            "route": "scalars",
            "accepted": False,
            "reason": "scalars cannot supply covariant STF rank-2 data",
        },
        {
            "route": "determinant_trace",
            "accepted": False,
            "reason": "determinant/log-det data is trace/volume data, not X_TF",
        },
    ]
    return {
        "description": (
            "Bounded P0 provenance gate for a trace-free H/Q_TF linear "
            "X_TF coupling."
        ),
        "status": "tracefree-h-linear-xtf-provenance-gate-open",
        "linear_coupling": "int Q_TF^{ab} X_TF_ab",
        "acceptance_rule": (
            "X_TF must be source-derived covariant STF rank-2 same-bridge data."
        ),
        "variation_rule": (
            "delta S includes int delta Q_TF^{ab} X_TF_ab plus int Q_TF^{ab} delta X_TF_ab; "
            "expand delta X_TF over H, L, phi, and matter dependencies when present."
        ),
        "x_tf_requirements": {
            "source_derived": True,
            "covariant": True,
            "stf": True,
            "rank_2": True,
            "same_bridge": True,
            "dependency_terms_included_if_present": True,
        },
        "candidates": candidates,
        "dependency_terms": dependency_terms,
        "rejected_routes": rejected_routes,
        "all_candidates_pass_gate": False,
        "any_candidate_accepted": False,
        "xtf_dependencies_can_be_ignored": False,
        "residual_xtf_allowed": False,
        "scalars_allowed": False,
        "determinant_trace_allowed": False,
        "source_selection_closed": False,
        "physics_closed": False,
        "prediction": False,
        "prediction_ready": False,
        "guardrails": [
            "do not introduce residual X_TF as a provenance source",
            "do not replace X_TF by scalar or determinant trace data",
            "do not omit H/L/phi/matter dependency terms when varying X_TF",
            "require same-bridge covariant STF rank-2 source derivation before prediction",
        ],
        "verdict": (
            "No X_TF candidate currently passes provenance. The linear Q_TF X_TF "
            "coupling remains open and non-predictive."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Linear X_TF Provenance Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Linear coupling: `{payload['linear_coupling']}`",
        f"Acceptance rule: {payload['acceptance_rule']}",
        f"Variation rule: {payload['variation_rule']}",
        f"All candidates pass gate: {payload['all_candidates_pass_gate']}",
        f"Any candidate accepted: {payload['any_candidate_accepted']}",
        f"X_TF dependencies can be ignored: {payload['xtf_dependencies_can_be_ignored']}",
        f"Residual X_TF allowed: {payload['residual_xtf_allowed']}",
        f"Scalars allowed: {payload['scalars_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## X_TF Requirements",
        "",
    ]
    for key, value in payload["x_tf_requirements"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Candidates",
            "",
            "| candidate | role | passes provenance gate | accepted | blocker |",
            "|---|---|---:|---:|---|",
        ]
    )
    for row in payload["candidates"]:
        lines.append(
            f"| {row['candidate']} | {row['role']} | "
            f"{row['source_derived_covariant_stf_rank2_same_bridge']} | "
            f"{row['accepted']} | {row['blocker']} |"
        )
    lines.extend(
        [
            "",
            "## Dependency Terms",
            "",
            "| dependency | include if | term |",
            "|---|---|---|",
        ]
    )
    for row in payload["dependency_terms"]:
        lines.append(f"| {row['dependency']} | {row['include_if']} | `{row['term']}` |")
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
