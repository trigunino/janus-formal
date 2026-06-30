from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_projector_variation_dependency_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_projector_variation_dependency_gate.json")


def build_payload() -> dict:
    branches = [
        {
            "branch": "fixed_background_projector",
            "variation_rule": "delta(P_STF X)=P_STF(delta X)",
            "allowed_if": "metric, tetrad, screen projector and congruence are fixed by gauge before variation",
            "accepted": False,
        },
        {
            "branch": "covariant_h_projector",
            "variation_rule": (
                "delta P_TF(N)=delta N - 1/4[(Tr(H^-1 deltaN - H^-1 deltaH H^-1 N))H "
                "+ Tr(H^-1 N)deltaH]"
            ),
            "allowed_if": "P_TF(N)=N-(Tr(H^-1N)/4)H and H is varied",
            "accepted": False,
        },
        {
            "branch": "screen_projector",
            "variation_rule": "delta h^{mu nu}=delta g^{mu nu}+delta u^mu u^nu+u^mu delta u^nu",
            "allowed_if": "spatial STF projection depends on receiver metric/congruence",
            "accepted": False,
        },
        {
            "branch": "chain_rule_with_projector",
            "variation_rule": "delta(P_STF Y)=P_STF(delta Y)+(delta P_STF)[Y]",
            "allowed_if": "used before pulling Q_TF variations back to H",
            "accepted": False,
        },
    ]
    requirements = [
        "declare whether P_STF is fixed-background or covariant-H before varying",
        "include deltaH inverse terms when using P_TF(N)=N-(Tr(H^-1N)/4)H",
        "include delta h and delta u terms for screen/congruence STF projectors",
        "use the same L/Omega/tetrad branch as Q_TF, K and Q_cross",
        "prove gauge/boundary conditions before dropping projector-variation terms",
    ]
    forbidden_routes = [
        "drop delta P_STF terms without a fixed-projector proof",
        "replace covariant trace-free projection by determinant trace",
        "use screen-shear STF data as full 4D H_TF without lift proof",
        "hide missing projector terms inside a residual source",
    ]
    return {
        "description": "Bounded P0 gate for projector-variation dependency terms in the H_TF/Q_TF channel.",
        "status": "tracefree-h-projector-variation-dependency-gate-open",
        "target_channel": "H_TF/Q_TF",
        "projector_dependency_closed": False,
        "fixed_projector_branch_proved": False,
        "covariant_h_projector_variation_recorded": True,
        "screen_projector_dependency_recorded": True,
        "chain_rule_requires_delta_projector": True,
        "branches": branches,
        "branches_total": len(branches),
        "branches_accepted": sum(1 for row in branches if row["accepted"]),
        "requirements": requirements,
        "forbidden_routes": forbidden_routes,
        "accepted_as_closure": False,
        "residual_target_allowed": False,
        "determinant_trace_allowed": False,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "Projector dependencies are now explicit. A fixed-projector shortcut "
            "is allowed only after gauge/tetrad/congruence conditions are proved; "
            "otherwise delta P_STF terms must remain in the H variation."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Projector Variation Dependency Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Projector dependency closed: {payload['projector_dependency_closed']}",
        f"Fixed projector branch proved: {payload['fixed_projector_branch_proved']}",
        f"Covariant H projector variation recorded: {payload['covariant_h_projector_variation_recorded']}",
        f"Screen projector dependency recorded: {payload['screen_projector_dependency_recorded']}",
        f"Chain rule requires delta projector: {payload['chain_rule_requires_delta_projector']}",
        f"Branches accepted: {payload['branches_accepted']}/{payload['branches_total']}",
        f"Residual target allowed: {payload['residual_target_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Branches",
        "",
        "| branch | variation rule | allowed if | accepted |",
        "|---|---|---|---:|",
    ]
    for row in payload["branches"]:
        lines.append(
            f"| {row['branch']} | `{row['variation_rule']}` | {row['allowed_if']} | {row['accepted']} |"
        )
    lines.extend(["", "## Requirements", ""])
    lines.extend(f"- {item}" for item in payload["requirements"])
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
