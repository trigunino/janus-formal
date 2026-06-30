from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_action_basis_el_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_action_basis_el_variation_gate.json")


def build_payload() -> dict:
    formal_variations = [
        {
            "term": "tr_qtf2",
            "action_density": "Tr(Q_TF^2)",
            "formal_variation": "delta Tr(Q_TF^2) -> 2 Q_TF",
            "projected_el_source": "2 Q_TF",
            "status": "formal/conditional",
            "accepted": False,
            "condition": "requires Janus action provenance before use as an H_TF/Q_TF source",
        },
        {
            "term": "tr_qtf3",
            "action_density": "Tr(Q_TF^3)",
            "formal_variation": "delta Tr(Q_TF^3) -> 3 P_STF(Q_TF^2)",
            "projected_el_source": "3 P_STF(Q_TF^2)",
            "status": "formal/conditional",
            "accepted": False,
            "condition": "requires Janus action provenance and STF projection closure",
        },
        {
            "term": "dqtf_kinetic",
            "action_density": "(D Q_TF)^2",
            "formal_variation": "delta (D Q_TF)^2 -> -2 P_STF(D*D Q_TF) + boundary",
            "projected_el_source": "-2 P_STF(D*D Q_TF)",
            "status": "formal/conditional",
            "accepted": False,
            "condition": "requires boundary data, integration by parts, and Janus provenance",
        },
        {
            "term": "dhtf_kinetic",
            "action_density": "(D H_TF)^2",
            "formal_variation": "delta (D H_TF)^2 -> -2 P_STF(D*D H_TF) + boundary",
            "projected_el_source": "-2 P_STF(D*D H_TF)",
            "status": "formal/conditional",
            "accepted": False,
            "condition": "analogous derivative variation requires boundary data and Janus provenance",
        },
        {
            "term": "qtf_xtf_linear",
            "action_density": "Q_TF^{ab} X_TF_ab",
            "formal_variation": "delta (Q_TF X_TF) -> X_TF + dependency terms",
            "projected_el_source": "X_TF plus dependency terms",
            "status": "formal/conditional",
            "accepted": False,
            "condition": "dependency terms are required if X_TF depends on H, L, phi, or matter",
        },
        {
            "term": "bf_gl_constraints",
            "action_density": "BF/GL multiplier constraints",
            "formal_variation": "BF/GL constraints -> multiplier source only if Janus-derived",
            "projected_el_source": "constraint multiplier source",
            "status": "formal/conditional",
            "accepted": False,
            "condition": "multipliers cannot be accepted unless derived from the Janus constraint action",
        },
    ]
    return {
        "description": (
            "Bounded P0 trace-free H/Q_TF action-basis Euler-Lagrange variation ledger."
        ),
        "status": "tracefree-h-action-basis-el-variation-gate-open",
        "target_channel": "H_TF/Q_TF",
        "ledger_scope": "formal candidate variations only",
        "variation_domain": "symmetric trace-free channel with P_STF projection",
        "formal_variations": formal_variations,
        "variation_count": len(formal_variations),
        "accepted_variations": [
            row["term"]
            for row in formal_variations
            if row["accepted"] and row["status"] == "accepted"
        ],
        "dependency_rule": (
            "For Q_TF X_TF, include dependency terms whenever X_TF depends on "
            "H, L, phi, or matter."
        ),
        "constraint_rule": (
            "BF/GL constraints give a multiplier source only when the constraint "
            "sector is Janus-derived."
        ),
        "all_variations_formal": True,
        "any_variation_accepted": False,
        "residual_target_allowed": False,
        "determinant_trace_allowed": False,
        "forbidden_routes": [
            "fit or declare a residual target for the trace-free source",
            "use determinant trace, log det(H), or B4vol as trace-free source data",
            "accept a BF/GL multiplier source without Janus derivation",
        ],
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The ledger records formal EL variations only. No action-basis term is "
            "accepted, residual targets and determinant trace are forbidden, and the "
            "artifact is not prediction-ready."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H Action-Basis EL Variation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Ledger scope: {payload['ledger_scope']}",
        f"Variation domain: {payload['variation_domain']}",
        f"All variations formal: {payload['all_variations_formal']}",
        f"Any variation accepted: {payload['any_variation_accepted']}",
        f"Residual target allowed: {payload['residual_target_allowed']}",
        f"Determinant trace allowed: {payload['determinant_trace_allowed']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Formal Variation Ledger",
        "",
        "| term | action density | formal variation | status | accepted | condition |",
        "|---|---|---|---|---:|---|",
    ]
    for row in payload["formal_variations"]:
        lines.append(
            f"| {row['term']} | `{row['action_density']}` | "
            f"`{row['formal_variation']}` | {row['status']} | "
            f"{row['accepted']} | {row['condition']} |"
        )
    lines.extend(
        [
            "",
            "## Rules",
            "",
            f"- Dependency rule: {payload['dependency_rule']}",
            f"- Constraint rule: {payload['constraint_rule']}",
            "",
            "## Forbidden Routes",
            "",
        ]
    )
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
