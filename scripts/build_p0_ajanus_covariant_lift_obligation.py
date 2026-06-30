from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_ajanus_linear_residual_matching_gate import (
    build_payload as build_linear_matching,
)
from scripts.build_p0_covariant_q_field_candidate_gate import (
    build_payload as build_q_gate,
)
from scripts.build_p0_relative_strain_q_regular_branch_gate import (
    build_payload as build_q_regular,
)


REPORT_PATH = Path("outputs/reports/p0_ajanus_covariant_lift_obligation.md")
JSON_PATH = Path("outputs/reports/p0_ajanus_covariant_lift_obligation.json")


def build_payload() -> dict:
    linear = build_linear_matching()
    q_gate = build_q_gate()
    q_regular = build_q_regular()
    q, r1, r3, a1, a3 = sp.symbols("q r1 r3 a1 a3")
    covariant_source_series = r1 * q + r3 * q**3
    p_like_transport = a1 * q + a3 * q**3
    unmatched = sp.expand(covariant_source_series - p_like_transport)
    match_conditions = {
        "linear": f"{unmatched.coeff(q, 1)}=0 -> a1=r1",
        "cubic": f"{unmatched.coeff(q, 3)}=0 -> a3=r3",
    }
    return {
        "description": "Covariant lift obligation for the weak-field A_Janus branch selection.",
        "status": "covariant-lift-obligation-written-not-closed",
        "depends_on": [
            "p0_ajanus_linear_residual_matching_gate",
            "p0_bianchi_minimal_full_connection_lift_system",
        ],
        "weakfield_branch_selected": linear["conditional_selected_branch"],
        "selected_covariant_q_object": q_gate["selected_candidate"],
        "selected_covariant_q_definition": q_gate["selected_candidate_definition"],
        "selected_covariant_q_trace_relation": q_regular["trace_relation"],
        "selected_covariant_q_regular_branch_defined": q_regular["q_regular_branch_defined"],
        "selected_covariant_q_derivative_gate": q_regular["derivative_gate"],
        "covariant_objects_required": [
            "covariant relative field Q[phi,L] selected by p0_covariant_q_field_candidate_gate",
            "DQ=1/2 FrechetLog_H[D_alpha H] from the same Omega_alpha branch",
            "source-derived odd residual one-form R_Janus[phi,L,g_plus,g_minus,matter]",
            "same Omega_alpha=(D_alpha L)L^{-1}",
            "relative curvature equation D Omega + Omega wedge Omega = F_relative[source]",
            "mirror inverse plus/minus branch",
        ],
        "covariant_source_series": str(covariant_source_series),
        "p_like_transport_series": str(p_like_transport),
        "unmatched_residual": str(unmatched),
        "match_conditions": match_conditions,
        "a1_source_fixed_if": "r1 is computed from the covariant Janus source/relative-curvature linearization",
        "a3_source_fixed_if": "r3 is computed from the same covariant Janus source/action expansion",
        "no_fit_rule": "a1 and a3 may equal r1 and r3 only when r1/r3 are source-derived, not data-fitted",
        "weakfield_promotion_done": False,
        "coefficients_source_fixed": False,
        "global_branch_selected_by_full_janus_source": False,
        "prediction_ready": False,
        "notable_improvement": (
            "The coefficient problem is now algebraic: for the surviving P-like branch, "
            "full covariant matching requires a1=r1 and a3=r3. The task is no longer "
            "to invent coefficients, but to derive r1/r3 from Janus source geometry. "
            "The q-object is now Q=1/2 log(H), not a determinant scalar."
        ),
        "remaining_lock": (
            "Derive the regular polar/log branch for Q and derive the odd source "
            "residual R_Janus from the Janus action/relative-curvature law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 A_Janus Covariant Lift Obligation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Depends on: {payload['depends_on']}",
        f"Weak-field branch selected: {payload['weakfield_branch_selected']}",
        f"Selected covariant q object: {payload['selected_covariant_q_object']}",
        f"Selected covariant q definition: {payload['selected_covariant_q_definition']}",
        f"Selected covariant q trace relation: {payload['selected_covariant_q_trace_relation']}",
        f"Selected covariant q regular branch defined: {payload['selected_covariant_q_regular_branch_defined']}",
        f"Selected covariant q derivative gate: {payload['selected_covariant_q_derivative_gate']}",
        f"Weak-field promotion done: {payload['weakfield_promotion_done']}",
        f"Coefficients source fixed: {payload['coefficients_source_fixed']}",
        f"Global branch selected by full Janus source: {payload['global_branch_selected_by_full_janus_source']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Required Covariant Objects",
        "",
    ]
    lines.extend(f"- `{item}`" for item in payload["covariant_objects_required"])
    lines.extend(
        [
            "",
            "## Matching",
            "",
            f"- source series: `{payload['covariant_source_series']}`",
            f"- P-like transport: `{payload['p_like_transport_series']}`",
            f"- unmatched residual: `{payload['unmatched_residual']}`",
            f"- linear match: `{payload['match_conditions']['linear']}`",
            f"- cubic match: `{payload['match_conditions']['cubic']}`",
            f"- a1 source fixed if: {payload['a1_source_fixed_if']}",
            f"- a3 source fixed if: {payload['a3_source_fixed_if']}",
            f"- no-fit rule: {payload['no_fit_rule']}",
            "",
            "## Result",
            "",
            payload["notable_improvement"],
            "",
            f"Remaining lock: {payload['remaining_lock']}",
            "",
        ]
    )
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
