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


REPORT_PATH = Path("outputs/reports/p0_ajanus_branch_selector_dynamics_gate.md")
JSON_PATH = Path("outputs/reports/p0_ajanus_branch_selector_dynamics_gate.json")


def build_payload() -> dict:
    linear_matching = build_linear_matching()
    q = sp.symbols("q")
    a1, a2, a3 = sp.symbols("a1 a2 a3")
    p_like = a1 * q + a3 * q**3
    pt_like = a2 * q**2
    p_linear = sp.diff(p_like, q).subs(q, 0)
    pt_linear = sp.diff(pt_like, q).subs(q, 0)

    return {
        "description": "Conditional dynamics gate for selecting the A_Janus parity branch.",
        "status": "conditional-p-like-selection-if-linear-transport-required",
        "input_from_pt_lie_gate": {
            "p_like_shape": str(p_like),
            "pt_like_shape_after_fixed_interface": str(pt_like),
            "fixed_interface_condition": "A(0)=0",
        },
        "mirror_equivariance": {
            "p_like": "A(-q)=-A(q)",
            "pt_like": "A(-q)=A(q) after time reversal",
        },
        "linearization_at_interface": {
            "p_like_dA_dq_at_0": str(p_linear),
            "pt_like_dA_dq_at_0": str(pt_linear),
        },
        "nondegenerate_linear_transport_gate": {
            "requirement": "dA/dq at q=0 is nonzero for first-order same-L transport",
            "p_like_passes_if": "a1 != 0",
            "pt_like_passes": False,
        },
        "linear_residual_matching_gate": {
            "weakfield_rows_are_linear": linear_matching[
                "weakfield_rows_are_linear_in_potential_difference"
            ],
            "p_like_linear_match_condition": linear_matching[
                "p_like_linear_match_condition"
            ],
            "pt_like_can_match_nonzero_linear_residual": linear_matching[
                "pt_like_can_match_nonzero_linear_residual"
            ],
            "scope": linear_matching["scope"],
        },
        "conditional_selected_branch": "P-like odd A_Janus",
        "janus_source_requires_linear_transport": True,
        "coefficients_source_fixed": False,
        "notable_improvement": (
            "If Janus requires a nondegenerate linear transport law at the mirror "
            "interface, the PT-like even A_Janus branch is eliminated and only the "
            "P-like odd branch A=a1*q+a3*q^3 remains. Weak-field relative curvature "
            "rows provide that linear-residual requirement in the non-equal branch."
        ),
        "remaining_lock": (
            "A full Janus source/action identity must still promote the weak-field "
            "linear matching to covariant closure and fix a1/a3."
        ),
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 A_Janus Branch Selector Dynamics Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Conditional selected branch: {payload['conditional_selected_branch']}",
        f"Janus source requires linear transport: {payload['janus_source_requires_linear_transport']}",
        f"Coefficients source fixed: {payload['coefficients_source_fixed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Input From PT/Lie Gate",
        "",
    ]
    for key, value in payload["input_from_pt_lie_gate"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Linearization", ""])
    for key, value in payload["linearization_at_interface"].items():
        lines.append(f"- {key}: `{value}`")
    gate = payload["nondegenerate_linear_transport_gate"]
    matching = payload["linear_residual_matching_gate"]
    lines.extend(
        [
            "",
            "## Nondegenerate Linear Transport Gate",
            "",
            f"- requirement: {gate['requirement']}",
            f"- P-like passes if: `{gate['p_like_passes_if']}`",
            f"- PT-like passes: {gate['pt_like_passes']}",
            "",
            "## Linear Residual Matching",
            "",
            f"- weak-field rows are linear: {matching['weakfield_rows_are_linear']}",
            f"- P-like linear match: `{matching['p_like_linear_match_condition']}`",
            f"- PT-like can match nonzero linear residual: {matching['pt_like_can_match_nonzero_linear_residual']}",
            f"- scope: {matching['scope']}",
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
