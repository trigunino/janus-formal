from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_weakfield_relative_curvature_rows_target import (
    build_payload as build_weakfield_rows,
)


REPORT_PATH = Path("outputs/reports/p0_ajanus_linear_residual_matching_gate.md")
JSON_PATH = Path("outputs/reports/p0_ajanus_linear_residual_matching_gate.json")


def build_payload() -> dict:
    weakfield = build_weakfield_rows()
    q, r1, r2, a1, a2, a3 = sp.symbols("q r1 r2 a1 a2 a3")
    source_residual = r1 * q + r2 * q**2
    p_like = a1 * q + a3 * q**3
    pt_like = a2 * q**2
    p_unmatched = sp.expand(source_residual - p_like)
    pt_unmatched = sp.expand(source_residual - pt_like)
    p_linear_coeff = sp.expand(p_unmatched).coeff(q, 1)
    pt_linear_coeff = sp.expand(pt_unmatched).coeff(q, 1)

    weakfield_expressions = " ".join(
        row["derived_expression"] for row in weakfield["curvature_rows"]
    )
    weakfield_rows_are_linear = all(
        "**2" not in row["derived_expression"] and "*" not in row["derived_expression"]
        for row in weakfield["curvature_rows"]
    )

    return {
        "description": "Linear residual matching gate for selecting the A_Janus transport branch in weak-field non-equal sectors.",
        "status": "weakfield-linear-matching-selects-p-like-conditionally",
        "weakfield_source_rows_available": bool(weakfield["source_rows_computable"]),
        "weakfield_rows_are_linear_in_potential_difference": weakfield_rows_are_linear,
        "weakfield_source_examples": weakfield_expressions[:240],
        "source_residual_model": str(source_residual),
        "p_like_transport": str(p_like),
        "pt_like_transport": str(pt_like),
        "p_like_unmatched_residual": str(p_unmatched),
        "pt_like_unmatched_residual": str(pt_unmatched),
        "p_like_linear_match_condition": f"{p_linear_coeff}=0 -> a1=r1",
        "pt_like_linear_residual": str(pt_linear_coeff),
        "pt_like_can_match_nonzero_linear_residual": False,
        "conditional_selected_branch": "P-like odd A_Janus for weak-field non-equal linear residuals",
        "janus_source_requires_linear_transport": True,
        "scope": "conditional weak-field/non-equal branch; not full covariant Janus closure",
        "global_branch_selected_by_full_janus_source": False,
        "remaining_lock": (
            "Promote the weak-field linear residual requirement to the full "
            "covariant source/action, then fix a1 and a3 from Janus geometry."
        ),
        "covariant_lift_next_artifact": "p0_ajanus_covariant_lift_obligation",
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 A_Janus Linear Residual Matching Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Weak-field source rows available: {payload['weakfield_source_rows_available']}",
        f"Weak-field rows linear: {payload['weakfield_rows_are_linear_in_potential_difference']}",
        f"Janus source requires linear transport: {payload['janus_source_requires_linear_transport']}",
        f"Global branch selected by full Janus source: {payload['global_branch_selected_by_full_janus_source']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Symbolic Matching",
        "",
        f"- source residual: `{payload['source_residual_model']}`",
        f"- P-like transport: `{payload['p_like_transport']}`",
        f"- PT-like transport: `{payload['pt_like_transport']}`",
        f"- P-like unmatched residual: `{payload['p_like_unmatched_residual']}`",
        f"- PT-like unmatched residual: `{payload['pt_like_unmatched_residual']}`",
        f"- P-like linear match condition: `{payload['p_like_linear_match_condition']}`",
        f"- PT-like linear residual: `{payload['pt_like_linear_residual']}`",
        f"- PT-like can match nonzero linear residual: {payload['pt_like_can_match_nonzero_linear_residual']}",
        "",
        "## Weak-Field Source Examples",
        "",
        f"`{payload['weakfield_source_examples']}`",
        "",
        "## Result",
        "",
        f"Conditional selected branch: {payload['conditional_selected_branch']}",
        "",
        f"Scope: {payload['scope']}",
        "",
        f"Remaining lock: {payload['remaining_lock']}",
        "",
        f"Next artifact: `{payload['covariant_lift_next_artifact']}`",
        "",
    ]
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
