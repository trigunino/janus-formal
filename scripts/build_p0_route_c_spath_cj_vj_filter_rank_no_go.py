from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_spath_cj_vj_coefficient_underselection_gate import (
    build_payload as build_coefficient_gate,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_filter_rank_no_go.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_cj_vj_filter_rank_no_go.json")


def build_payload() -> dict:
    coefficient_gate = build_coefficient_gate()
    variable_count = int(coefficient_gate["linear_family_free_coefficients_lower_bound"])
    variables = ["c0"] + [f"c{i}" for i in range(1, 6)] + [f"v{i}" for i in range(1, 6)]
    compatibility_matrix = sp.zeros(0, variable_count)
    rank = int(compatibility_matrix.rank())
    nullity = variable_count - rank
    proof_rows = [
        {
            "input": "no_fit_filter",
            "linear_equation_count": 0,
            "rank_contribution": 0,
            "reason": "removes fitted observable basis terms only",
        },
        {
            "input": "PT_same_L_filters",
            "linear_equation_count": 0,
            "rank_contribution": 0,
            "reason": "surviving invariants were already PT/same-L compatible",
        },
        {
            "input": "stability_sign_inequalities",
            "linear_equation_count": 0,
            "rank_contribution": 0,
            "reason": "inequalities can bound an open region but cannot pick one vector",
        },
        {
            "input": "weak_field_sign_filter",
            "linear_equation_count": 0,
            "rank_contribution": 0,
            "reason": "sign choice does not fix amplitude or nonlinear coefficients",
        },
        {
            "input": "missing_source_action",
            "linear_equation_count": 0,
            "rank_contribution": 0,
            "reason": "no Janus source equation supplies coefficient constraints",
        },
    ]
    return {
        "description": (
            "Rank no-go for selecting the linear C_J/V_J coefficient family from "
            "compatibility filters alone."
        ),
        "status": "spath-cj-vj-filter-rank-no-go-closed",
        "depends_on": ["p0_route_c_spath_cj_vj_coefficient_underselection_gate"],
        "linear_family": coefficient_gate["linear_family"],
        "coefficient_variables": variables,
        "coefficient_variable_count": variable_count,
        "compatibility_matrix_shape": list(compatibility_matrix.shape),
        "compatibility_matrix_rank": rank,
        "compatibility_nullity": nullity,
        "proof_rows": proof_rows,
        "filters_select_unique_coefficients": False,
        "rank_no_go_closed_for_filter_only_family": True,
        "source_equations_required_for_unique_selection": variable_count,
        "stability_inequalities_not_counted_as_rank": True,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Compatibility filters alone have rank zero on the surviving linear "
            "C_J/V_J coefficient vector, leaving nullity 11. A unique selector "
            "requires source/action equations, not additional filter language."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path C_J/V_J Filter Rank No-Go",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Linear family: `{payload['linear_family']}`",
        f"Coefficient variable count: {payload['coefficient_variable_count']}",
        f"Compatibility matrix shape: {payload['compatibility_matrix_shape']}",
        f"Compatibility matrix rank: {payload['compatibility_matrix_rank']}",
        f"Compatibility nullity: {payload['compatibility_nullity']}",
        f"Filters select unique coefficients: {payload['filters_select_unique_coefficients']}",
        (
            "Rank no-go closed for filter-only family: "
            f"{payload['rank_no_go_closed_for_filter_only_family']}"
        ),
        (
            "Source equations required for unique selection: "
            f"{payload['source_equations_required_for_unique_selection']}"
        ),
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| input | linear equations | rank contribution | reason |",
        "|---|---:|---:|---|",
    ]
    for row in payload["proof_rows"]:
        lines.append(
            f"| {row['input']} | {row['linear_equation_count']} | "
            f"{row['rank_contribution']} | {row['reason']} |"
        )
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
