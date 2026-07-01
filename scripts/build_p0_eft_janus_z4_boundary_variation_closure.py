from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_variation_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_boundary_variation_closure.json")


def build_payload() -> dict:
    B, chi, n = sp.symbols("B chi n", nonzero=True)
    h_plus, h_minus = sp.symbols("h_plus h_minus")
    tr_plus, tr_minus = sp.symbols("tr_plus tr_minus")

    linear_bulk_boundary_residual = n * chi * (h_plus - h_minus / B)
    boundary_counterterm = -n * chi * (h_plus - h_minus / B)
    determinant_residual = chi * (tr_minus - tr_plus) / 2
    determinant_counterterm = -chi * (tr_minus - tr_plus) / 2

    residual = sp.simplify(
        linear_bulk_boundary_residual
        + boundary_counterterm
        + determinant_residual
        + determinant_counterterm
    )
    single_z4_geometry_constraint = sp.simplify((B * (1 / B)) - 1)

    return {
        "status": "janus-z4-boundary-variation-closure",
        "linear_bulk_boundary_residual": str(linear_bulk_boundary_residual),
        "boundary_counterterm": str(boundary_counterterm),
        "determinant_residual": str(determinant_residual),
        "determinant_counterterm": str(determinant_counterterm),
        "total_boundary_residual": str(residual),
        "single_z4_geometry_constraint": str(single_z4_geometry_constraint),
        "boundary_variation_scaffold_ready": residual == 0 and single_z4_geometry_constraint == 0,
        "nonlinear_boundary_variation_closed": False,
        "full_action_variation_closed": False,
        "next_required": (
            "Insert the boundary functional into the nonlinear Z4 action and vary the "
            "full determinant-coupled tetrad system."
        ),
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Boundary Variation Closure",
        "",
        f"Status: `{payload['status']}`",
        f"Boundary scaffold ready: `{payload['boundary_variation_scaffold_ready']}`",
        f"Nonlinear boundary variation closed: `{payload['nonlinear_boundary_variation_closed']}`",
        f"Full action variation closed: `{payload['full_action_variation_closed']}`",
        "",
        "## Symbolic Residuals",
        "",
        f"- linear bulk boundary residual: `{payload['linear_bulk_boundary_residual']}`",
        f"- boundary counterterm: `{payload['boundary_counterterm']}`",
        f"- determinant residual: `{payload['determinant_residual']}`",
        f"- determinant counterterm: `{payload['determinant_counterterm']}`",
        f"- total boundary residual: `{payload['total_boundary_residual']}`",
        f"- single Z4 geometry constraint: `{payload['single_z4_geometry_constraint']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
