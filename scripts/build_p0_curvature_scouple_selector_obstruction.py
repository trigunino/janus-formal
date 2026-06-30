from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_curvature_scouple_selector_obstruction.md")
JSON_PATH = Path("outputs/reports/p0_curvature_scouple_selector_obstruction.json")


def build_payload() -> dict:
    x = sp.symbols("x")
    alpha, lam = sp.symbols("alpha lambda", positive=True)
    phi = sp.Function("phi")(x)
    dphi = sp.diff(phi, x)
    r_plus = sp.Function("R_plus")(x)
    r_minus = sp.Function("R_minus")
    source = sp.Function("F")

    weighted_top_form = r_plus * source(phi) * dphi
    weighted_top_form_el = sp.simplify(
        sp.diff(weighted_top_form, phi) - sp.diff(sp.diff(weighted_top_form, dphi), x)
    )

    curvature_kinetic = sp.Rational(1, 2) * alpha * r_plus * dphi**2
    curvature_kinetic_el = sp.simplify(
        sp.diff(curvature_kinetic, phi) - sp.diff(sp.diff(curvature_kinetic, dphi), x)
    )

    scalar_match = sp.Rational(1, 2) * lam * (r_plus - r_minus(phi)) ** 2
    scalar_match_el = sp.simplify(sp.diff(scalar_match, phi))

    rows = [
        {
            "route": "curvature_weighted_pullback",
            "lagrangian": "R_plus(x) F(phi) D phi",
            "euler_lagrange": str(weighted_top_form_el),
            "produces_map_equation": True,
            "selects_unique_map": False,
            "reason": "equation constrains R_plus gradient/source support, not an invertible phi/J/L map",
        },
        {
            "route": "curvature_weighted_kinetic",
            "lagrangian": "alpha/2 R_plus(x) (D phi)^2",
            "euler_lagrange": str(curvature_kinetic_el),
            "produces_map_equation": True,
            "selects_unique_map": False,
            "reason": "PDE needs source-derived alpha, curvature branch, and boundary data",
        },
        {
            "route": "scalar_curvature_matching",
            "lagrangian": "lambda/2 (R_plus(x)-R_minus(phi))^2",
            "euler_lagrange": str(scalar_match_el),
            "produces_map_equation": True,
            "selects_unique_map": False,
            "reason": "scalar curvature matching is degenerate and omits same-L/tensor residual closure",
        },
    ]
    return {
        "description": "Obstruction for local curvature-dependent S_couple selector routes.",
        "status": "curvature-scouple-selector-obstruction-open",
        "rows": rows,
        "curvature_weighted_top_form_el": str(weighted_top_form_el),
        "curvature_weighted_kinetic_el": str(curvature_kinetic_el),
        "scalar_curvature_match_el": str(scalar_match_el),
        "curvature_terms_produce_map_equations": True,
        "curvature_terms_select_unique_phi_j_l": False,
        "scalar_curvature_matching_degenerate": True,
        "requires_source_derived_curvature_branch": True,
        "requires_source_derived_coefficients": True,
        "requires_boundary_or_initial_data": True,
        "requires_same_l_tensor_residual_proof": True,
        "requires_split_noether_proof": True,
        "new_axiom_if_adopted_without_source": True,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "hidden_axiom_used": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Curvature couplings can generate map equations, but the tested local "
            "curvature class still does not select a unique phi/J/L. Scalar curvature "
            "matching is degenerate, curvature-weighted PDEs need coefficients and "
            "boundary/source data, and none proves same-L tensor residual closure."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Curvature S_couple Selector Obstruction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Curvature weighted top-form EL: `{payload['curvature_weighted_top_form_el']}`",
        f"Curvature weighted kinetic EL: `{payload['curvature_weighted_kinetic_el']}`",
        f"Scalar curvature match EL: `{payload['scalar_curvature_match_el']}`",
        f"Curvature terms produce map equations: {payload['curvature_terms_produce_map_equations']}",
        f"Curvature terms select unique phi/J/L: {payload['curvature_terms_select_unique_phi_j_l']}",
        f"Scalar curvature matching degenerate: {payload['scalar_curvature_matching_degenerate']}",
        f"Requires source-derived curvature branch: {payload['requires_source_derived_curvature_branch']}",
        f"Requires source-derived coefficients: {payload['requires_source_derived_coefficients']}",
        f"Requires boundary or initial data: {payload['requires_boundary_or_initial_data']}",
        f"Requires same-L tensor residual proof: {payload['requires_same_l_tensor_residual_proof']}",
        f"Requires split Noether proof: {payload['requires_split_noether_proof']}",
        f"New axiom if adopted without source: {payload['new_axiom_if_adopted_without_source']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Hidden axiom used: {payload['hidden_axiom_used']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Rows",
        "",
        "| route | lagrangian | Euler-Lagrange | produces equation | selects unique map | reason |",
        "|---|---|---|---:|---:|---|",
    ]
    for row in payload["rows"]:
        lines.append(
            f"| {row['route']} | `{row['lagrangian']}` | `{row['euler_lagrange']}` | "
            f"{row['produces_map_equation']} | {row['selects_unique_map']} | {row['reason']} |"
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
