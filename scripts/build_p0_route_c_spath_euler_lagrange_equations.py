from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_minimal_spath_extension_axiom_gate import (
    build_payload as build_minimal_spath,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_euler_lagrange_equations.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_euler_lagrange_equations.json")


def euler_lagrange(lagrangian: sp.Expr, field: sp.Function, variable: sp.Symbol) -> sp.Expr:
    return sp.simplify(
        sp.diff(lagrangian, field(variable))
        - sp.diff(sp.diff(lagrangian, sp.diff(field(variable), variable)), variable)
    )


def build_payload() -> dict:
    minimal = build_minimal_spath()
    s = sp.symbols("s")
    gamma = sp.Function("gamma")
    ell = sp.Function("ell")
    c_j = sp.Function("C_J")
    v_j = sp.Function("V_J")
    omega = sp.Function("omega")

    gamma_dot = sp.diff(gamma(s), s)
    path_lagrangian = sp.Rational(1, 2) * c_j(gamma(s)) * gamma_dot**2 + v_j(gamma(s))
    gamma_el = euler_lagrange(path_lagrangian, gamma, s)

    transport_residual = sp.diff(ell(s), s) + omega(s) * ell(s)
    transport_lagrangian = sp.Rational(1, 2) * transport_residual**2
    ell_el = euler_lagrange(transport_lagrangian, ell, s)

    variation_rows = [
        {
            "variation": "delta_gamma S_path",
            "formal_equation": str(gamma_el),
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "C_J, V_J and boundary law are not yet physically fixed",
        },
        {
            "variation": "delta_L S_path",
            "formal_equation": str(ell_el),
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "scalar ell represents only one transport component; full Lorentz/tetrad constrained matrix L remains open",
        },
        {
            "variation": "endpoint_boundary_terms",
            "formal_equation": "delta gamma endpoint term = partial L_path / partial gamma_dot * delta gamma | boundary",
            "derived_formally": True,
            "closed_for_prediction": False,
            "blocker": "PT/boundary endpoint law is still not selected",
        },
        {
            "variation": "lorentz_constraint",
            "formal_equation": "L^T eta L = eta with multiplier or projected variation delta L in so(1,3)",
            "derived_formally": False,
            "closed_for_prediction": False,
            "blocker": "full constrained variation must be done before same-L substitution",
        },
    ]
    return {
        "description": (
            "Formal Euler-Lagrange scaffold for the explicit S_path extension. "
            "It derives representative path and transport equations without "
            "claiming tensor closure or prediction readiness."
        ),
        "status": "spath-euler-lagrange-equations-formal-open",
        "depends_on": ["p0_route_c_minimal_spath_extension_axiom_gate"],
        "minimal_spath_status": minimal["status"],
        "extension_object": minimal["extension_object"],
        "path_lagrangian_representative": str(path_lagrangian),
        "gamma_euler_lagrange_representative": str(gamma_el),
        "transport_lagrangian_representative": str(transport_lagrangian),
        "transport_residual_representative": str(transport_residual),
        "l_euler_lagrange_representative": str(ell_el),
        "variation_rows": variation_rows,
        "gamma_el_derived_formally": True,
        "l_transport_el_derived_formally": True,
        "endpoint_boundary_terms_identified": True,
        "lorentz_constraint_variation_closed": False,
        "source_functions_fixed": False,
        "same_l_stack_closed": False,
        "bianchi_noether_closure_closed": False,
        "stability_screen_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The variational skeleton exists, but it is not a physical closure: "
            "C_J/V_J, PT boundary data, full Lorentz-constrained matrix variation, "
            "same-L substitution and Bianchi/Noether closure remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Euler-Lagrange Equations",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Extension object: `{payload['extension_object']}`",
        f"Path Lagrangian representative: `{payload['path_lagrangian_representative']}`",
        f"Gamma Euler-Lagrange representative: `{payload['gamma_euler_lagrange_representative']}`",
        f"Transport residual representative: `{payload['transport_residual_representative']}`",
        f"L Euler-Lagrange representative: `{payload['l_euler_lagrange_representative']}`",
        f"Gamma EL derived formally: {payload['gamma_el_derived_formally']}",
        f"L transport EL derived formally: {payload['l_transport_el_derived_formally']}",
        f"Lorentz constraint variation closed: {payload['lorentz_constraint_variation_closed']}",
        f"Same-L stack closed: {payload['same_l_stack_closed']}",
        f"Bianchi/Noether closure closed: {payload['bianchi_noether_closure_closed']}",
        f"Stability screen closed: {payload['stability_screen_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| variation | formal equation | derived formally | closed for prediction | blocker |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["variation_rows"]:
        lines.append(
            f"| {row['variation']} | `{row['formal_equation']}` | "
            f"{row['derived_formally']} | {row['closed_for_prediction']} | {row['blocker']} |"
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
