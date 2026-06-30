from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_route_c_spath_euler_lagrange_equations import (
    build_payload as build_spath_el,
)


REPORT_PATH = Path("outputs/reports/p0_route_c_spath_lorentz_tetrad_variation_gate.md")
JSON_PATH = Path("outputs/reports/p0_route_c_spath_lorentz_tetrad_variation_gate.json")


ETA = sp.diag(1, -1, -1, -1)


def lorentz_generator() -> sp.Matrix:
    bx, by, bz, rx, ry, rz = sp.symbols("b_x b_y b_z r_x r_y r_z")
    return sp.Matrix(
        [
            [0, bx, by, bz],
            [bx, 0, rz, -ry],
            [by, -rz, 0, rx],
            [bz, ry, -rx, 0],
        ]
    )


def eta_lorentz_projector(matrix: sp.Matrix) -> sp.Matrix:
    return sp.simplify((matrix - ETA * matrix.T * ETA) / 2)


def build_payload() -> dict:
    spath_el = build_spath_el()
    xi = lorentz_generator()
    xi_eta_residual = sp.simplify(xi.T * ETA + ETA * xi)

    a = sp.Matrix(4, 4, lambda i, j: sp.symbols(f"a{i}{j}"))
    projected_a = eta_lorentz_projector(a)
    projected_residual = sp.simplify(projected_a.T * ETA + ETA * projected_a)

    first_order_constraint_residual = xi_eta_residual
    variation_rows = [
        {
            "object": "admissible_variation",
            "formula": "delta L = L Xi, Xi^T eta + eta Xi = 0",
            "formalized": True,
            "closed_for_prediction": False,
            "blocker": "does not select Xi or the physical path gamma",
        },
        {
            "object": "constraint_preservation",
            "formula": "delta(L^T eta L)=Xi^T eta + eta Xi=0",
            "formalized": True,
            "closed_for_prediction": False,
            "blocker": "first-order Lorentz admissibility only",
        },
        {
            "object": "projected_el_equation",
            "formula": "P_so(1,3)(L^{-1} E_L)=0",
            "formalized": True,
            "closed_for_prediction": False,
            "blocker": "requires full E_L from tensor S_path, not only scalar representative",
        },
        {
            "object": "spin_covariant_residual",
            "formula": "D_s L = partial_s L + omega_plus,s L - L omega_minus,s",
            "formalized": True,
            "closed_for_prediction": False,
            "blocker": "omega_plus/omega_minus and path gamma remain source-open",
        },
        {
            "object": "tetrad_bridge",
            "formula": "M_minus_to_plus = e_plus L e_minus^{-1}",
            "formalized": True,
            "closed_for_prediction": False,
            "blocker": "same bridge must still be substituted into K, Q_cross and Vlasov",
        },
    ]
    return {
        "description": (
            "Formal Lorentz/tetrad constrained-variation gate for the explicit "
            "S_path extension. It upgrades scalar delta_L bookkeeping to "
            "delta L = L Xi with Xi in so(1,3)."
        ),
        "status": "spath-lorentz-tetrad-variation-formal-open",
        "depends_on": ["p0_route_c_spath_euler_lagrange_equations"],
        "spath_el_status": spath_el["status"],
        "eta_signature": [1, -1, -1, -1],
        "xi_generator": str(xi),
        "xi_eta_residual": str(xi_eta_residual),
        "first_order_constraint_residual": str(first_order_constraint_residual),
        "projector_formula": "P_so_eta(A)=1/2*(A-eta*A.T*eta)",
        "projected_generic_matrix_eta_residual": str(projected_residual),
        "variation_rows": variation_rows,
        "lorentz_constrained_variation_formalized": True,
        "first_order_lorentz_constraint_preserved": xi_eta_residual == sp.zeros(4),
        "eta_lorentz_projector_verified": projected_residual == sp.zeros(4),
        "tetrad_bridge_formula_written": True,
        "full_tensor_el_closed": False,
        "source_functions_fixed": False,
        "same_l_stack_closed": False,
        "bianchi_noether_closure_closed": False,
        "stability_screen_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The Lorentz variation contract is now formalized: variations must "
            "live in the eta-antisymmetric algebra and raw E_L must be projected. "
            "This is algebraic progress only; the tensor S_path, source functions, "
            "same-L substitution, Bianchi/Noether closure and stability remain open."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route C S_path Lorentz/Tetrad Variation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Xi eta residual: `{payload['xi_eta_residual']}`",
        f"Projector formula: `{payload['projector_formula']}`",
        f"Projected generic matrix eta residual: `{payload['projected_generic_matrix_eta_residual']}`",
        f"Lorentz constrained variation formalized: {payload['lorentz_constrained_variation_formalized']}",
        f"First-order Lorentz constraint preserved: {payload['first_order_lorentz_constraint_preserved']}",
        f"Eta-Lorentz projector verified: {payload['eta_lorentz_projector_verified']}",
        f"Tetrad bridge formula written: {payload['tetrad_bridge_formula_written']}",
        f"Full tensor EL closed: {payload['full_tensor_el_closed']}",
        f"Same-L stack closed: {payload['same_l_stack_closed']}",
        f"Bianchi/Noether closure closed: {payload['bianchi_noether_closure_closed']}",
        f"Stability screen closed: {payload['stability_screen_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "| object | formula | formalized | closed for prediction | blocker |",
        "|---|---|---:|---:|---|",
    ]
    for row in payload["variation_rows"]:
        lines.append(
            f"| {row['object']} | `{row['formula']}` | {row['formalized']} | "
            f"{row['closed_for_prediction']} | {row['blocker']} |"
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
