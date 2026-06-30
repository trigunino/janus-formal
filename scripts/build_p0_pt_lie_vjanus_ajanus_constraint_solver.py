from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_ajanus_branch_selector_dynamics_gate import (
    build_payload as build_ajanus_branch_gate,
)


REPORT_PATH = Path("outputs/reports/p0_pt_lie_vjanus_ajanus_constraint_solver.md")
JSON_PATH = Path("outputs/reports/p0_pt_lie_vjanus_ajanus_constraint_solver.json")


def zero_coefficients(expr: sp.Expr, symbol: sp.Symbol) -> list[str]:
    poly = sp.Poly(sp.expand(expr), symbol)
    return [str(coef) for coef in poly.all_coeffs() if coef != 0]


def build_payload() -> dict:
    branch_gate = build_ajanus_branch_gate()
    q = sp.symbols("q")
    c0, c1, c2, c3, c4 = sp.symbols("c0 c1 c2 c3 c4")
    a0, a1, a2, a3 = sp.symbols("a0 a1 a2 a3")
    v = c0 + c1 * q + c2 * q**2 + c3 * q**3 + c4 * q**4
    a = a0 + a1 * q + a2 * q**2 + a3 * q**3

    v_even_residual = sp.expand(v.subs(q, -q) - v)
    a_odd_residual = sp.expand(a.subs(q, -q) + a)
    a_even_residual = sp.expand(a.subs(q, -q) - a)
    v_stability = sp.diff(v, q, 2).subs(q, 0)

    return {
        "description": "PT/Lie admissibility constraints for the surviving V_Janus/A_Janus S_cross families.",
        "status": "pt-lie-constraints-derived-branch-not-selected",
        "source_anchor": "M31/X2025-symplectic: torsor/symmetry classification only; no coefficient dynamics extracted",
        "v_ansatz": str(v),
        "a_ansatz": str(a),
        "v_even_residual": str(v_even_residual),
        "v_forbidden_coefficients": zero_coefficients(v_even_residual, q),
        "v_allowed_shape": "c0 + c2*q^2 + c4*q^4",
        "v_stability_condition_at_origin": f"{v_stability} >= 0",
        "a_p_branch_residual": str(a_odd_residual),
        "a_p_branch_forbidden_coefficients": zero_coefficients(a_odd_residual, q),
        "a_p_branch_allowed_shape": "a1*q + a3*q^3",
        "a_pt_branch_residual": str(a_even_residual),
        "a_pt_branch_forbidden_coefficients": zero_coefficients(a_even_residual, q),
        "a_pt_branch_allowed_shape": "a0 + a2*q^2; with fixed interface A(0)=0 this also requires a0=0",
        "conditional_dynamics_gate": {
            "selected_branch_if_linear_transport_required": branch_gate[
                "conditional_selected_branch"
            ],
            "janus_source_requires_linear_transport": branch_gate[
                "janus_source_requires_linear_transport"
            ],
            "p_like_passes_if": branch_gate["nondegenerate_linear_transport_gate"][
                "p_like_passes_if"
            ],
            "pt_like_passes": branch_gate["nondegenerate_linear_transport_gate"][
                "pt_like_passes"
            ],
        },
        "branch_selected_by_janus_source": False,
        "coefficients_source_fixed": False,
        "notable_improvement": (
            "V_Janus is reduced to an even potential and A_Janus to a parity branch. "
            "This removes linear/cubic V terms and half of the polynomial A coefficients "
            "before any observational comparison."
        ),
        "remaining_lock": (
            "Janus source equations must still select P-like versus PT-like transport "
            "and fix c2/c4 or a1/a3/a2 from geometry/action, not by fit."
        ),
        "prediction_ready": False,
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 PT/Lie V_Janus A_Janus Constraint Solver",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source anchor: {payload['source_anchor']}",
        f"Branch selected by Janus source: {payload['branch_selected_by_janus_source']}",
        f"Coefficients source fixed: {payload['coefficients_source_fixed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## V_Janus",
        "",
        f"- ansatz: `{payload['v_ansatz']}`",
        f"- PT/Lie even residual: `{payload['v_even_residual']}`",
        f"- forbidden coefficients: `{payload['v_forbidden_coefficients']}`",
        f"- allowed shape: `{payload['v_allowed_shape']}`",
        f"- stability at origin: `{payload['v_stability_condition_at_origin']}`",
        "",
        "## A_Janus",
        "",
        f"- ansatz: `{payload['a_ansatz']}`",
        f"- P-like residual: `{payload['a_p_branch_residual']}`",
        f"- P-like forbidden coefficients: `{payload['a_p_branch_forbidden_coefficients']}`",
        f"- P-like allowed shape: `{payload['a_p_branch_allowed_shape']}`",
        f"- PT-like residual: `{payload['a_pt_branch_residual']}`",
        f"- PT-like forbidden coefficients: `{payload['a_pt_branch_forbidden_coefficients']}`",
        f"- PT-like allowed shape: `{payload['a_pt_branch_allowed_shape']}`",
        "",
        "## Conditional Dynamics Gate",
        "",
        f"- selected if linear transport required: `{payload['conditional_dynamics_gate']['selected_branch_if_linear_transport_required']}`",
        f"- Janus source requires linear transport: {payload['conditional_dynamics_gate']['janus_source_requires_linear_transport']}",
        f"- P-like passes if: `{payload['conditional_dynamics_gate']['p_like_passes_if']}`",
        f"- PT-like passes: {payload['conditional_dynamics_gate']['pt_like_passes']}",
        "",
        "## Result",
        "",
        payload["notable_improvement"],
        "",
        f"Remaining lock: {payload['remaining_lock']}",
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
