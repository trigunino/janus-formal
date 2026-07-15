from __future__ import annotations

from pathlib import Path
import json
import os
from functools import lru_cache

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import (
        LAMBDA_PHI,
        MHR2,
        MPL2,
        VEV,
        expr_text,
    )
    from scripts.derive_svt_hr_second_order_hessian import derived_hessians
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import (
        LAMBDA_PHI,
        MHR2,
        MPL2,
        VEV,
        expr_text,
    )
    from derive_svt_hr_second_order_hessian import derived_hessians


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_constraint_reduction.md"
JSON_PATH = REPORT_DIR / "svt_scalar_constraint_reduction.json"

K = sp.Symbol("k", nonzero=True)
PSI_P, PSI_M, DPSI_P, DPSI_M = sp.symbols("psi_p psi_m dpsi_p dpsi_m")
DPHI, B_P, B_M, ZETA = sp.symbols("dphi B_p B_m zeta")


@lru_cache(maxsize=None)
def hr_scalar_hessian_entries() -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    matrix = derived_hessians()["scalar_hessian"]
    return matrix[0][0], matrix[0][1], matrix[1][1]


@lru_cache(maxsize=None)
def hr_shift_hessian() -> sp.Expr:
    return derived_hessians()["vector_hessian"]


def spatial_mismatch() -> sp.Expr:
    return PSI_M - PSI_P + K**2 * ZETA


def shift_mismatch() -> sp.Expr:
    return B_M - B_P


@lru_cache(maxsize=None)
def hr_surface_quadratic_density() -> sp.Expr:
    h_ll, h_ls, h_ss = hr_scalar_hessian_entries()
    h_bb = hr_shift_hessian()
    scalar_part = (
        h_ll * DPHI**2
        + 2 * h_ls * DPHI * spatial_mismatch()
        + h_ss * spatial_mismatch() ** 2
    )
    shift_part = h_bb * shift_mismatch() ** 2
    return sp.factor(
        -sp.Rational(1, 2) * MHR2 * MPL2 * (scalar_part + shift_part)
    )


@lru_cache(maxsize=None)
def constraint_equations() -> dict[str, sp.Expr]:
    density = hr_surface_quadratic_density()
    d_s_d_phi_plus = -sp.diff(density, DPHI)
    d_s_d_phi_minus = sp.diff(density, DPHI)
    d_s_d_b_plus = sp.diff(density, B_P)
    d_s_d_b_minus = sp.diff(density, B_M)
    d_s_d_zeta = sp.diff(density, ZETA)
    return {
        "lapse_plus": sp.factor(2 * MPL2 * K**2 * PSI_P - d_s_d_phi_plus),
        "lapse_minus": sp.factor(2 * MPL2 * VEV * K**2 * PSI_M - d_s_d_phi_minus),
        "shift_plus": sp.factor(
            2 * MPL2 * K**2 * (DPSI_P - K**2 * B_P) - d_s_d_b_plus
        ),
        "shift_minus": sp.factor(
            MPL2 * VEV * (2 * K**2 / VEV**2) * (DPSI_M - K**2 * B_M)
            - d_s_d_b_minus
        ),
        "bending": sp.factor(K**2 * ZETA + d_s_d_zeta),
    }


@lru_cache(maxsize=None)
def lapse_compatibility_condition() -> sp.Expr:
    equations = constraint_equations()
    return sp.factor(equations["lapse_plus"] + equations["lapse_minus"])


@lru_cache(maxsize=None)
def solve_lapse_difference() -> sp.Expr:
    equations = constraint_equations()
    solutions = sp.solve(equations["lapse_plus"], DPHI, dict=True)
    return sp.factor(solutions[0][DPHI])


@lru_cache(maxsize=None)
def solve_shifts() -> dict[str, sp.Expr]:
    equations = constraint_equations()
    solutions = sp.solve(
        [equations["shift_plus"], equations["shift_minus"]],
        [B_P, B_M],
        dict=True,
        simplify=True,
    )
    return {key.name: sp.factor(value) for key, value in solutions[0].items()}


@lru_cache(maxsize=None)
def solve_bending_after_lapse() -> sp.Expr:
    equations = constraint_equations()
    dphi_solution = solve_lapse_difference()
    reduced_bending = sp.factor(equations["bending"].subs(DPHI, dphi_solution))
    solutions = sp.solve(reduced_bending, ZETA, dict=True, simplify=True)
    return sp.factor(solutions[0][ZETA])


def canonical_radion_mass2() -> sp.Expr:
    return sp.factor(8 * LAMBDA_PHI * VEV**3)


@lru_cache(maxsize=None)
def build_payload() -> dict:
    equations = constraint_equations()
    shifts = solve_shifts()
    return {
        "artifact": "svt_scalar_constraint_reduction",
        "status": "constraints_encoded_with_lapse_compatibility_and_bending_solution",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "hr_sign": "negative surface potential",
        "hr_contribution": {
            "bare_surface_level": "mass algebraic only",
            "after_constraint_elimination": "mass and gradient channels can mix through k^2 constraints",
        },
        "constraint_equations": {
            key: expr_text(value) for key, value in equations.items()
        },
        "lapse_compatibility_condition": expr_text(lapse_compatibility_condition()),
        "solutions": {
            "dphi_from_lapse_plus": expr_text(solve_lapse_difference()),
            "B_p": expr_text(shifts["B_p"]),
            "B_m": expr_text(shifts["B_m"]),
            "zeta_after_lapse": expr_text(solve_bending_after_lapse()),
        },
        "canonical_radion": {
            "field_definition": "chi = deltaPhi/sqrt(v)",
            "mass2": expr_text(canonical_radion_mass2()),
        },
        "constraint_closure": {
            "encoded_primary_lapse_equations_present": True,
            "shift_system_solved_algebraically": bool(shifts),
            "bending_solved_after_lapse_substitution": True,
            "lapse_compatibility_derived_from_full_eh_action": False,
            "secondary_hamiltonian_constraint_derived": False,
            "boulware_deser_mode_removed": False,
        },
        "closed_primitives": [
            "provided lapse/shift/bending constraints encoded",
            "shift multipliers solved algebraically",
            "lapse difference solved with explicit compatibility condition",
            "bending solved after lapse substitution",
            "canonical radion mass fixed to 8*lambdaPhi*v^3",
        ],
        "still_open_primitives": [
            "prove the lapse compatibility condition from the full plus/minus Einstein-Hilbert scalar sector",
            "verify exact projection factors from metric perturbations into HR Hessian variables",
            "reinject solutions into full scalar quadratic action and extract final alpha/beta/mass matrix",
        ],
        "prediction_ready": False,
        "needed_inputs": [
            "full EH scalar quadratic action terms containing phi_pm and B_pm, not only their constraint equations",
            "exact normalized map from phi_pm, psi_pm, zeta into HR square-root perturbation variables",
            "boundary condition deciding whether psi_p + v*psi_m = 0 is a physical constraint or is cancelled by omitted EH/source terms",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Constraint Reduction",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Compatibility",
        f"- lapse: `{payload['lapse_compatibility_condition']}`",
        "",
        "## Solutions",
    ]
    for key, value in payload["solutions"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Needed Inputs"])
    lines.extend(f"- {item}" for item in payload["needed_inputs"])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
