from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_curved_branch_missing_contact_solver import missing_delta_n
    from scripts.derive_svt_quadratic_coefficients import MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_curved_branch_missing_contact_solver import missing_delta_n
    from derive_svt_quadratic_coefficients import MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_composite_contact_solver.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_composite_contact_solver.json"

G1, G2 = sp.symbols("gamma1 gamma2")
DPSI, PSI, ZETA = sp.symbols("dpsi psi zeta")


def normalize_delta_n_from_lagrangian(lagrangian: sp.Expr) -> sp.Expr:
    coeff = sp.factor(sp.diff(lagrangian, DPSI, 2) / 2)
    return sp.factor(16 * A**4 * coeff / (MPL2 * K**2))


def uK_raw_lagrangian() -> sp.Expr:
    return sp.factor(
        -3 * H * A**3 * DPSI**2
        + 4 * K**2 * DPSI * ZETA / A**2
        + K**4 * ZETA**2 / A**4
    )


def uK_reduced_lagrangian() -> sp.Expr:
    solution = sp.solve(sp.diff(uK_raw_lagrangian(), ZETA), ZETA)[0]
    return sp.factor(uK_raw_lagrangian().subs(ZETA, solution))


def ghy_taylor_reduced_lagrangian() -> sp.Expr:
    # Supplied Taylor block after v=1 dS branch and chi=2*Mpl2*psi.
    # This is the direct local H contact implied by DeltaK0=6H; it has no k tower.
    chi = 2 * MPL2 * PSI
    return sp.factor(MPL2 * A**3 * (chi**2 / 12) * (6 * H))


def composite_delta_n() -> sp.Expr:
    return sp.factor(
        G1 * normalize_delta_n_from_lagrangian(uK_reduced_lagrangian())
        + G2 * normalize_delta_n_from_lagrangian(ghy_taylor_reduced_lagrangian())
    )


def has_inverse_k(expr: sp.Expr) -> bool:
    return K in sp.factor(expr).as_numer_denom()[1].free_symbols


def polynomial_identity_residual() -> sp.Expr:
    return sp.factor(composite_delta_n() - missing_delta_n())


def solve_constant_gammas() -> list[dict]:
    residual = sp.together(polynomial_identity_residual())
    numerator = sp.Poly(residual.as_numer_denom()[0], H, A, K, MPL2)
    equations = [coeff for _, coeff in numerator.terms()]
    return sp.solve(equations, [G1, G2], dict=True)


@lru_cache(maxsize=None)
def build_payload() -> dict:
    solutions = solve_constant_gammas()
    return {
        "artifact": "svt_curved_branch_composite_contact_solver",
        "status": "two_coefficient_composite_does_not_span_contact_target",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "uK_reduced_lagrangian": expr_text(uK_reduced_lagrangian()),
        "uK_deltaN_per_gamma1": expr_text(normalize_delta_n_from_lagrangian(uK_reduced_lagrangian())),
        "ghy_taylor_lagrangian": expr_text(ghy_taylor_reduced_lagrangian()),
        "ghy_deltaN_per_gamma2": expr_text(
            normalize_delta_n_from_lagrangian(ghy_taylor_reduced_lagrangian())
        ),
        "composite_deltaN": expr_text(composite_delta_n()),
        "target_missing_deltaN": expr_text(missing_delta_n()),
        "constant_gamma_solutions": [
            {str(key): expr_text(value) for key, value in solution.items()}
            for solution in solutions
        ],
        "has_constant_gamma_solution": bool(solutions),
        "verdict": {
            "uK_has_k_tower_after_zeta_elimination": K in normalize_delta_n_from_lagrangian(uK_reduced_lagrangian()).free_symbols,
            "uK_has_inverse_k_pole_after_zeta_elimination": has_inverse_k(
                normalize_delta_n_from_lagrangian(uK_reduced_lagrangian())
            ),
            "ghy_has_k_tower": K in normalize_delta_n_from_lagrangian(ghy_taylor_reduced_lagrangian()).free_symbols,
            "ghy_has_inverse_k_pole": has_inverse_k(
                normalize_delta_n_from_lagrangian(ghy_taylor_reduced_lagrangian())
            ),
            "two_constant_coefficients_close_target": bool(solutions),
            "prediction_ready": False,
        },
        "needed_inputs": [
            "full uK invariant before reducing zeta, including all dS shear and shift terms",
            "additional independent local invariants if gamma1,gamma2 are required to be constants",
            "or a derivation allowing gamma1,gamma2 to be fixed functions, not free fit parameters",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Composite Contact Solver",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        f"- uK_deltaN_per_gamma1: `{payload['uK_deltaN_per_gamma1']}`",
        f"- ghy_deltaN_per_gamma2: `{payload['ghy_deltaN_per_gamma2']}`",
        f"- has_constant_gamma_solution: `{payload['has_constant_gamma_solution']}`",
        "",
        "## Needed Inputs",
    ]
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
