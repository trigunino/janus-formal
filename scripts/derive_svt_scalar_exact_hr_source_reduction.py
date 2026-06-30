from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_quadratic_coefficients import MHR2, MPL2, VEV, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_scalar_exact_hr_source_reduction.md"
JSON_PATH = REPORT_DIR / "svt_scalar_exact_hr_source_reduction.json"

K = sp.Symbol("k", nonzero=True)
PHI_P, PHI_M = sp.symbols("phi_p phi_m")
B_P, B_M = sp.symbols("B_p B_m")
PSI_P, PSI_M = sp.symbols("psi_p psi_m")
DPSI_P, DPSI_M = sp.symbols("dpsi_p dpsi_m")
ZETA = sp.Symbol("zeta")


def h_phi_phi() -> sp.Expr:
    return sp.factor(sp.Rational(3, 2) * (1 + VEV))


def h_bb() -> sp.Expr:
    return sp.factor(4 * VEV / (1 + VEV))


def h_psi_psi() -> sp.Expr:
    return sp.factor(3 * (1 + 1 / VEV))


def h_zeta_zeta() -> sp.Expr:
    return sp.factor((3 * VEV - 3) * K**2)


@lru_cache(maxsize=None)
def exact_hr_surface_density() -> sp.Expr:
    return sp.factor(
        -MHR2
        * MPL2
        * (
            h_phi_phi() * (PHI_P - PHI_M) ** 2
            + h_bb() * K**2 * (B_P - B_M) ** 2
            + h_psi_psi() * (PSI_P - PSI_M) ** 2
            + h_zeta_zeta() * ZETA**2
        )
    )


@lru_cache(maxsize=None)
def exact_hr_sources() -> dict[str, sp.Expr]:
    density = exact_hr_surface_density()
    return {
        "dS_d_phi_p": sp.factor(sp.diff(density, PHI_P)),
        "dS_d_phi_m": sp.factor(sp.diff(density, PHI_M)),
        "dS_d_B_p": sp.factor(sp.diff(density, B_P)),
        "dS_d_B_m": sp.factor(sp.diff(density, B_M)),
        "dS_d_zeta": sp.factor(sp.diff(density, ZETA)),
        "dS_d_psi_p": sp.factor(sp.diff(density, PSI_P)),
        "dS_d_psi_m": sp.factor(sp.diff(density, PSI_M)),
    }


@lru_cache(maxsize=None)
def constraint_equations() -> dict[str, sp.Expr]:
    sources = exact_hr_sources()
    return {
        "lapse_plus": sp.factor(2 * MPL2 * K**2 * PSI_P - sources["dS_d_phi_p"]),
        "lapse_minus": sp.factor(
            2 * MPL2 * VEV * K**2 * PSI_M - sources["dS_d_phi_m"]
        ),
        "shift_plus": sp.factor(
            2 * MPL2 * K**2 * (DPSI_P - K**2 * B_P) - sources["dS_d_B_p"]
        ),
        "shift_minus": sp.factor(
            MPL2 * VEV * (2 * K**2 / VEV**2) * (DPSI_M - K**2 * B_M)
            - sources["dS_d_B_m"]
        ),
        "bending": sp.factor(K**2 * ZETA + sources["dS_d_zeta"]),
    }


def delta_phi_solution() -> sp.Expr:
    equation = constraint_equations()["lapse_plus"]
    phi_p_solution = sp.solve(equation, PHI_P, dict=True)[0][PHI_P]
    return sp.factor(phi_p_solution - PHI_M)


def lapse_compatibility() -> sp.Expr:
    from_plus = delta_phi_solution()
    minus_eq = constraint_equations()["lapse_minus"].subs(PHI_P, PHI_M + from_plus)
    return sp.factor(minus_eq)


def shift_solutions() -> dict[str, sp.Expr]:
    equations = constraint_equations()
    solutions = sp.solve(
        [equations["shift_plus"], equations["shift_minus"]],
        [B_P, B_M],
        dict=True,
        simplify=True,
    )[0]
    return {key.name: sp.factor(value) for key, value in solutions.items()}


def bending_solution() -> sp.Expr:
    equation = constraint_equations()["bending"]
    solutions = sp.solve(equation, ZETA, dict=True, simplify=True)
    if not solutions:
        return sp.Integer(0)
    return sp.factor(solutions[0][ZETA])


def build_payload() -> dict:
    equations = constraint_equations()
    shifts = shift_solutions()
    return {
        "artifact": "svt_scalar_exact_hr_source_reduction",
        "status": "exact_hr_sources_injected_constraints_solved_conditionally",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "hessian_coefficients": {
            "H_phi_phi": expr_text(h_phi_phi()),
            "H_BB": expr_text(h_bb()),
            "H_psi_psi": expr_text(h_psi_psi()),
            "H_zeta_zeta": expr_text(h_zeta_zeta()),
        },
        "surface_density": expr_text(exact_hr_surface_density()),
        "sources": {key: expr_text(value) for key, value in exact_hr_sources().items()},
        "constraint_equations": {
            key: expr_text(value) for key, value in equations.items()
        },
        "solutions": {
            "phi_p_minus_phi_m": expr_text(delta_phi_solution()),
            "lapse_compatibility_after_substitution": expr_text(lapse_compatibility()),
            "B_p": expr_text(shifts["B_p"]),
            "B_m": expr_text(shifts["B_m"]),
            "zeta_generic": expr_text(bending_solution()),
        },
        "verdict": {
            "hr_sources_closed": True,
            "shift_constraints_closed": True,
            "bending_generic_solution_closed": True,
            "lapse_difference_closed": True,
            "lapse_compatibility_still_required": True,
            "phi_sum_gauge_free": True,
        },
        "prediction_ready": False,
        "still_open_primitives": [
            "decide whether psi_p + v*psi_m = 0 is physical or cancelled by omitted EH/source terms",
            "fix gauge or boundary condition for phi_p + phi_m",
            "reinject solved constraints into full EH+HR scalar quadratic action",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Scalar Exact HR Source Reduction",
        "",
        f"Status: `{payload['status']}`",
        f"Fit used: `{payload['fit_used']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Hessian Coefficients",
    ]
    for key, value in payload["hessian_coefficients"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Solutions"])
    for key, value in payload["solutions"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Still Open"])
    lines.extend(f"- {item}" for item in payload["still_open_primitives"])
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
