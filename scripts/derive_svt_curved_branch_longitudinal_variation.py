from __future__ import annotations

from functools import lru_cache
from pathlib import Path
import json
import os

import sympy as sp

try:
    from scripts.derive_svt_curved_branch_desitter_seed import A, H, K
    from scripts.derive_svt_curved_branch_longitudinal_aether_check import (
        required_delta_for_constant_alpha,
    )
    from scripts.derive_svt_quadratic_coefficients import MPL2, expr_text
except ModuleNotFoundError:  # pragma: no cover - direct script execution
    from derive_svt_curved_branch_desitter_seed import A, H, K
    from derive_svt_curved_branch_longitudinal_aether_check import (
        required_delta_for_constant_alpha,
    )
    from derive_svt_quadratic_coefficients import MPL2, expr_text


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "svt_curved_branch_longitudinal_variation.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_longitudinal_variation.json"

A0, ZETA_A, DZETA_A = sp.symbols("A0 zeta_A dzeta_A")
DPSI, DCHI = sp.symbols("dpsi dchi")


def velocity_combo() -> sp.Expr:
    return -DPSI + DCHI


@lru_cache(maxsize=None)
def longitudinal_aether_lagrangian() -> sp.Expr:
    kphys2 = K**2 / A**2
    return sp.factor(
        A**3
        * (
            sp.Rational(1, 2) * kphys2 * A0**2
            + kphys2 * A0 * DZETA_A
            + sp.Rational(1, 2) * kphys2 * DZETA_A**2
            - sp.Rational(3, 2) * H * kphys2 * ZETA_A * DZETA_A
            - 2 * MPL2 * (K / A) * A0 * velocity_combo()
        )
    )


def solve_a0() -> sp.Expr:
    return sp.factor(sp.solve(sp.diff(longitudinal_aether_lagrangian(), A0), A0)[0])


@lru_cache(maxsize=None)
def reduced_after_a0() -> sp.Expr:
    return sp.factor(sp.cancel(longitudinal_aether_lagrangian().subs(A0, solve_a0())))


def dL_ddzeta() -> sp.Expr:
    return sp.factor(sp.diff(reduced_after_a0(), DZETA_A))


def dL_dzeta() -> sp.Expr:
    return sp.factor(sp.diff(reduced_after_a0(), ZETA_A))


def boundary_constraint_substitution() -> dict[sp.Symbol, sp.Expr]:
    return {
        DCHI: 2 * MPL2 * DPSI,
    }


def kinetic_delta_from_a0_reduction() -> sp.Expr:
    reduced = reduced_after_a0().subs(boundary_constraint_substitution())
    return sp.factor(sp.diff(reduced, DPSI, 2) / 2)


def build_payload() -> dict:
    required = required_delta_for_constant_alpha()
    kinetic_delta = kinetic_delta_from_a0_reduction()
    return {
        "artifact": "svt_curved_branch_longitudinal_variation",
        "status": "longitudinal_variation_does_not_derive_required_delta_without_extra_reduction_rule",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "lagrangian": expr_text(longitudinal_aether_lagrangian()),
        "A0_solution": expr_text(solve_a0()),
        "reduced_after_A0": expr_text(reduced_after_a0()),
        "zeta_variation_terms": {
            "dL_ddzeta": expr_text(dL_ddzeta()),
            "dL_dzeta": expr_text(dL_dzeta()),
            "needs_total_time_derivative_rule": True,
        },
        "boundary_projected_kinetic_delta": expr_text(kinetic_delta),
        "required_delta_for_alpha_5392": expr_text(required),
        "matches_required_delta": sp.simplify(kinetic_delta - required) == 0,
        "verdict": {
            "A0_constraint_solved": True,
            "zetaA_reduction_closed": False,
            "required_delta_derived": False,
            "prediction_ready": False,
            "reason": (
                "The supplied Lagrangian solves A0, but deriving required DeltaN "
                "needs an additional rule for the zeta_A Euler-Lagrange equation, "
                "accelerations, and integrations by parts."
            ),
        },
        "needed_inputs": [
            "explicit time-derivative reduction rule for d/dt(a^n Xdot) terms",
            "how zeta_A acceleration terms are eliminated before collecting alpha_dS",
            "normalization map from the reduced zeta_A action contribution to DeltaN",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Longitudinal Variation",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        f"- A0_solution: `{payload['A0_solution']}`",
        f"- boundary_projected_kinetic_delta: `{payload['boundary_projected_kinetic_delta']}`",
        f"- required_delta_for_alpha_5392: `{payload['required_delta_for_alpha_5392']}`",
        f"- matches_required_delta: `{payload['matches_required_delta']}`",
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
