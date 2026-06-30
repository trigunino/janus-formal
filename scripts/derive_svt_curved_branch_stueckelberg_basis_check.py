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
REPORT_PATH = REPORT_DIR / "svt_curved_branch_stueckelberg_basis_check.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_stueckelberg_basis_check.json"

ZT, DZT, PSI, DPSI = sp.symbols("tilde_zeta_A dtilde_zeta_A psi dpsi")
BP, CHI, DCHI = sp.symbols("B_p chi dchi")


def literal_diagonal_lagrangian() -> sp.Expr:
    return sp.factor(
        sp.Rational(1, 2) * A * K**2 * DZT**2
        - 2 * MPL2 * A**2 * K**2 * DPSI * ZT
        - 44 * MPL2 * H * A**3 * K**2 * PSI * ZT
    )


def literal_momentum_solution() -> sp.Expr:
    return sp.factor(sp.solve(sp.diff(literal_diagonal_lagrangian(), DZT), DZT)[0])


def velocity_coupled_variant() -> sp.Expr:
    source = 2 * MPL2 * A * DPSI + 44 * MPL2 * H * A**2 * PSI
    return sp.factor(sp.Rational(1, 2) * A * K**2 * DZT**2 - A * K**2 * source * DZT)


def velocity_variant_solution() -> sp.Expr:
    return sp.factor(sp.solve(sp.diff(velocity_coupled_variant(), DZT), DZT)[0])


def velocity_variant_delta_lagrangian() -> sp.Expr:
    solution = velocity_variant_solution()
    return sp.factor(velocity_coupled_variant().subs(DZT, solution))


def normalized_velocity_variant_delta_n() -> sp.Expr:
    coeff = sp.factor(sp.diff(velocity_variant_delta_lagrangian(), DPSI, 2) / 2)
    return sp.factor(16 * A**4 * coeff / (MPL2 * K**2))


def shifted_action_candidate() -> sp.Expr:
    return sp.factor(
        sp.Rational(1, 2) * A * K**2 * DZT**2
        + MPL2 * ((K**2 / A**2) * BP**2 - 4 * H * BP * DPSI)
        - (K / A) * BP * ((K**2 / A**2) * DZT - 4 * MPL2 * H * PSI)
        - 2 * MPL2 * (K / A) * DZT * (DPSI - DCHI)
        - 44 * MPL2 * H * K**2 * ZT * PSI
    )


def shifted_action_solution_b() -> sp.Expr:
    return sp.factor(sp.solve(sp.diff(shifted_action_candidate(), BP), BP)[0])


def shifted_action_after_b() -> sp.Expr:
    return sp.factor(sp.cancel(shifted_action_candidate().subs(BP, shifted_action_solution_b())))


def shifted_action_solution_dzt() -> sp.Expr:
    return sp.factor(sp.solve(sp.diff(shifted_action_after_b(), DZT), DZT)[0])


def shifted_action_final() -> sp.Expr:
    return sp.factor(sp.cancel(shifted_action_after_b().subs(DZT, shifted_action_solution_dzt())))


def normalized_shifted_action_delta_n() -> sp.Expr:
    projected = shifted_action_final().subs({DCHI: 2 * MPL2 * DPSI, CHI: 2 * MPL2 * PSI})
    coeff = sp.factor(sp.diff(projected, DPSI, 2) / 2)
    return sp.factor(16 * A**4 * coeff / (MPL2 * K**2))


@lru_cache(maxsize=None)
def build_payload() -> dict:
    literal_solution = literal_momentum_solution()
    variant_delta = normalized_velocity_variant_delta_n()
    shifted_delta = normalized_shifted_action_delta_n()
    required = required_delta_for_constant_alpha()
    return {
        "artifact": "svt_curved_branch_stueckelberg_basis_check",
        "status": "proposed_stueckelberg_basis_does_not_derive_required_delta",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "literal_lagrangian": expr_text(literal_diagonal_lagrangian()),
        "literal_dL_ddtilde_solution": expr_text(literal_solution),
        "literal_matches_claimed_solution": sp.simplify(
            literal_solution
            - (2 * MPL2 * A * DPSI + 44 * MPL2 * H * A**2 * PSI)
        )
        == 0,
        "velocity_coupled_variant": {
            "lagrangian": expr_text(velocity_coupled_variant()),
            "solution": expr_text(velocity_variant_solution()),
            "normalized_deltaN": expr_text(variant_delta),
            "residual_vs_required": expr_text(sp.factor(variant_delta - required)),
            "matches_required_delta": sp.simplify(variant_delta - required) == 0,
        },
        "shifted_action_candidate": {
            "lagrangian": expr_text(shifted_action_candidate()),
            "B_p_solution": expr_text(shifted_action_solution_b()),
            "dtilde_solution": expr_text(shifted_action_solution_dzt()),
            "normalized_deltaN": expr_text(shifted_delta),
            "residual_vs_required": expr_text(sp.factor(shifted_delta - required)),
            "matches_required_delta": sp.simplify(shifted_delta - required) == 0,
        },
        "required_deltaN": expr_text(required),
        "verdict": {
            "literal_formula_solves_to_claimed_velocity": False,
            "velocity_variant_matches_required_delta": sp.simplify(variant_delta - required)
            == 0,
            "shifted_action_candidate_matches_required_delta": sp.simplify(
                shifted_delta - required
            )
            == 0,
            "prediction_ready": False,
            "reason": (
                "The written Lagrangian couples dpsi to zeta, not to dzeta, so "
                "solving dL/ddzeta gives dzeta=0. A velocity-coupled repair gives "
                "the claimed dzeta equation but still does not reproduce required DeltaN. "
                "The shifted B_p-first candidate is also tested explicitly."
            ),
        },
        "needed_inputs": [
            "a Stueckelberg-shifted full action showing whether the source multiplies zeta_A or dot(zeta_A)",
            "a derived cancellation of inverse-k terms after including B_p in the same action, not after B_p elimination",
            "a direct equality proof from the shifted action to required_deltaN",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Stueckelberg Basis Check",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        f"- literal_dL_ddtilde_solution: `{payload['literal_dL_ddtilde_solution']}`",
        f"- literal_matches_claimed_solution: `{payload['literal_matches_claimed_solution']}`",
        f"- velocity_variant_deltaN: `{payload['velocity_coupled_variant']['normalized_deltaN']}`",
        f"- shifted_action_deltaN: `{payload['shifted_action_candidate']['normalized_deltaN']}`",
        f"- required_deltaN: `{payload['required_deltaN']}`",
        f"- velocity_variant_matches_required_delta: `{payload['velocity_coupled_variant']['matches_required_delta']}`",
        f"- shifted_action_matches_required_delta: `{payload['shifted_action_candidate']['matches_required_delta']}`",
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
