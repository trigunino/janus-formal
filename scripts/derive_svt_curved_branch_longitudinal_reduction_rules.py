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
REPORT_PATH = REPORT_DIR / "svt_curved_branch_longitudinal_reduction_rules.md"
JSON_PATH = REPORT_DIR / "svt_curved_branch_longitudinal_reduction_rules.json"

DZETA, ZETA = sp.symbols("dzeta_A zeta_A")
DPSI, DCHI = sp.symbols("dpsi dchi")
PSI, CHI = sp.symbols("psi chi")
DDPSI, DDCHI = sp.symbols("ddpsi ddchi")
PZETA = sp.Symbol("P_zeta")


def current_c() -> sp.Expr:
    return 4 * MPL2 * A**2 * K * (DPSI - DCHI)


def coefficient_a() -> sp.Expr:
    return sp.Rational(1, 2) * A * K**2


def coefficient_b() -> sp.Expr:
    return -sp.Rational(3, 2) * H * A * K**2


def effective_longitudinal_form() -> sp.Expr:
    return sp.factor(coefficient_a() * DZETA**2 + coefficient_b() * ZETA * DZETA + current_c() * DZETA)


def schur_contact_delta_lagrangian() -> sp.Expr:
    acoef = coefficient_a()
    c = current_c()
    # Minimal algebraic part supplied by the Legendre/contact reduction.
    return sp.factor(-c**2 / (4 * acoef))


def coefficient_d() -> sp.Expr:
    return sp.Rational(3, 4) * H**2 * A * K**2


def supplied_complete_contact_lagrangian() -> sp.Expr:
    acoef = coefficient_a()
    bcoef = coefficient_b()
    dcoef = coefficient_d()
    c = current_c()
    return sp.factor(
        -c**2 / (4 * acoef)
        + (bcoef / (2 * acoef)) * H * c
        - (dcoef / (4 * acoef**2)) * c**2
        - (1 / (2 * acoef)) * (3 * H * A**2 * c) * c
    )


def d_current_c_source() -> sp.Expr:
    c = current_c()
    derivative = (
        sp.diff(c, A) * H * A
        + sp.diff(c, DPSI) * DDPSI
        + sp.diff(c, DCHI) * DDCHI
    )
    return sp.factor(derivative)


def acceleration_rules() -> dict[sp.Symbol, sp.Expr]:
    return {
        DDPSI: -3 * H * DPSI - (K**2 / A**2) * PSI,
        DDCHI: -3 * H * DCHI - (K**2 / A**2) * CHI,
    }


def spin_torsion_term() -> sp.Expr:
    return 8 * MPL2 * H * A * K**2 * ZETA * PSI


def surface_p_term() -> sp.Expr:
    acoef = coefficient_a()
    c = current_c()
    dc = d_current_c_source().subs(acceleration_rules())
    return sp.factor(
        -A**3
        * (
            (dc * c) / (4 * acoef * H)
            + sp.Rational(3, 8) * (c**2 / acoef)
        )
    )


def revised_total_lagrangian() -> sp.Expr:
    return sp.factor(supplied_complete_contact_lagrangian() + spin_torsion_term() + surface_p_term())


def boundary_projected_delta_lagrangian() -> sp.Expr:
    return sp.factor(schur_contact_delta_lagrangian().subs(DCHI, 2 * MPL2 * DPSI))


def boundary_projected_complete_lagrangian() -> sp.Expr:
    return sp.factor(supplied_complete_contact_lagrangian().subs(DCHI, 2 * MPL2 * DPSI))


def boundary_projected_revised_lagrangian() -> sp.Expr:
    return sp.factor(
        revised_total_lagrangian().subs(
            {
                DCHI: 2 * MPL2 * DPSI,
                CHI: 2 * MPL2 * PSI,
            }
        )
    )


def normalized_delta_n() -> sp.Expr:
    coeff = sp.factor(sp.diff(boundary_projected_delta_lagrangian(), DPSI, 2) / 2)
    return sp.factor(16 * A**4 * coeff / (MPL2 * K**2))


def normalized_complete_delta_n() -> sp.Expr:
    coeff = sp.factor(sp.diff(boundary_projected_complete_lagrangian(), DPSI, 2) / 2)
    return sp.factor(16 * A**4 * coeff / (MPL2 * K**2))


def normalized_revised_delta_n() -> sp.Expr:
    coeff = sp.factor(sp.diff(boundary_projected_revised_lagrangian(), DPSI, 2) / 2)
    return sp.factor(16 * A**4 * coeff / (MPL2 * K**2))


@lru_cache(maxsize=None)
def build_payload() -> dict:
    delta_n = normalized_delta_n()
    complete_delta_n = normalized_complete_delta_n()
    revised_delta_n = normalized_revised_delta_n()
    required = required_delta_for_constant_alpha()
    return {
        "artifact": "svt_curved_branch_longitudinal_reduction_rules",
        "status": "ds_reduction_rules_do_not_yield_required_delta",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "reduction_coefficients": {
            "A": expr_text(coefficient_a()),
            "B": expr_text(coefficient_b()),
            "D": expr_text(coefficient_d()),
            "C": expr_text(current_c()),
        },
        "effective_longitudinal_form": expr_text(effective_longitudinal_form()),
        "schur_contact_delta_lagrangian": expr_text(schur_contact_delta_lagrangian()),
        "supplied_complete_contact_lagrangian": expr_text(supplied_complete_contact_lagrangian()),
        "dC_source_after_rules": expr_text(d_current_c_source().subs(acceleration_rules())),
        "spin_torsion_term": expr_text(spin_torsion_term()),
        "surface_P_term": expr_text(surface_p_term()),
        "revised_total_lagrangian": expr_text(revised_total_lagrangian()),
        "boundary_projected_delta_lagrangian": expr_text(boundary_projected_delta_lagrangian()),
        "boundary_projected_complete_lagrangian": expr_text(boundary_projected_complete_lagrangian()),
        "boundary_projected_revised_lagrangian": expr_text(boundary_projected_revised_lagrangian()),
        "normalized_deltaN": expr_text(delta_n),
        "normalized_complete_deltaN": expr_text(complete_delta_n),
        "normalized_revised_deltaN": expr_text(revised_delta_n),
        "required_deltaN": expr_text(required),
        "residual": expr_text(sp.factor(delta_n - required)),
        "complete_residual": expr_text(sp.factor(complete_delta_n - required)),
        "revised_residual": expr_text(sp.factor(revised_delta_n - required)),
        "matches_required_delta": sp.simplify(delta_n - required) == 0,
        "complete_matches_required_delta": sp.simplify(complete_delta_n - required) == 0,
        "revised_matches_required_delta": sp.simplify(revised_delta_n - required) == 0,
        "verdict": {
            "normalization_map_applied": True,
            "minimal_contact_reduction_closed": True,
            "H_B_term_included_as_symbolic_coefficient": True,
            "supplied_complete_formula_evaluated": True,
            "revised_surface_spin_torsion_formula_evaluated": True,
            "required_delta_derived": sp.simplify(revised_delta_n - required) == 0,
            "prediction_ready": False,
            "reason": (
                "The supplied complete contact formula has been evaluated. If "
                "complete_matches_required_delta is false, the remaining missing "
                "piece is not represented by the current A/B/C/D expression."
            ),
        },
        "needed_inputs": [
            "explicit additional terms represented by the ellipsis in DeltaL = -C^2/(4A) + (B/(2A))*H*C ...",
            "exact treatment of P_zeta and total derivative boundary terms",
            "a derived, not fitted, expression for the missing curvature-contact contribution",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# SVT Curved Branch Longitudinal Reduction Rules",
        "",
        f"Status: `{payload['status']}`",
        f"Prediction ready: `{payload['verdict']['prediction_ready']}`",
        "",
        f"- normalized_deltaN: `{payload['normalized_deltaN']}`",
        f"- normalized_complete_deltaN: `{payload['normalized_complete_deltaN']}`",
        f"- normalized_revised_deltaN: `{payload['normalized_revised_deltaN']}`",
        f"- required_deltaN: `{payload['required_deltaN']}`",
        f"- residual: `{payload['residual']}`",
        f"- complete_residual: `{payload['complete_residual']}`",
        f"- revised_residual: `{payload['revised_residual']}`",
        f"- matches_required_delta: `{payload['matches_required_delta']}`",
        f"- complete_matches_required_delta: `{payload['complete_matches_required_delta']}`",
        f"- revised_matches_required_delta: `{payload['revised_matches_required_delta']}`",
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
