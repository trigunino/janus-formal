from __future__ import annotations

import json
import os
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
REPORT_PATH = REPORT_DIR / "bimetric_minisuperspace_dirac_constraints.md"
JSON_PATH = REPORT_DIR / "bimetric_minisuperspace_dirac_constraints.json"

A_PLUS, A_MINUS = sp.symbols("a_plus a_minus", positive=True)
P_PLUS, P_MINUS = sp.symbols("p_plus p_minus")
M_PLUS2, M_MINUS2 = sp.symbols("M_plus2 M_minus2", positive=True)
N_PLUS, N_MINUS = sp.symbols("N_plus N_minus", nonzero=True)
BETA0, BETA1, BETA2, BETA3, BETA4 = sp.symbols("beta0 beta1 beta2 beta3 beta4")


def ratio() -> sp.Expr:
    return A_MINUS / A_PLUS


def plus_potential_polynomial(r: sp.Expr) -> sp.Expr:
    return BETA0 + 3 * BETA1 * r + 3 * BETA2 * r**2 + BETA3 * r**3


def minus_potential_polynomial(r: sp.Expr) -> sp.Expr:
    return BETA1 + 3 * BETA2 * r + 3 * BETA3 * r**2 + BETA4 * r**3


def constraints() -> tuple[sp.Expr, sp.Expr]:
    r = ratio()
    c_plus = -P_PLUS**2 / (12 * M_PLUS2 * A_PLUS) + A_PLUS**3 * plus_potential_polynomial(r)
    c_minus = -P_MINUS**2 / (12 * M_MINUS2 * A_MINUS) + A_PLUS**3 * minus_potential_polynomial(r)
    return sp.factor(c_plus), sp.factor(c_minus)


def poisson(first: sp.Expr, second: sp.Expr) -> sp.Expr:
    return sp.factor(
        sp.diff(first, A_PLUS) * sp.diff(second, P_PLUS)
        - sp.diff(first, P_PLUS) * sp.diff(second, A_PLUS)
        + sp.diff(first, A_MINUS) * sp.diff(second, P_MINUS)
        - sp.diff(first, P_MINUS) * sp.diff(second, A_MINUS)
    )


def canonical_data() -> dict[str, sp.Expr]:
    c_plus, c_minus = constraints()
    secondary = poisson(c_plus, c_minus)
    hamiltonian = N_PLUS * c_plus + N_MINUS * c_minus
    return {
        "constraint_plus": c_plus,
        "constraint_minus": c_minus,
        "hamiltonian": sp.factor(hamiltonian),
        "secondary_candidate": sp.factor(secondary),
        "preserve_plus": sp.factor(poisson(c_plus, hamiltonian)),
        "preserve_minus": sp.factor(poisson(c_minus, hamiltonian)),
        "preserve_secondary": sp.factor(poisson(secondary, hamiltonian)),
    }


def sample_secondary() -> sp.Expr:
    data = canonical_data()
    sample = {
        A_PLUS: 1,
        A_MINUS: 2,
        P_PLUS: 3,
        P_MINUS: 5,
        M_PLUS2: 7,
        M_MINUS2: 11,
        BETA0: 0,
        BETA1: 1,
        BETA2: 2,
        BETA3: 1,
        BETA4: 0,
    }
    return sp.factor(data["secondary_candidate"].subs(sample))


def constrained_sample() -> dict[sp.Symbol, sp.Expr]:
    c_plus, c_minus = constraints()
    sample = {
        A_PLUS: sp.Integer(1), A_MINUS: sp.Integer(2), P_PLUS: sp.Integer(3),
        M_PLUS2: sp.Integer(7), M_MINUS2: sp.Integer(11),
        BETA1: sp.Integer(1), BETA2: sp.Integer(2), BETA3: sp.Integer(1),
    }
    sample[P_MINUS] = sp.factor(
        sample[M_MINUS2] * sample[A_MINUS] * sample[P_PLUS]
        / (sample[M_PLUS2] * sample[A_PLUS])
    )
    sample[BETA0] = sp.solve(c_plus.subs(sample), BETA0)[0]
    sample[BETA4] = sp.solve(c_minus.subs(sample), BETA4)[0]
    return sample


def local_constraint_rank() -> int:
    data = canonical_data()
    jacobian = sp.Matrix(
        [data["constraint_plus"], data["constraint_minus"], data["secondary_candidate"]]
    ).jacobian([A_PLUS, P_PLUS, A_MINUS, P_MINUS])
    return int(jacobian.subs(constrained_sample()).rank())


def constrained_sample_residuals() -> list[sp.Expr]:
    data = canonical_data()
    sample = constrained_sample()
    return [
        sp.factor(data[key].subs(sample))
        for key in ("constraint_plus", "constraint_minus", "secondary_candidate")
    ]


def text(expr: sp.Expr) -> str:
    return str(sp.factor(expr)).replace("**", "^")


def build_payload() -> dict:
    data = canonical_data()
    secondary = data["secondary_candidate"]
    return {
        "artifact": "bimetric_minisuperspace_dirac_constraints",
        "status": "secondary_constraint_candidate_derived_in_diagonal_minisuperspace",
        "fit_used": False,
        "free_parameters_fitted_to_data": [],
        "ansatz": "H=N_plus*C_plus+N_minus*C_minus on diagonal FLRW phase space",
        "constraints": {
            "C_plus": text(data["constraint_plus"]),
            "C_minus": text(data["constraint_minus"]),
        },
        "secondary_candidate": text(secondary),
        "secondary_is_nonzero_polynomial": sp.simplify(secondary) != 0,
        "sample_secondary": text(sample_secondary()),
        "factor_branches": {
            "kinematic": "M_minus2*a_minus*p_plus-M_plus2*a_plus*p_minus=0",
            "potential": "beta1*a_plus^2+2*beta2*a_plus*a_minus+beta3*a_minus^2=0",
        },
        "local_constraint_rank_at_exact_sample": local_constraint_rank(),
        "local_secondary_independence_witnessed": local_constraint_rank() == 3,
        "constrained_sample_residuals": [text(value) for value in constrained_sample_residuals()],
        "preservation": {
            "dot_C_plus": text(data["preserve_plus"]),
            "dot_C_minus": text(data["preserve_minus"]),
            "dot_secondary": text(data["preserve_secondary"]),
            "dot_C_plus_matches_Nminus_secondary": sp.simplify(
                data["preserve_plus"] - N_MINUS * secondary
            ) == 0,
            "dot_C_minus_matches_minus_Nplus_secondary": sp.simplify(
                data["preserve_minus"] + N_PLUS * secondary
            ) == 0,
        },
        "closure": {
            "primary_lapse_constraints_derived": True,
            "primary_poisson_bracket_computed": True,
            "secondary_candidate_derived": True,
            "secondary_independence_global_rank_proved": False,
            "secondary_independence_local_rank_witnessed": local_constraint_rank() == 3,
            "full_adm_shift_redefinition_included": False,
            "boulware_deser_mode_removed_in_full_field_theory": False,
        },
        "interpretation": (
            "For nonzero lapses, preservation of both primary constraints requires "
            "the nontrivial bracket C_secondary={C_plus,C_minus} to vanish. "
            "Preservation of C_secondary is linear in the lapses and generically fixes "
            "a lapse combination; full BD removal still requires the unreduced ADM rank count."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# Bimetric Minisuperspace Dirac Constraints",
            "",
            f"Status: `{payload['status']}`",
            f"Secondary nonzero: `{payload['secondary_is_nonzero_polynomial']}`",
            f"Sample secondary: `{payload['sample_secondary']}`",
            "",
            payload["interpretation"],
        ]
    )


def write_reports() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
