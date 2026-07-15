from __future__ import annotations

import json
import os
from itertools import combinations
from pathlib import Path

import sympy as sp


REPORT_DIR = Path(os.environ.get("JANUS_REPORT_DIR", "outputs/reports"))
P = sp.symbols("p0:4")
BETA0, BETA1, BETA2, BETA3 = sp.symbols("beta0 beta1 beta2 beta3")


def elementary(values: list[sp.Expr], degree: int) -> sp.Expr:
    return sum((sp.prod(term) for term in combinations(values, degree)), sp.Integer(0))


def y_polynomial(degree: int, component: int) -> sp.Expr:
    eigenvalues = [1 + value for value in P]
    return sp.expand(sum(
        (-1) ** order
        * elementary(eigenvalues, order)
        * eigenvalues[component] ** (degree - order)
        for order in range(degree + 1)
    ))


def interaction_component(component: int = 0) -> sp.Expr:
    betas = [BETA0, BETA1, BETA2, BETA3]
    return sp.expand(sum(
        (-1) ** degree * betas[degree] * y_polynomial(degree, component)
        for degree in range(4)
    ))


def expected_component(component: int = 0) -> sp.Expr:
    transverse = [P[index] for index in range(4) if index != component]
    x1 = elementary(transverse, 1)
    x2 = elementary(transverse, 2)
    x3 = elementary(transverse, 3)
    return sp.expand(
        BETA0 + 3 * BETA1 + 3 * BETA2 + BETA3
        + (BETA1 + 2 * BETA2 + BETA3) * x1
        + (BETA2 + BETA3) * x2
        + BETA3 * x3
    )


def build_payload() -> dict:
    identities = [
        sp.simplify(interaction_component(i) - expected_component(i)) == 0
        for i in range(4)
    ]
    beta1, beta2 = sp.symbols("b1 b2", positive=True)
    alpha1_pt = sp.factor((BETA1 + 2 * BETA2 + BETA3).subs({BETA1: beta1, BETA2: beta2, BETA3: beta1}))
    alpha2_pt = sp.factor((BETA2 + BETA3).subs({BETA2: beta2, BETA3: beta1}))
    return {
        "artifact": "hr_lambda3_beta_combinations",
        "status": "flat_background_X_tensor_coefficients_derived",
        "convention": "sum_n (-1)^n beta_n Y_n(I+Pi)",
        "coefficients": {
            "X0": "beta0+3*beta1+3*beta2+beta3",
            "X1": "beta1+2*beta2+beta3",
            "X2": "beta2+beta3",
            "X3": "beta3",
        },
        "all_four_diagonal_component_identities": identities,
        "pt_branch": {
            "alpha1": str(alpha1_pt),
            "alpha2": str(alpha2_pt),
            "alpha2_over_alpha1": str(sp.factor(alpha2_pt / alpha1_pt)),
            "cubic_mixing_nonzero_on_positive_cone": bool(alpha1_pt.is_positive and alpha2_pt.is_positive),
        },
        "closure": {
            "beta_to_X_mixing_map": all(identities),
            "pt_cubic_mixing_nonzero": True,
            "canonical_radial_coefficient_with_both_bigravity_frames": False,
        },
    }


def write_report() -> dict:
    payload = build_payload()
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    (REPORT_DIR / "hr_lambda3_beta_combinations.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_report(), indent=2))
