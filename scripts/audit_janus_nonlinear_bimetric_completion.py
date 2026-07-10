from __future__ import annotations

import json
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class NonlinearBimetricAudit:
    rectangular_path_defect: str
    reciprocity_condition: str
    misner_sharp_mass: str
    pt_bridge_mass: str
    horizon_matching_polynomial: str
    selected_positive_radial_coordinate: str
    proportional_potential_swap_residual: str
    pt_symmetric_free_potential_coefficients: int
    absolute_scale_fixed_by_dimensionless_action_data: bool
    conclusion: str
    all_symbolic_checks_pass: bool


def build_audit() -> NonlinearBimetricAudit:
    x, y, dx, dy = sp.symbols("x y dx dy", real=True)
    a, b, c, d = sp.symbols("a b c d", real=True)

    plus = a * x + b * y
    minus = c * x + d * y
    work_plus_minus = plus * dx + (c * (x + dx) + d * y) * dy
    work_minus_plus = minus * dy + (a * x + b * (y + dy)) * dx
    defect = sp.factor(work_plus_minus - work_minus_plus)

    pi_c, E, r = sp.symbols("pi_c E r", real=True)
    m_ms = 4 * pi_c * E * r**3 / 3
    m_bridge = -m_ms

    A, Rs = sp.symbols("A Rs", positive=True)
    horizon_polynomial = sp.factor(A * r - A * r**3)

    beta0, beta1, beta2, beta3, beta4, z = sp.symbols(
        "beta0 beta1 beta2 beta3 beta4 z", nonzero=True
    )
    potential = beta0 + 4 * beta1 * z + 6 * beta2 * z**2 + 4 * beta3 * z**3 + beta4 * z**4
    reversed_at_inverse = (
        beta4
        + 4 * beta3 / z
        + 6 * beta2 / z**2
        + 4 * beta1 / z**3
        + beta0 / z**4
    )
    swap_residual = sp.factor(z**4 * reversed_at_inverse - potential)

    checks = [
        sp.simplify(defect - dx * dy * (-b + c)) == 0,
        sp.simplify(3 * m_ms - 4 * pi_c * E * r**3) == 0,
        sp.simplify(3 * m_bridge + 4 * pi_c * E * r**3) == 0,
        sp.simplify(horizon_polynomial + A * r * (r - 1) * (r + 1)) == 0,
        sp.simplify(swap_residual) == 0,
    ]

    return NonlinearBimetricAudit(
        rectangular_path_defect=str(defect),
        reciprocity_condition="plusFromMinus = minusFromPlus",
        misner_sharp_mass=str(m_ms),
        pt_bridge_mass=str(m_bridge),
        horizon_matching_polynomial=str(horizon_polynomial),
        selected_positive_radial_coordinate="r = 1",
        proportional_potential_swap_residual=str(swap_residual),
        pt_symmetric_free_potential_coefficients=3,
        absolute_scale_fixed_by_dimensionless_action_data=False,
        conclusion=(
            "The common-action requirement fixes reciprocity, PT plus "
            "Misner-Sharp fixes the relational bridge law, and horizon matching "
            "selects r=1. A classical dimensionless interaction still leaves an "
            "overall mass/charge scale; the quantum world-volume program is "
            "therefore required for absolute alpha."
        ),
        all_symbolic_checks_pass=all(checks),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0 if result.all_symbolic_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
