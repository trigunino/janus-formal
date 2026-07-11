from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class FundamentalGeometryDAudit:
    hopf_compatible_total_reversal_possible: bool
    spectral_circle_modulus_squared: str
    spectral_circle_modulus: float
    alpha_over_geometry_length_unit_charge: float
    cleared_alpha_ratio_residual: str
    rp4_pin_plus: bool
    rp4_pin_minus: bool
    twisted_hopf_pin_plus_if_target_classes_vanish: bool
    twisted_hopf_pin_minus_if_target_classes_vanish: bool
    conclusion: str
    all_symbolic_checks_pass: bool


def build_audit() -> FundamentalGeometryDAudit:
    """Audit the first theorem-level consequences of Program D."""

    # A primitive Hopf-bundle automorphism has matching fiber/base orientation
    # signs.  The product parity is their XOR, hence always preserving.
    hopf_reversal_possible = any(
        fiber == base and (fiber ^ base)
        for fiber in (False, True)
        for base in (False, True)
    )

    T, pi_c, c_q, A, L, q = sp.symbols(
        "T pi_c c_q A L q", positive=True
    )

    sphere_mode = sp.Integer(2) / L**2
    circle_mode = (2 * pi_c / (L * T)) ** 2
    isotropy_solution = sp.solve(
        sp.Eq(sphere_mode, circle_mode), T**2, dict=True
    )[0][T**2]

    # q L^2 = 2 c_q and 16 q^2 A^4 = 1.
    q_sub = 2 * c_q / L**2
    cleared_ratio = sp.factor(
        64 * c_q**2 * A**4 - L**4
    )
    flux_substituted = sp.factor(
        (16 * q**2 * A**4 - 1).subs(q, q_sub) * L**4
    )
    ratio_residual = sp.simplify(flux_substituted - cleared_ratio / 4)

    alpha_ratio = 1.0 / (2.0 * math.sqrt(2.0))
    T_value = math.sqrt(2.0) * math.pi

    # Obstruction arithmetic in Z2.
    def pin_plus(w2: int) -> bool:
        return w2 % 2 == 0

    def pin_minus(w2: int, w1_squared: int) -> bool:
        return (w2 + w1_squared) % 2 == 0

    checks = [
        not hopf_reversal_possible,
        sp.simplify(isotropy_solution - 2 * pi_c**2) == 0,
        ratio_residual == 0,
        math.isclose(alpha_ratio**2, 1.0 / 8.0, rel_tol=1.0e-15),
        pin_plus(0),
        not pin_minus(0, 1),
        pin_plus(0),
        pin_minus(0, 0),
    ]

    return FundamentalGeometryDAudit(
        hopf_compatible_total_reversal_possible=hopf_reversal_possible,
        spectral_circle_modulus_squared=str(isotropy_solution),
        spectral_circle_modulus=T_value,
        alpha_over_geometry_length_unit_charge=alpha_ratio,
        cleared_alpha_ratio_residual=str(ratio_residual),
        rp4_pin_plus=pin_plus(0),
        rp4_pin_minus=pin_minus(0, 1),
        twisted_hopf_pin_plus_if_target_classes_vanish=pin_plus(0),
        twisted_hopf_pin_minus_if_target_classes_vanish=pin_minus(0, 0),
        conclusion=(
            "The ordinary primitive Hopf U(1) cannot descend through an "
            "orientation-reversing S3 monodromy. The canonical throat route "
            "survives, and a spectral-isotropy plus unit-charge lock predicts "
            "A/L = 1/(2*sqrt(2)) conditionally."
        ),
        all_symbolic_checks_pass=all(checks),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0 if result.all_symbolic_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
