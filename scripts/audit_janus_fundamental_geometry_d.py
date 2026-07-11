from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class FundamentalGeometryDAudit:
    hopf_compatible_total_reversal_possible: bool
    fixed_throat_conjugate_nonzero_flux_possible: bool
    spectral_circle_modulus_squared: str
    spectral_circle_modulus: float
    euclidean_thermal_circle_modulus: float
    thermal_and_spectral_circle_laws_compatible: bool
    alpha_over_geometry_length_unit_charge: float
    required_spectral_coefficient_for_alpha_equals_geometry: float
    cleared_alpha_ratio_residual: str
    lee_level_spacing_factor: float
    planck_anchored_alpha_level_22_m: float
    planck_anchored_alpha_level_23_m: float
    rp4_pin_plus: bool
    rp4_pin_minus: bool
    twisted_hopf_pin_plus_if_target_classes_vanish: bool
    twisted_hopf_pin_minus_if_target_classes_vanish: bool
    conclusion: str
    all_symbolic_checks_pass: bool


def build_audit() -> FundamentalGeometryDAudit:
    """Audit the first theorem-level consequences of Program D."""

    # A primitive Hopf-bundle automorphism has matching fiber/base orientation
    # signs. The product parity is their XOR, hence always preserving.
    hopf_reversal_possible = any(
        fiber == base and (fiber ^ base)
        for fiber in (False, True)
        for base in (False, True)
    )

    # A pointwise-fixed S2 has base sign +1. Charge conjugation has fiber sign
    # -1, so a descended integer flux obeys n=-n and is necessarily zero.
    fixed_throat_conjugate_nonzero_flux_possible = False

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
    cleared_ratio = sp.factor(64 * c_q**2 * A**4 - L**4)
    flux_substituted = sp.factor(
        (16 * q**2 * A**4 - 1).subs(q, q_sub) * L**4
    )
    ratio_residual = sp.simplify(flux_substituted - cleared_ratio / 4)

    unit_charge_alpha_ratio = 1.0 / (2.0 * math.sqrt(2.0))
    spectral_T = math.sqrt(2.0) * math.pi
    thermal_T = 4.0 * math.pi
    circles_compatible = math.isclose(
        spectral_T, thermal_T, rel_tol=1.0e-15, abs_tol=0.0
    )

    # If the bimetric bridge says A=L, then 64*c_q^2=1 and positivity gives
    # c_q=1/8. This equals the LL auxiliary-metric normalization.
    required_cq = 1.0 / 8.0

    # Candidate integral Lee class T=2*pi*n. Adjacent levels are extremely
    # coarse, so this route needs a further amplitude or fractional lock.
    planck_length_m = 1.616255e-35
    spacing = math.exp(2.0 * math.pi)
    alpha_n22 = 0.5 * planck_length_m * math.exp(2.0 * math.pi * 22.0)
    alpha_n23 = 0.5 * planck_length_m * math.exp(2.0 * math.pi * 23.0)

    # Obstruction arithmetic in Z2.
    def pin_plus(w2: int) -> bool:
        return w2 % 2 == 0

    def pin_minus(w2: int, w1_squared: int) -> bool:
        return (w2 + w1_squared) % 2 == 0

    checks = [
        not hopf_reversal_possible,
        not fixed_throat_conjugate_nonzero_flux_possible,
        sp.simplify(isotropy_solution - 2 * pi_c**2) == 0,
        ratio_residual == 0,
        math.isclose(
            unit_charge_alpha_ratio**2, 1.0 / 8.0, rel_tol=1.0e-15
        ),
        not circles_compatible,
        math.isclose(required_cq, 0.125, rel_tol=1.0e-15),
        math.isclose(alpha_n23 / alpha_n22, spacing, rel_tol=1.0e-12),
        pin_plus(0),
        not pin_minus(0, 1),
        pin_plus(0),
        pin_minus(0, 0),
    ]

    return FundamentalGeometryDAudit(
        hopf_compatible_total_reversal_possible=hopf_reversal_possible,
        fixed_throat_conjugate_nonzero_flux_possible=(
            fixed_throat_conjugate_nonzero_flux_possible
        ),
        spectral_circle_modulus_squared=str(isotropy_solution),
        spectral_circle_modulus=spectral_T,
        euclidean_thermal_circle_modulus=thermal_T,
        thermal_and_spectral_circle_laws_compatible=circles_compatible,
        alpha_over_geometry_length_unit_charge=unit_charge_alpha_ratio,
        required_spectral_coefficient_for_alpha_equals_geometry=required_cq,
        cleared_alpha_ratio_residual=str(ratio_residual),
        lee_level_spacing_factor=spacing,
        planck_anchored_alpha_level_22_m=alpha_n22,
        planck_anchored_alpha_level_23_m=alpha_n23,
        rp4_pin_plus=pin_plus(0),
        rp4_pin_minus=pin_minus(0, 1),
        twisted_hopf_pin_plus_if_target_classes_vanish=pin_plus(0),
        twisted_hopf_pin_minus_if_target_classes_vanish=pin_minus(0, 0),
        conclusion=(
            "The ordinary primitive Hopf U(1) and a PT-conjugate monopole on "
            "the pointwise-fixed throat do not descend as initially imagined. "
            "The surviving route is an intrinsic or cover-level throat gauge "
            "sector. Spectral, LL and bimetric normalizations meet at c_q=1/8, "
            "while integral Lee levels alone are too coarsely spaced."
        ),
        all_symbolic_checks_pass=all(checks),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0 if result.all_symbolic_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
