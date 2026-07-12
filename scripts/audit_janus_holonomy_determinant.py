from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class HolonomyDeterminantAudit:
    quarter_twist: float
    quarter_cosine: float
    product_ratio_cutoff: int
    product_ratio_error: float
    quarter_derivative_at_x1: float
    quarter_has_finite_stationary_point: bool
    interior_twist: float
    interior_stationary_x: float
    interior_stationary_second_derivative: float
    mixed_periodic_weight: float
    mixed_antiperiodic_weight: float
    mixed_stationary_exponential: float
    mixed_stationary_x: float
    mixed_stationary_modulus_for_mass_sqrt2: float
    periodic_quarter_threshold_ratio: float
    first_integer_quarter_weight: int
    periodic_quarter_maximum_x: float
    periodic_quarter_maximum_second_derivative: float
    periodic_quarter_minimum_x: float
    periodic_quarter_minimum_second_derivative: float
    periodic_quarter_minimum_modulus_for_mass_sqrt2: float
    unweighted_first_mode_modulus: float
    mixed_and_unweighted_moduli_equal: bool
    conclusion: str
    all_checks_pass: bool


def truncated_logdet_ratio(
    twist: float,
    x: float,
    reference_x: float,
    cutoff: int,
) -> float:
    """Finite-product approximation to a one-dimensional determinant ratio."""

    if cutoff < 1:
        raise ValueError("cutoff must be positive")
    if x <= 0.0 or reference_x <= 0.0:
        raise ValueError("dimensionless masses must be positive")

    total = 0.0
    for mode in range(-cutoff, cutoff + 1):
        momentum = 2.0 * math.pi * (mode + twist)
        total += math.log(
            (momentum * momentum + x * x)
            / (momentum * momentum + reference_x * reference_x)
        )
    return total


def analytic_logdet_ratio(
    twist: float,
    x: float,
    reference_x: float,
) -> float:
    """Zeta-product ratio proportional to `cosh(x)-cos(2*pi*a)`."""

    cosine = math.cos(2.0 * math.pi * twist)
    return math.log(
        (math.cosh(x) - cosine)
        / (math.cosh(reference_x) - cosine)
    )


def renormalized_holonomy_potential(twist: float, x: float) -> float:
    """Remove the local term linear in x from the determinant magnitude."""

    if x <= 0.0:
        raise ValueError("x must be positive")
    cosine = math.cos(2.0 * math.pi * twist)
    radial = math.exp(-x)
    return math.log(1.0 - 2.0 * cosine * radial + radial * radial)


def renormalized_holonomy_derivative(twist: float, x: float) -> float:
    cosine = math.cos(2.0 * math.pi * twist)
    radial = math.exp(-x)
    factor = 1.0 - 2.0 * cosine * radial + radial * radial
    return 2.0 * radial * (cosine - radial) / factor


def numerical_second_derivative(function, x: float, step: float = 1.0e-5) -> float:
    return (function(x + step) - 2.0 * function(x) + function(x - step)) / (
        step * step
    )


def fermionic_mixed_potential(
    x: float,
    periodic_weight: float,
    antiperiodic_weight: float,
) -> float:
    if x <= 0.0:
        raise ValueError("x must be positive")
    periodic = 2.0 * math.log1p(-math.exp(-x))
    antiperiodic = 2.0 * math.log1p(math.exp(-x))
    return -(periodic_weight * periodic + antiperiodic_weight * antiperiodic)


def periodic_quarter_potential(
    x: float,
    periodic_weight: float,
    quarter_weight: float,
) -> float:
    """Bosonic-sign common-mass proxy after local linear subtraction."""

    if x <= 0.0:
        raise ValueError("x must be positive")
    radial = math.exp(-x)
    periodic = 2.0 * math.log1p(-radial)
    quarter = math.log1p(radial * radial)
    return periodic_weight * periodic + quarter_weight * quarter


def build_audit() -> HolonomyDeterminantAudit:
    quarter_twist = 0.25
    quarter_cosine = math.cos(2.0 * math.pi * quarter_twist)

    cutoff = 1000
    x = 1.7
    reference_x = 0.9
    finite_ratio = truncated_logdet_ratio(
        quarter_twist, x, reference_x, cutoff
    )
    analytic_ratio = analytic_logdet_ratio(
        quarter_twist, x, reference_x
    )
    product_error = abs(finite_ratio - analytic_ratio)

    quarter_derivative = renormalized_holonomy_derivative(quarter_twist, 1.0)
    quarter_grid = [0.05 + 0.05 * index for index in range(1, 401)]
    quarter_derivatives = [
        renormalized_holonomy_derivative(quarter_twist, value)
        for value in quarter_grid
    ]
    # The exact quarter derivative is strictly negative for every finite x.
    # A tiny magnitude at large x is asymptotic decay, not a stationary point.
    quarter_all_strictly_negative = all(value < 0.0 for value in quarter_derivatives)
    quarter_has_stationary = not quarter_all_strictly_negative

    # theta=pi/3 gives cos(theta)=1/2, hence exp(-x_*)=1/2 and x_*=log(2).
    interior_twist = 1.0 / 6.0
    interior_x = math.log(2.0)
    interior_second = numerical_second_derivative(
        lambda value: renormalized_holonomy_potential(interior_twist, value),
        interior_x,
    )

    periodic_weight = 2.0
    antiperiodic_weight = 3.0
    stationary_exponential = (
        antiperiodic_weight + periodic_weight
    ) / (antiperiodic_weight - periodic_weight)
    stationary_x = math.log(stationary_exponential)
    mass = math.sqrt(2.0)
    stationary_modulus = stationary_x / mass
    mixed_second = numerical_second_derivative(
        lambda value: fermionic_mixed_potential(
            value, periodic_weight, antiperiodic_weight
        ),
        stationary_x,
    )

    # Periodic versus exact-quarter competition requires q/p >= 2+2*sqrt(2).
    threshold_ratio = 2.0 + 2.0 * math.sqrt(2.0)
    first_integer_quarter_weight = 5
    maximum_x = math.log(2.0)
    minimum_x = math.log(3.0)
    maximum_second = numerical_second_derivative(
        lambda value: periodic_quarter_potential(value, 1.0, 5.0),
        maximum_x,
    )
    minimum_second = numerical_second_derivative(
        lambda value: periodic_quarter_potential(value, 1.0, 5.0),
        minimum_x,
    )
    minimum_modulus = minimum_x / mass

    unweighted_modulus = math.sqrt(2.0) * math.pi
    moduli_equal = math.isclose(
        stationary_modulus, unweighted_modulus, rel_tol=1.0e-12
    )

    checks = [
        abs(quarter_cosine) < 1.0e-14,
        product_error < 2.0e-4,
        quarter_derivative < 0.0,
        quarter_all_strictly_negative,
        not quarter_has_stationary,
        abs(renormalized_holonomy_derivative(interior_twist, interior_x))
        < 1.0e-12,
        interior_second > 0.0,
        math.isclose(stationary_exponential, 5.0, rel_tol=1.0e-15),
        mixed_second > 0.0,
        4.8 < threshold_ratio < 4.9,
        first_integer_quarter_weight > threshold_ratio,
        maximum_second < 0.0,
        minimum_second > 0.0,
        not moduli_equal,
    ]

    return HolonomyDeterminantAudit(
        quarter_twist=quarter_twist,
        quarter_cosine=quarter_cosine,
        product_ratio_cutoff=cutoff,
        product_ratio_error=product_error,
        quarter_derivative_at_x1=quarter_derivative,
        quarter_has_finite_stationary_point=quarter_has_stationary,
        interior_twist=interior_twist,
        interior_stationary_x=interior_x,
        interior_stationary_second_derivative=interior_second,
        mixed_periodic_weight=periodic_weight,
        mixed_antiperiodic_weight=antiperiodic_weight,
        mixed_stationary_exponential=stationary_exponential,
        mixed_stationary_x=stationary_x,
        mixed_stationary_modulus_for_mass_sqrt2=stationary_modulus,
        periodic_quarter_threshold_ratio=threshold_ratio,
        first_integer_quarter_weight=first_integer_quarter_weight,
        periodic_quarter_maximum_x=maximum_x,
        periodic_quarter_maximum_second_derivative=maximum_second,
        periodic_quarter_minimum_x=minimum_x,
        periodic_quarter_minimum_second_derivative=minimum_second,
        periodic_quarter_minimum_modulus_for_mass_sqrt2=minimum_modulus,
        unweighted_first_mode_modulus=unweighted_modulus,
        mixed_and_unweighted_moduli_equal=moduli_equal,
        conclusion=(
            "The zeta-product ratio is reproduced numerically. A single exact "
            "Z4 quarter-holonomy tower, including a positive-weight finite tower "
            "or its PT pair, is monotone and cannot stabilize the circle. A "
            "generic interior holonomy can. Competing sectors can also work: a "
            "fermionic 2:3 periodic/antiperiodic mixture has exp(m*T)=5, while "
            "periodic versus quarter holonomy requires q/p >= 2+2*sqrt(2); the "
            "first integer pair 1:5 gives a local minimum at m*T=log(3). None "
            "of these derived moduli equals the old unweighted crossing, so the "
            "microscopic field content and renormalization must decide."
        ),
        all_checks_pass=all(checks),
    )


def main() -> int:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    return 0 if audit.all_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
