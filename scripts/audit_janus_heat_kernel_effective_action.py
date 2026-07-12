from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class CountertermTarget:
    target_x: float
    target_exponent: float
    fitted_local_coefficient: float
    derivative_at_target: float
    curvature_at_target: float


@dataclass(frozen=True)
class HeatKernelEffectiveActionAudit:
    circumference: float
    heat_time: float
    holonomies: tuple[float, ...]
    direct_poisson_errors: tuple[float, ...]
    local_poisson_term: float
    quarter_first_winding_weight: float
    quarter_second_winding_weight: float
    antiperiodic_first_winding_weight: float
    quarter_to_antiperiodic_leading_magnitude_ratio: float
    local_action_midpoint_residual: float
    counterterm_targets: tuple[CountertermTarget, ...]
    fitted_coefficients_are_distinct: bool
    all_checks_pass: bool
    conclusion: str


def direct_circle_heat_trace(
    circumference: float,
    heat_time: float,
    holonomy: float,
    cutoff: int = 100,
) -> float:
    if circumference <= 0.0 or heat_time <= 0.0:
        raise ValueError("circumference and heat_time must be positive")
    return sum(
        math.exp(
            -heat_time
            * (2.0 * math.pi * (mode + holonomy) / circumference) ** 2
        )
        for mode in range(-cutoff, cutoff + 1)
    )


def poisson_circle_heat_trace(
    circumference: float,
    heat_time: float,
    holonomy: float,
    cutoff: int = 30,
) -> float:
    if circumference <= 0.0 or heat_time <= 0.0:
        raise ValueError("circumference and heat_time must be positive")
    prefactor = circumference / math.sqrt(4.0 * math.pi * heat_time)
    winding_sum = sum(
        math.exp(-circumference**2 * winding**2 / (4.0 * heat_time))
        * math.cos(2.0 * math.pi * winding * holonomy)
        for winding in range(-cutoff, cutoff + 1)
    )
    return prefactor * winding_sum


def local_heat_action(
    circle_modulus: float,
    geometric_length: float,
    coefficients: tuple[float, float, float],
) -> float:
    c0, c2, c4 = coefficients
    density = (
        c0 * geometric_length**3
        + c2 * geometric_length
        + c4 / geometric_length
    )
    return circle_modulus * density


def quarter_counterterm_coefficient(nonlocal_weight: float, target_x: float) -> float:
    return 2.0 * nonlocal_weight / (math.exp(2.0 * target_x) + 1.0)


def quarter_local_nonlocal_derivative(
    local_coefficient: float,
    nonlocal_weight: float,
    x: float,
) -> float:
    return local_coefficient - 2.0 * nonlocal_weight / (
        math.exp(2.0 * x) + 1.0
    )


def quarter_local_nonlocal_curvature(nonlocal_weight: float, x: float) -> float:
    exponent = math.exp(2.0 * x)
    return 4.0 * nonlocal_weight * exponent / (exponent + 1.0) ** 2


def build_audit() -> HeatKernelEffectiveActionAudit:
    circumference = 3.7
    heat_time = 0.45
    holonomies = (0.0, 0.25, 0.5)

    errors = tuple(
        abs(
            direct_circle_heat_trace(
                circumference, heat_time, holonomy, cutoff=120
            )
            - poisson_circle_heat_trace(
                circumference, heat_time, holonomy, cutoff=30
            )
        )
        for holonomy in holonomies
    )

    local_term = circumference / math.sqrt(4.0 * math.pi * heat_time)
    quarter_w1 = math.cos(2.0 * math.pi * 1 * 0.25)
    quarter_w2 = math.cos(2.0 * math.pi * 2 * 0.25)
    anti_w1 = math.cos(2.0 * math.pi * 1 * 0.5)

    quarter_leading = math.exp(-circumference**2 / heat_time)
    anti_leading = math.exp(-circumference**2 / (4.0 * heat_time))
    suppression_ratio = quarter_leading / anti_leading

    coefficients = (0.7, -0.2, 1.1)
    geometric_length = 2.3
    center = 4.0
    displacement = 0.6
    midpoint_residual = (
        2.0 * local_heat_action(center, geometric_length, coefficients)
        - local_heat_action(center - displacement, geometric_length, coefficients)
        - local_heat_action(center + displacement, geometric_length, coefficients)
    )

    nonlocal_weight = 1.7
    target_x_values = (0.25, 0.8, 1.6, 2.4)
    targets = tuple(
        CountertermTarget(
            target_x=target_x,
            target_exponent=math.exp(2.0 * target_x),
            fitted_local_coefficient=quarter_counterterm_coefficient(
                nonlocal_weight, target_x
            ),
            derivative_at_target=quarter_local_nonlocal_derivative(
                quarter_counterterm_coefficient(nonlocal_weight, target_x),
                nonlocal_weight,
                target_x,
            ),
            curvature_at_target=quarter_local_nonlocal_curvature(
                nonlocal_weight, target_x
            ),
        )
        for target_x in target_x_values
    )

    fitted_coefficients = [item.fitted_local_coefficient for item in targets]
    coefficients_distinct = len(set(round(value, 14) for value in fitted_coefficients)) == len(
        fitted_coefficients
    )

    checks = [
        all(error < 1.0e-12 for error in errors),
        local_term > 0.0,
        abs(quarter_w1) < 1.0e-14,
        math.isclose(quarter_w2, -1.0, abs_tol=1.0e-15),
        math.isclose(anti_w1, -1.0, abs_tol=1.0e-15),
        0.0 < suppression_ratio < 1.0,
        abs(midpoint_residual) < 1.0e-12,
        all(
            0.0 < target.fitted_local_coefficient < nonlocal_weight
            for target in targets
        ),
        all(abs(target.derivative_at_target) < 1.0e-14 for target in targets),
        all(target.curvature_at_target > 0.0 for target in targets),
        coefficients_distinct,
    ]

    return HeatKernelEffectiveActionAudit(
        circumference=circumference,
        heat_time=heat_time,
        holonomies=holonomies,
        direct_poisson_errors=errors,
        local_poisson_term=local_term,
        quarter_first_winding_weight=quarter_w1,
        quarter_second_winding_weight=quarter_w2,
        antiperiodic_first_winding_weight=anti_w1,
        quarter_to_antiperiodic_leading_magnitude_ratio=suppression_ratio,
        local_action_midpoint_residual=midpoint_residual,
        counterterm_targets=targets,
        fitted_coefficients_are_distinct=coefficients_distinct,
        all_checks_pass=all(checks),
        conclusion=(
            "Poisson resummation separates a holonomy-independent local term "
            "from nonlocal windings. Quarter holonomy kills the first winding, "
            "so its leading signal is more strongly suppressed than the "
            "antiperiodic signal. Local heat-kernel terms are affine in the "
            "circle modulus and cannot stabilize it alone. A finite local term "
            "can stabilize the quarter determinant, but its coefficient can be "
            "chosen to place the minimum at any target modulus; without an "
            "independent renormalization law this is hidden fitting."
        ),
    )


def main() -> int:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    return 0 if audit.all_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
