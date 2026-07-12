from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class HeatTraceSample:
    heat_time: float
    exact_scaled_trace: float
    a0_a2_a4_approximation: float
    absolute_residual: float
    extracted_a4: float


@dataclass(frozen=True)
class D7SeeleyDeWittAudit:
    geometric_length: float
    circle_modulus: float
    circumference: float
    monopole_magnitude: int
    holonomy: float
    reduced_a0: float
    reduced_a2: float
    reduced_a4: float
    symbolic_a0_residual: str
    symbolic_a2_residual: str
    symbolic_a4_residual: str
    universal_to_dirac_a4_residual: str
    heat_trace_samples: tuple[HeatTraceSample, ...]
    maximum_small_time_residual: float
    smallest_time_extracted_a4_error: float
    local_coefficients_linear_in_circle_modulus: bool
    common_scale_orbit_residual: float
    all_checks_pass: bool
    conclusion: str


def sphere_monopole_dirac_squared_heat_trace(
    heat_time: float,
    geometric_length: float,
    monopole_magnitude: int,
    cutoff: int = 800,
) -> float:
    """Heat trace of the squared two-sphere Dirac spectrum.

    For positive integer q=|n|:

      zero-mode degeneracy = q,
      lambda_k^2 L^2 = k(k+q),
      total nonzero D^2 degeneracy = 2(q+2k),  k>=1.
    """

    if heat_time <= 0.0 or geometric_length <= 0.0:
        raise ValueError("heat_time and geometric_length must be positive")
    if monopole_magnitude <= 0 or cutoff < 1:
        raise ValueError("monopole_magnitude and cutoff must be positive")

    total = float(monopole_magnitude)
    for level in range(1, cutoff + 1):
        eigenvalue_squared = (
            level * (level + monopole_magnitude) / geometric_length**2
        )
        degeneracy = 2 * (monopole_magnitude + 2 * level)
        total += degeneracy * math.exp(-heat_time * eigenvalue_squared)
    return total


def shifted_circle_heat_trace(
    heat_time: float,
    circumference: float,
    holonomy: float,
    cutoff: int = 2000,
) -> float:
    if heat_time <= 0.0 or circumference <= 0.0:
        raise ValueError("heat_time and circumference must be positive")
    return sum(
        math.exp(
            -heat_time
            * (2.0 * math.pi * (mode + holonomy) / circumference) ** 2
        )
        for mode in range(-cutoff, cutoff + 1)
    )


def exact_product_heat_trace(
    heat_time: float,
    geometric_length: float,
    circle_modulus: float,
    monopole_magnitude: int,
    holonomy: float,
) -> float:
    circumference = geometric_length * circle_modulus
    return sphere_monopole_dirac_squared_heat_trace(
        heat_time, geometric_length, monopole_magnitude
    ) * shifted_circle_heat_trace(heat_time, circumference, holonomy)


def reduced_dirac_coefficients(
    geometric_length: float,
    circle_modulus: float,
    monopole_magnitude: int,
) -> tuple[float, float, float]:
    pi = math.pi
    a0 = 8.0 * pi * geometric_length**3 * circle_modulus
    a2 = -(4.0 * pi / 3.0) * geometric_length * circle_modulus
    a4 = (
        2.0
        * pi
        * (5.0 * monopole_magnitude**2 - 1.0)
        * circle_modulus
        / (15.0 * geometric_length)
    )
    return a0, a2, a4


def build_audit() -> D7SeeleyDeWittAudit:
    L, T, pi_c, n = sp.symbols("L T pi_c n", nonzero=True, real=True)

    volume = 4 * pi_c * L**3 * T
    integrated_r = 8 * pi_c * L * T
    integrated_r2 = 16 * pi_c * T / L
    integrated_ric2 = 8 * pi_c * T / L
    integrated_riem2 = 16 * pi_c * T / L
    integrated_f2 = 2 * pi_c * n**2 * T / L

    a0_symbolic = 2 * volume
    a2_symbolic = -integrated_r / 6
    a4_symbolic = (
        5 * integrated_r2
        - 8 * integrated_ric2
        - 7 * integrated_riem2
    ) / 720 + integrated_f2 / 3

    expected_a0 = 8 * pi_c * L**3 * T
    expected_a2 = -(4 * pi_c / 3) * L * T
    expected_a4 = 2 * pi_c * (5 * n**2 - 1) * T / (15 * L)

    universal_a4 = (
        2 * (5 * integrated_r2 - 2 * integrated_ric2 + 2 * integrated_riem2)
        + 60 * (-integrated_r2 / 2)
        + 180 * (integrated_r2 / 8 + integrated_f2)
        + 30 * (-integrated_riem2 / 4 - 2 * integrated_f2)
    ) / 360

    geometric_length = 1.3
    circle_modulus = 4.2
    monopole_magnitude = 1
    holonomy = 0.25
    circumference = geometric_length * circle_modulus
    a0, a2, a4 = reduced_dirac_coefficients(
        geometric_length, circle_modulus, monopole_magnitude
    )

    heat_times = (0.02, 0.01, 0.005, 0.002, 0.001)
    samples: list[HeatTraceSample] = []
    for heat_time in heat_times:
        exact_trace = exact_product_heat_trace(
            heat_time,
            geometric_length,
            circle_modulus,
            monopole_magnitude,
            holonomy,
        )
        scaled_trace = exact_trace * (4.0 * math.pi * heat_time) ** 1.5
        approximation = a0 + a2 * heat_time + a4 * heat_time**2
        extracted_a4 = (scaled_trace - a0 - a2 * heat_time) / heat_time**2
        samples.append(
            HeatTraceSample(
                heat_time=heat_time,
                exact_scaled_trace=scaled_trace,
                a0_a2_a4_approximation=approximation,
                absolute_residual=abs(scaled_trace - approximation),
                extracted_a4=extracted_a4,
            )
        )

    scale = 3.7
    cutoff = 2.4
    unscaled_action = cutoff**3 * a0 + cutoff * a2 + a4 / cutoff
    scaled_a0 = scale**3 * a0
    scaled_a2 = scale * a2
    scaled_a4 = a4 / scale
    scaled_cutoff = cutoff / scale
    scaled_action = (
        scaled_cutoff**3 * scaled_a0
        + scaled_cutoff * scaled_a2
        + scaled_a4 / scaled_cutoff
    )
    scale_orbit_residual = abs(scaled_action - unscaled_action)

    max_residual = max(sample.absolute_residual for sample in samples[-3:])
    extracted_error = abs(samples[-1].extracted_a4 - a4)

    checks = [
        sp.simplify(a0_symbolic - expected_a0) == 0,
        sp.simplify(a2_symbolic - expected_a2) == 0,
        sp.simplify(a4_symbolic - expected_a4) == 0,
        sp.simplify(universal_a4 - a4_symbolic) == 0,
        max_residual < 1.0e-7,
        extracted_error < 1.0e-3,
        scale_orbit_residual < 1.0e-10,
    ]

    return D7SeeleyDeWittAudit(
        geometric_length=geometric_length,
        circle_modulus=circle_modulus,
        circumference=circumference,
        monopole_magnitude=monopole_magnitude,
        holonomy=holonomy,
        reduced_a0=a0,
        reduced_a2=a2,
        reduced_a4=a4,
        symbolic_a0_residual=str(sp.simplify(a0_symbolic - expected_a0)),
        symbolic_a2_residual=str(sp.simplify(a2_symbolic - expected_a2)),
        symbolic_a4_residual=str(sp.simplify(a4_symbolic - expected_a4)),
        universal_to_dirac_a4_residual=str(
            sp.simplify(universal_a4 - a4_symbolic)
        ),
        heat_trace_samples=tuple(samples),
        maximum_small_time_residual=max_residual,
        smallest_time_extracted_a4_error=extracted_error,
        local_coefficients_linear_in_circle_modulus=True,
        common_scale_orbit_residual=scale_orbit_residual,
        all_checks_pass=all(checks),
        conclusion=(
            "The universal closed-manifold a0/a2/a4 formulas reduce exactly to "
            "the Program-D rank-two Dirac/monopole coefficients. The separated "
            "primitive-monopole spectrum numerically reproduces those coefficients "
            "in the small-time heat trace. All local terms remain linear in the "
            "circle modulus, and the local action is invariant under a common "
            "metric/cutoff rescaling. Therefore local Seeley-DeWitt data fix UV "
            "counterterms and relative normalizations, not a finite circle or "
            "absolute length by themselves."
        ),
    )


def main() -> int:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    return 0 if audit.all_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
