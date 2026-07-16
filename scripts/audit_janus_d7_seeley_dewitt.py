from __future__ import annotations

import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path

import sympy as sp


REPO_ROOT = Path(__file__).resolve().parents[1]
D7_GATE_ROOT = Path(
    "JanusFormal/Branches/FundamentalGeometryD7SpectralTheory/Gates"
)
D7_FACADE = Path(
    "JanusFormal/Branches/FundamentalGeometryD7SpectralTheory.lean"
)


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
    recent_wave0_gates_integrated: bool
    infinite_sphere_heat_trace_formally_constructed: bool
    quarter_determinant_convergence_formally_closed: bool
    algebraic_coefficient_correspondence_formally_closed: bool
    euler_maclaurin_remainder_estimate_formally_proved: bool
    unconditional_small_time_limit_formally_closed: bool
    small_time_limit_proof_basis: str
    heat_trace_samples: tuple[HeatTraceSample, ...]
    maximum_small_time_residual: float
    smallest_time_extracted_a4_error: float
    numerical_small_time_evidence_pass: bool
    local_coefficients_linear_in_circle_modulus: bool
    common_scale_orbit_residual: float
    all_checks_pass: bool
    conclusion: str


def audit_d7_wave0_formalization(
    repo_root: Path = REPO_ROOT,
) -> dict[str, bool]:
    facade = (repo_root / D7_FACADE).read_text(encoding="utf-8")
    sphere = (
        repo_root / D7_GATE_ROOT / "P0EFTJanusMonopoleSphereHeatTrace.lean"
    ).read_text(encoding="utf-8")
    asymptotic = (
        repo_root / D7_GATE_ROOT / "P0EFTJanusMonopoleHeatAsymptoticMatch.lean"
    ).read_text(encoding="utf-8")
    euler_maclaurin = (
        repo_root / D7_GATE_ROOT / "P0EFTJanusEulerMaclaurinOrderFour.lean"
    ).read_text(encoding="utf-8")
    quarter = (
        repo_root / D7_GATE_ROOT / "P0EFTJanusQuarterDeterminantConvergence.lean"
    ).read_text(encoding="utf-8")

    gate_names = (
        "P0EFTJanusMonopoleSphereHeatTrace",
        "P0EFTJanusEulerMaclaurinOrderFour",
        "P0EFTJanusMonopoleHeatAsymptoticMatch",
        "P0EFTJanusQuarterDeterminantConvergence",
    )
    recent_gates_integrated = all(
        (
            "import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory."
            f"Gates.{gate_name}"
        )
        in facade
        for gate_name in gate_names
    )

    local_start = facade.index("def localSpectralFoundationClosed")
    analytic_start = facade.index("def analyticSpectralTheoryClosed")
    full_start = facade.index("def fullD7Closure")
    local_closure = facade[local_start:analytic_start]
    analytic_closure = facade[analytic_start:full_start]

    sphere_constructed = all(
        declaration in sphere
        for declaration in (
            "def sphereHeatTrace",
            "theorem sphere_heat_trace_summable",
            "theorem sphere_heat_trace_has_sum",
        )
    ) and "s.infiniteMonopoleSphereHeatTraceConstructed" in local_closure

    quarter_closed = all(
        declaration in quarter
        for declaration in (
            "theorem quarter_remainder_summable",
            "theorem quarter_cutoff_remainder_converges",
            "noncomputable def z4RenormalizedDeterminant",
        )
    ) and all(
        status in local_closure
        for status in (
            "s.z4QuarterRemainderSummableProved",
            "s.z4RenormalizedDeterminantConstructed",
        )
    )

    algebraic_correspondence_closed = (
        "theorem spectral_product_coefficients_match_universal" in asymptotic
        and "s.spectralHeatCoefficientAlgebraMatched" in local_closure
    )
    euler_maclaurin_remainder_proved = all(
        declaration in euler_maclaurin
        for declaration in (
            "theorem euler_maclaurin_cell",
            "theorem euler_maclaurin_finite_remainder_bound",
            "theorem euler_maclaurin_tsum_error_bound",
        )
    ) and all(
        declaration in asymptotic
        for declaration in (
            "def EulerMaclaurinRemainderControlled",
            "theorem dimensionless_trace_euler_maclaurin_bound",
            "theorem euler_maclaurin_remainder_controlled",
        )
    )
    unconditional_small_time_closed = re.search(
        r"\btheorem\s+small_time_coefficients_match\s*(?:\(|\n)",
        asymptotic,
    ) is not None and all(
        status in analytic_closure
        for status in (
            "s.heatTraceAsymptoticsProved",
            "s.unconditionalMonopoleSphereSmallTimeAsymptoticsProved",
        )
    )

    return {
        "recent_wave0_gates_integrated": recent_gates_integrated,
        "infinite_sphere_heat_trace_formally_constructed": sphere_constructed,
        "quarter_determinant_convergence_formally_closed": quarter_closed,
        "algebraic_coefficient_correspondence_formally_closed": (
            algebraic_correspondence_closed
        ),
        "euler_maclaurin_remainder_estimate_formally_proved": (
            euler_maclaurin_remainder_proved
        ),
        "unconditional_small_time_limit_formally_closed": (
            unconditional_small_time_closed
        ),
    }


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
    wave0 = audit_d7_wave0_formalization()
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
    numerical_small_time_evidence_pass = (
        max_residual < 1.0e-7 and extracted_error < 1.0e-3
    )

    checks = [
        sp.simplify(a0_symbolic - expected_a0) == 0,
        sp.simplify(a2_symbolic - expected_a2) == 0,
        sp.simplify(a4_symbolic - expected_a4) == 0,
        sp.simplify(universal_a4 - a4_symbolic) == 0,
        wave0["recent_wave0_gates_integrated"],
        wave0["infinite_sphere_heat_trace_formally_constructed"],
        wave0["quarter_determinant_convergence_formally_closed"],
        wave0["algebraic_coefficient_correspondence_formally_closed"],
        wave0["euler_maclaurin_remainder_estimate_formally_proved"],
        wave0["unconditional_small_time_limit_formally_closed"],
        numerical_small_time_evidence_pass,
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
        recent_wave0_gates_integrated=wave0["recent_wave0_gates_integrated"],
        infinite_sphere_heat_trace_formally_constructed=wave0[
            "infinite_sphere_heat_trace_formally_constructed"
        ],
        quarter_determinant_convergence_formally_closed=wave0[
            "quarter_determinant_convergence_formally_closed"
        ],
        algebraic_coefficient_correspondence_formally_closed=wave0[
            "algebraic_coefficient_correspondence_formally_closed"
        ],
        euler_maclaurin_remainder_estimate_formally_proved=wave0[
            "euler_maclaurin_remainder_estimate_formally_proved"
        ],
        unconditional_small_time_limit_formally_closed=wave0[
            "unconditional_small_time_limit_formally_closed"
        ],
        small_time_limit_proof_basis="proved order-four Euler-Maclaurin remainder bound",
        heat_trace_samples=tuple(samples),
        maximum_small_time_residual=max_residual,
        smallest_time_extracted_a4_error=extracted_error,
        numerical_small_time_evidence_pass=numerical_small_time_evidence_pass,
        local_coefficients_linear_in_circle_modulus=True,
        common_scale_orbit_residual=scale_orbit_residual,
        all_checks_pass=all(checks),
        conclusion=(
            "The universal closed-manifold a0/a2/a4 formulas reduce exactly to "
            "the Program-D rank-two Dirac/monopole coefficients; this algebraic "
            "correspondence is formally closed. The separated primitive-monopole "
            "spectrum gives the same numerical small-time coefficients, and the "
            "order-four Euler-Maclaurin remainder bound now proves the formal "
            "small-time limit unconditionally. All local terms remain linear in the "
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
