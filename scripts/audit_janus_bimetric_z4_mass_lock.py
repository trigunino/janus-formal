from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class BimetricZ4MassAudit:
    standard_massless_weight: int
    standard_massive_weight: int
    standard_discriminant: int
    doubled_massive_weight: int
    doubled_discriminant: int
    doubled_stationary_radials: tuple[float, float]
    stable_bosonic_radial: float
    stable_dimensionless_exponent: float
    spectral_target_modulus: float
    compatible_mass_times_length: float
    compatible_mass_times_length_squared: float
    first_sphere_dirac_mass_times_length_squared: float
    first_sphere_mass_compatible: bool
    minimal_per_fold_periodic_weight: int
    minimal_per_fold_quarter_weight: int
    positive_fold_doubled_level: int
    negative_fold_doubled_level: int
    paired_level_sum: int
    diagnostic_mass_inverse_m_for_A_1e26m: float
    diagnostic_mass_eV_for_A_1e26m: float
    all_checks_pass: bool
    conclusion: str


def stationarity_discriminant(periodic_weight: int, quarter_weight: int) -> int:
    return quarter_weight**2 - 4 * periodic_weight * (
        periodic_weight + quarter_weight
    )


def stationary_radials(periodic_weight: float, quarter_weight: float) -> tuple[float, float]:
    discriminant = quarter_weight**2 - 4.0 * periodic_weight * (
        periodic_weight + quarter_weight
    )
    if discriminant < 0.0:
        raise ValueError("no real stationary radials")
    denominator = 2.0 * (periodic_weight + quarter_weight)
    root = math.sqrt(discriminant)
    return (
        (quarter_weight + root) / denominator,
        (quarter_weight - root) / denominator,
    )


def build_audit(target_alpha_m: float = 1.0e26) -> BimetricZ4MassAudit:
    if target_alpha_m <= 0.0:
        raise ValueError("target alpha length must be positive")

    massless_weight = 2
    massive_weight = 5
    standard_discriminant = stationarity_discriminant(
        massless_weight, massive_weight
    )

    doubled_massive_weight = 2 * massive_weight
    doubled_discriminant = stationarity_discriminant(
        massless_weight, doubled_massive_weight
    )
    roots = stationary_radials(massless_weight, doubled_massive_weight)
    roots = tuple(sorted(roots, reverse=True))

    # Bosonic-sign potential: r=1/2 is the local maximum and r=1/3 the minimum.
    stable_radial = 1.0 / 3.0
    stable_exponent = -math.log(stable_radial)

    spectral_modulus = math.sqrt(2.0) * math.pi
    compatible_mass_length = stable_exponent / spectral_modulus
    compatible_mass_length_squared = compatible_mass_length**2
    first_sphere_mass_squared = 2.0

    # Minimal anomaly arithmetic per fold.
    p_fold = 1
    q_fold = 5
    bare_level = -2
    positive_doubled_level = 2 * bare_level + q_fold
    negative_doubled_level = -2 * bare_level - q_fold

    inverse_m = compatible_mass_length / target_alpha_m
    hbar_c_eVm = 1.973269804e-7
    mass_eV = inverse_m * hbar_c_eVm

    checks = [
        standard_discriminant < 0,
        doubled_discriminant == 4,
        all(
            math.isclose(value, expected, rel_tol=1.0e-15)
            for value, expected in zip(roots, (0.5, 1.0 / 3.0))
        ),
        math.isclose(stable_exponent, math.log(3.0), rel_tol=1.0e-15),
        compatible_mass_length_squared < 0.5,
        not math.isclose(
            compatible_mass_length_squared,
            first_sphere_mass_squared,
            rel_tol=1.0e-12,
        ),
        q_fold == 5,
        positive_doubled_level == 1,
        negative_doubled_level == -1,
        positive_doubled_level + negative_doubled_level == 0,
        inverse_m > 0.0,
        mass_eV > 0.0,
    ]

    return BimetricZ4MassAudit(
        standard_massless_weight=massless_weight,
        standard_massive_weight=massive_weight,
        standard_discriminant=standard_discriminant,
        doubled_massive_weight=doubled_massive_weight,
        doubled_discriminant=doubled_discriminant,
        doubled_stationary_radials=roots,
        stable_bosonic_radial=stable_radial,
        stable_dimensionless_exponent=stable_exponent,
        spectral_target_modulus=spectral_modulus,
        compatible_mass_times_length=compatible_mass_length,
        compatible_mass_times_length_squared=compatible_mass_length_squared,
        first_sphere_dirac_mass_times_length_squared=first_sphere_mass_squared,
        first_sphere_mass_compatible=False,
        minimal_per_fold_periodic_weight=p_fold,
        minimal_per_fold_quarter_weight=q_fold,
        positive_fold_doubled_level=positive_doubled_level,
        negative_fold_doubled_level=negative_doubled_level,
        paired_level_sum=positive_doubled_level + negative_doubled_level,
        diagnostic_mass_inverse_m_for_A_1e26m=inverse_m,
        diagnostic_mass_eV_for_A_1e26m=mass_eV,
        all_checks_pass=all(checks),
        conclusion=(
            "The standard 4D bimetric helicity count 2:5 is below the "
            "periodic/Z4 stabilization threshold. A shared massless tower plus "
            "two independent PT-related massive towers gives 2:10=1:5 and the "
            "stable root exp(-mLT)=1/3. Compatibility with the earlier spectral "
            "modulus requires mL=log(3)/(sqrt(2)*pi), far below the first "
            "primitive sphere Dirac excitation. The minimal per-fold 1:5 "
            "content also carries doubled Chern-Simons levels +1 and -1, which "
            "cancel globally under PT."
        ),
    )


def main() -> int:
    audit = build_audit()
    print(json.dumps(asdict(audit), indent=2, sort_keys=True))
    return 0 if audit.all_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
