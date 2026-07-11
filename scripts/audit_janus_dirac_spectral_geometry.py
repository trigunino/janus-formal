from __future__ import annotations

import json
import math
from dataclasses import asdict, dataclass

import sympy as sp


@dataclass(frozen=True)
class DiracSpectralAudit:
    monopole_magnitude: int
    zero_mode_multiplicity: int
    first_nonzero_gap_squared_times_l2: int
    half_holonomy_eta: float
    half_holonomy_determinant_amplitude: float
    determinant_grid_maximizer: float
    circle_modulus_squared: float
    circle_radius_over_sphere_radius: float
    ll_charge_times_sphere_radius_squared: float
    alpha_over_sphere_radius: float
    alpha_over_sphere_radius_general_m2: float
    bimetric_selected_monopole_magnitude: int
    doubled_cs_levels: tuple[int, int]
    doubled_cs_total: int
    corrected_interpretation: str
    all_checks_pass: bool


def monopole_gap_squared_times_l2(monopole_magnitude: int, radial_level: int) -> int:
    if monopole_magnitude < 0 or radial_level < 0:
        raise ValueError("magnitudes and radial levels must be nonnegative")
    return radial_level * (radial_level + monopole_magnitude)


def zero_mode_eta(index: int, holonomy: float) -> float:
    return index * (1.0 - 2.0 * holonomy)


def determinant_amplitude(holonomy: float) -> float:
    return 2.0 * math.sin(math.pi * holonomy)


def alpha_over_sphere_radius(monopole_magnitude: float) -> float:
    if monopole_magnitude < 0:
        raise ValueError("monopole magnitude must be nonnegative")
    return math.sqrt(2.0 / (monopole_magnitude + 1.0))


def build_audit() -> DiracSpectralAudit:
    m = 1
    zero_modes = m
    first_gap_cleared = monopole_gap_squared_times_l2(m, 1)

    half = 0.5
    eta_half = zero_mode_eta(m, half)
    det_half = determinant_amplitude(half)

    grid = [i / 2000.0 for i in range(1, 2000)]
    grid_maximizer = max(grid, key=determinant_amplitude)

    # Half-holonomy circle gap: pi^2/(L^2 T^2).
    # Primitive-monopole sphere gap: 2/L^2.
    # Equality gives T^2 = pi^2/2.
    modulus_squared = math.pi**2 / 2.0
    circle_ratio = math.sqrt(modulus_squared) / (2.0 * math.pi)

    # q_LL = (1/8) * lambda_1^2, hence q_LL L^2 = 1/4.
    q_l2 = first_gap_cleared / 8.0

    alpha_ratio_primitive = alpha_over_sphere_radius(m)
    alpha_ratio_m2 = alpha_over_sphere_radius(2)

    # Solving sqrt(2/(m+1))=1 over nonnegative integer m gives m=1.
    m_symbol = sp.symbols("m", nonnegative=True)
    selected = sp.solve(sp.Eq(sp.sqrt(2 / (m_symbol + 1)), 1), m_symbol)
    selected_m = int(selected[0])

    levels = (1, -1)
    total_level = sum(levels)

    checks = [
        zero_modes == 1,
        first_gap_cleared == 2,
        math.isclose(eta_half, 0.0, abs_tol=1.0e-15),
        math.isclose(det_half, 2.0, rel_tol=1.0e-15),
        math.isclose(grid_maximizer, 0.5, abs_tol=5.1e-4),
        math.isclose(circle_ratio, 1.0 / (2.0 * math.sqrt(2.0)), rel_tol=1.0e-15),
        math.isclose(q_l2, 0.25, rel_tol=1.0e-15),
        math.isclose(alpha_ratio_primitive, 1.0, rel_tol=1.0e-15),
        alpha_ratio_m2 < 1.0,
        selected_m == 1,
        total_level == 0,
        math.isclose(zero_mode_eta(m, 1.0 - 0.2), -zero_mode_eta(m, 0.2)),
    ]

    return DiracSpectralAudit(
        monopole_magnitude=m,
        zero_mode_multiplicity=zero_modes,
        first_nonzero_gap_squared_times_l2=first_gap_cleared,
        half_holonomy_eta=eta_half,
        half_holonomy_determinant_amplitude=det_half,
        determinant_grid_maximizer=grid_maximizer,
        circle_modulus_squared=modulus_squared,
        circle_radius_over_sphere_radius=circle_ratio,
        ll_charge_times_sphere_radius_squared=q_l2,
        alpha_over_sphere_radius=alpha_ratio_primitive,
        alpha_over_sphere_radius_general_m2=alpha_ratio_m2,
        bimetric_selected_monopole_magnitude=selected_m,
        doubled_cs_levels=levels,
        doubled_cs_total=total_level,
        corrected_interpretation=(
            "The primitive monopole Dirac/LL lock gives alpha equal to the S2 "
            "throat radius. The factor 1/(2*sqrt(2)) belongs to the compact "
            "circle radius relative to the S2 radius, not to alpha itself."
        ),
        all_checks_pass=all(checks),
    )


def main() -> int:
    result = build_audit()
    print(json.dumps(asdict(result), indent=2, sort_keys=True))
    return 0 if result.all_checks_pass else 1


if __name__ == "__main__":
    raise SystemExit(main())
