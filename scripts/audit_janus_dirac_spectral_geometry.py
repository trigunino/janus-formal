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
    zero_mode_grid_maximizer: float
    truncated_full_determinant_grid_maximizer: float
    truncated_log_determinant_half_advantage: float
    circle_modulus_squared: float
    circle_radius_over_sphere_radius: float
    ll_charge_times_sphere_radius_squared: float
    alpha_over_sphere_radius: float
    alpha_over_sphere_radius_general_m2: float
    bimetric_selected_monopole_magnitude: int
    doubled_cs_levels: tuple[int, int]
    doubled_cs_total: int
    odd_dimensional_zeta_zero_scaling_factor: float
    rescaled_alpha_over_sphere_radius: float
    corrected_interpretation: str
    all_checks_pass: bool


def monopole_gap_squared_times_l2(monopole_magnitude: int, radial_level: int) -> int:
    if monopole_magnitude < 0 or radial_level < 0:
        raise ValueError("magnitudes and radial levels must be nonnegative")
    return radial_level * (radial_level + monopole_magnitude)


def level_degeneracy(monopole_magnitude: int, radial_level: int) -> int:
    return monopole_magnitude + 2 * radial_level


def zero_mode_eta(index: int, holonomy: float) -> float:
    return index * (1.0 - 2.0 * holonomy)


def determinant_amplitude(holonomy: float) -> float:
    return 2.0 * math.sin(math.pi * holonomy)


def mode_kernel(mass_angle: float, holonomy: float) -> float:
    return math.cosh(mass_angle) - math.cos(2.0 * math.pi * holonomy)


def truncated_log_determinant(
    monopole_magnitude: int,
    circle_modulus: float,
    holonomy: float,
    max_radial_level: int = 8,
) -> float:
    if not 0.0 < holonomy < 1.0:
        raise ValueError("holonomy must lie in the open fundamental domain")

    # Work with D^2. The k=0 factor is the monopole zero-mode tower; k>=1
    # includes the symmetric product branches. Holonomy-independent constants
    # are omitted because they do not affect vacuum selection.
    total = monopole_magnitude * math.log(mode_kernel(0.0, holonomy))
    for k in range(1, max_radial_level + 1):
        mass_angle = circle_modulus * math.sqrt(
            monopole_gap_squared_times_l2(monopole_magnitude, k)
        )
        total += level_degeneracy(monopole_magnitude, k) * math.log(
            mode_kernel(mass_angle, holonomy)
        )
    return total


def alpha_over_sphere_radius(monopole_magnitude: float) -> float:
    if monopole_magnitude < 0:
        raise ValueError("monopole magnitude must be nonnegative")
    return math.sqrt(2.0 / (monopole_magnitude + 1.0))


def determinant_scaling_factor(zeta_at_zero: float, scale: float) -> float:
    if scale <= 0.0:
        raise ValueError("scale must be positive")
    return math.exp(-2.0 * zeta_at_zero * math.log(scale))


def build_audit() -> DiracSpectralAudit:
    m = 1
    zero_modes = m
    first_gap_cleared = monopole_gap_squared_times_l2(m, 1)

    half = 0.5
    eta_half = zero_mode_eta(m, half)
    det_half = determinant_amplitude(half)

    grid = [i / 2000.0 for i in range(1, 2000)]
    zero_grid_maximizer = max(grid, key=determinant_amplitude)

    # Half-holonomy circle gap: pi^2/(L^2 T^2).
    # Primitive-monopole sphere gap: 2/L^2.
    # Equality gives T^2 = pi^2/2.
    modulus_squared = math.pi**2 / 2.0
    modulus = math.sqrt(modulus_squared)
    circle_ratio = modulus / (2.0 * math.pi)

    full_grid_maximizer = max(
        grid,
        key=lambda a: truncated_log_determinant(m, modulus, a),
    )
    half_advantage = truncated_log_determinant(m, modulus, 0.5) - max(
        truncated_log_determinant(m, modulus, 0.25),
        truncated_log_determinant(m, modulus, 0.75),
    )

    # q_LL = (1/8) * lambda_1^2, hence q_LL L^2 = 1/4.
    q_l2 = first_gap_cleared / 8.0

    alpha_ratio_primitive = alpha_over_sphere_radius(m)
    alpha_ratio_m2 = alpha_over_sphere_radius(2)

    # Solving sqrt(2/(m+1))=1 over nonnegative m gives m=1.
    m_symbol = sp.symbols("m", nonnegative=True)
    selected = sp.solve(sp.Eq(sp.sqrt(2 / (m_symbol + 1)), 1), m_symbol)
    selected_m = int(selected[0])

    levels = (1, -1)
    total_level = sum(levels)

    # Closed odd-dimensional massless determinant: zeta(0)=0, so uniform
    # rescaling does not change the determinant.
    scale_factor = determinant_scaling_factor(0.0, 10.0)

    original_l = 3.0
    original_a = alpha_ratio_primitive * original_l
    rescaling = 7.0
    rescaled_ratio = (rescaling * original_a) / (rescaling * original_l)

    checks = [
        zero_modes == 1,
        first_gap_cleared == 2,
        math.isclose(eta_half, 0.0, abs_tol=1.0e-15),
        math.isclose(det_half, 2.0, rel_tol=1.0e-15),
        math.isclose(zero_grid_maximizer, 0.5, abs_tol=5.1e-4),
        math.isclose(full_grid_maximizer, 0.5, abs_tol=5.1e-4),
        half_advantage > 0.0,
        math.isclose(circle_ratio, 1.0 / (2.0 * math.sqrt(2.0)), rel_tol=1.0e-15),
        math.isclose(q_l2, 0.25, rel_tol=1.0e-15),
        math.isclose(alpha_ratio_primitive, 1.0, rel_tol=1.0e-15),
        alpha_ratio_m2 < 1.0,
        selected_m == 1,
        total_level == 0,
        math.isclose(zero_mode_eta(m, 1.0 - 0.2), -zero_mode_eta(m, 0.2)),
        math.isclose(scale_factor, 1.0, rel_tol=1.0e-15),
        math.isclose(rescaled_ratio, alpha_ratio_primitive, rel_tol=1.0e-15),
    ]

    return DiracSpectralAudit(
        monopole_magnitude=m,
        zero_mode_multiplicity=zero_modes,
        first_nonzero_gap_squared_times_l2=first_gap_cleared,
        half_holonomy_eta=eta_half,
        half_holonomy_determinant_amplitude=det_half,
        zero_mode_grid_maximizer=zero_grid_maximizer,
        truncated_full_determinant_grid_maximizer=full_grid_maximizer,
        truncated_log_determinant_half_advantage=half_advantage,
        circle_modulus_squared=modulus_squared,
        circle_radius_over_sphere_radius=circle_ratio,
        ll_charge_times_sphere_radius_squared=q_l2,
        alpha_over_sphere_radius=alpha_ratio_primitive,
        alpha_over_sphere_radius_general_m2=alpha_ratio_m2,
        bimetric_selected_monopole_magnitude=selected_m,
        doubled_cs_levels=levels,
        doubled_cs_total=total_level,
        odd_dimensional_zeta_zero_scaling_factor=scale_factor,
        rescaled_alpha_over_sphere_radius=rescaled_ratio,
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
