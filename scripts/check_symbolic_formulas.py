from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


@dataclass(frozen=True)
class SymbolicCheck:
    name: str
    ok: bool
    expression: str


def is_zero(expr: sp.Expr) -> bool:
    return bool(sp.simplify(sp.trigsimp(expr)) == 0)


def check_m18_deceleration() -> SymbolicCheck:
    u = sp.symbols("u", positive=True)
    a = sp.cosh(u) ** 2
    t = sp.sinh(2 * u) / 2 + u
    da_dt = sp.diff(a, u) / sp.diff(t, u)
    d2a_dt2 = sp.diff(da_dt, u) / sp.diff(t, u)
    q = -a * d2a_dt2 / da_dt**2
    expected = -1 / (2 * sp.sinh(u) ** 2)
    diff = sp.simplify(sp.trigsimp(q - expected))
    return SymbolicCheck("M18 q(u)", is_zero(diff), str(diff))


def check_variable_constant_gauge() -> list[SymbolicCheck]:
    a = sp.symbols("a", positive=True)
    c_hat = a ** sp.Rational(-1, 2)
    h_hat = a ** sp.Rational(3, 2)
    g_hat = a ** -1
    e_hat = a ** sp.Rational(1, 2)
    m_hat = a
    t_hat = a ** sp.Rational(3, 2)

    checks = {
        "X2026 energy conservation": sp.simplify(m_hat * c_hat**2 - 1),
        "X2026 Einstein constant scale": sp.simplify(g_hat / c_hat**2 - 1),
        "X2026 Compton length scale": sp.simplify(h_hat / (m_hat * c_hat) / a - 1),
        "X2026 fine-structure scale": sp.simplify(e_hat**2 / (h_hat * c_hat) - 1),
        "X2026 metric gauge scale": sp.simplify(c_hat * t_hat / a - 1),
    }
    return [SymbolicCheck(name, is_zero(expr), str(expr)) for name, expr in checks.items()]


def check_two_sector_newtonian_matrix() -> SymbolicCheck:
    density = sp.Matrix([1, -1])
    metric_equation = sp.Matrix([1, -1])
    coupling = metric_equation * density.T
    expected = sp.Matrix([[1, -1], [-1, 1]])
    diff = coupling - expected
    return SymbolicCheck("M15/M30 two-sector Newtonian sign matrix", diff == sp.zeros(2), str(diff))


def check_two_sector_poisson_rhs() -> SymbolicCheck:
    rho_plus, rho_minus_abs, gravitational_constant = sp.symbols(
        "rho_plus rho_minus_abs G", positive=True
    )
    density = sp.Matrix([rho_plus, rho_minus_abs])
    coupling = sp.Matrix([[1, -1], [-1, 1]])
    rhs = 4 * sp.pi * gravitational_constant * coupling * density
    expected = 4 * sp.pi * gravitational_constant * sp.Matrix(
        [rho_plus - rho_minus_abs, -rho_plus + rho_minus_abs]
    )
    diff = sp.simplify(rhs - expected)
    return SymbolicCheck("M15/M30 weak-field Poisson RHS", diff == sp.zeros(2, 1), str(diff))


def check_linearized_00_poisson_normalization() -> SymbolicCheck:
    laplacian_psi, chi, gravitational_constant, rho_eff = sp.symbols(
        "DeltaPsi chi G rho_eff", positive=True
    )
    linearized_g00 = 2 * laplacian_psi
    field_equation = sp.Eq(linearized_g00, chi * rho_eff)
    poisson_lhs = sp.solve(field_equation.subs(chi, 8 * sp.pi * gravitational_constant), laplacian_psi)[0]
    expected = 4 * sp.pi * gravitational_constant * rho_eff
    diff = sp.simplify(poisson_lhs - expected)
    return SymbolicCheck("Linearized 00 equation gives Poisson normalization", is_zero(diff), str(diff))


def check_zero_anisotropic_stress_lensing_potential() -> SymbolicCheck:
    phi, psi, pi_aniso = sp.symbols("Phi Psi Pi")
    slip_equation = sp.Eq(phi - psi, pi_aniso)
    no_stress_psi = sp.solve(slip_equation.subs(pi_aniso, 0), psi)[0]
    lensing_potential = sp.simplify((phi + no_stress_psi) / 2)
    diff = sp.simplify(lensing_potential - phi)
    return SymbolicCheck("Zero anisotropic stress makes lensing potential equal Phi", is_zero(diff), str(diff))


def check_comoving_perfect_fluid_t00_density_only() -> SymbolicCheck:
    rho, pressure, pi00 = sp.symbols("rho p Pi00")
    u0 = sp.Integer(1)
    eta00 = sp.Integer(-1)
    t00 = (rho + pressure) * u0**2 + pressure * eta00 + pi00
    diff = sp.simplify(t00.subs(pi00, 0) - rho)
    return SymbolicCheck("Comoving perfect-fluid T00 reduces to density", is_zero(diff), str(diff))


def check_boosted_perfect_fluid_t00() -> SymbolicCheck:
    rho, pressure, gamma, pi00 = sp.symbols("rho p gamma Pi00")
    eta00 = sp.Integer(-1)
    u0 = gamma
    t00 = (rho + pressure) * u0**2 + pressure * eta00 + pi00
    expected = (rho + pressure) * gamma**2 - pressure + pi00
    diff = sp.simplify(t00 - expected)
    return SymbolicCheck("Boosted perfect-fluid T00 includes gamma^2(rho+p)", is_zero(diff), str(diff))


def check_determinant_ratio_linearization() -> SymbolicCheck:
    epsilon, trace_plus, trace_minus = sp.symbols("epsilon h_plus h_minus")
    ratio = sp.sqrt((1 + epsilon * trace_minus) / (1 + epsilon * trace_plus))
    linear = 1 + epsilon * (trace_minus - trace_plus) / 2
    diff = sp.series(ratio - linear, epsilon, 0, 2).removeO()
    return SymbolicCheck("M15 determinant-ratio first-order expansion", is_zero(diff), str(diff))


def check_flrw_determinant_ratio_factor() -> SymbolicCheck:
    a_plus, a_minus = sp.symbols("a_plus a_minus", positive=True)
    determinant_plus = a_plus**8
    determinant_minus = a_minus**8
    ratio = sp.sqrt(determinant_minus / determinant_plus)
    expected = (a_minus / a_plus) ** 4
    diff = sp.simplify(ratio - expected)
    return SymbolicCheck("FLRW determinant-ratio factor", is_zero(diff), str(diff))


def check_coupled_determinant_ratio_reciprocity() -> SymbolicCheck:
    determinant_plus, determinant_minus = sp.symbols("g_plus g_minus", positive=True)
    b_plus = sp.sqrt(determinant_minus / determinant_plus)
    b_minus = sp.sqrt(determinant_plus / determinant_minus)
    diff = sp.simplify(b_plus * b_minus - 1)
    return SymbolicCheck("Coupled determinant-ratio reciprocity", is_zero(diff), str(diff))


def check_coupled_stationary_limit_sign_matrix() -> SymbolicCheck:
    rho_plus, rho_minus_abs = sp.symbols("rho_plus rho_minus_abs", positive=True)
    b_plus = sp.Integer(1)
    b_minus = sp.Integer(1)
    sources = sp.Matrix([rho_plus - b_plus * rho_minus_abs, rho_minus_abs - b_minus * rho_plus])
    expected = sp.Matrix([[1, -1], [-1, 1]]) * sp.Matrix([rho_plus, rho_minus_abs])
    diff = sp.simplify(sources - expected)
    return SymbolicCheck("Coupled stationary determinant limit sign matrix", diff == sp.zeros(2, 1), str(diff))


def check_determinant_weighted_positive_source() -> SymbolicCheck:
    rho_plus, rho_minus_abs, determinant_ratio = sp.symbols(
        "rho_plus rho_minus_abs B", positive=True
    )
    source = rho_plus - determinant_ratio * rho_minus_abs
    expected = rho_plus - determinant_ratio * rho_minus_abs
    diff = sp.simplify(source - expected)
    return SymbolicCheck("Determinant-weighted positive optical source", is_zero(diff), str(diff))


def check_null_einstein_contraction() -> SymbolicCheck:
    ricci_kk, ricci_scalar, metric_kk = sp.symbols("Rkk R gkk")
    einstein_kk = ricci_kk - sp.Rational(1, 2) * ricci_scalar * metric_kk
    diff = sp.simplify(einstein_kk.subs(metric_kk, 0) - ricci_kk)
    return SymbolicCheck("Null contraction G_kk equals R_kk", is_zero(diff), str(diff))


def check_positive_optical_source_signed_density_limit() -> SymbolicCheck:
    chi, rho_plus, rho_minus_abs, projection = sp.symbols(
        "chi rho_plus rho_minus_abs A", positive=True
    )
    source = chi * (rho_plus * projection - rho_minus_abs * projection)
    expected = chi * projection * (rho_plus - rho_minus_abs)
    diff = sp.simplify(source - expected)
    return SymbolicCheck("Positive optical source signed-density limit", is_zero(diff), str(diff))


def check_positive_effective_density_convention() -> SymbolicCheck:
    rho_plus, rho_minus_proper, determinant_ratio = sp.symbols(
        "rho_plus rho_minus_proper B", positive=True
    )
    rho_minus_effective = determinant_ratio * rho_minus_proper
    source_from_proper = rho_plus - determinant_ratio * rho_minus_proper
    source_from_effective = rho_plus - rho_minus_effective
    diff = sp.simplify(source_from_proper - source_from_effective)
    return SymbolicCheck("Positive effective negative-density convention", is_zero(diff), str(diff))


def check_effective_branch_absorbs_qdet() -> SymbolicCheck:
    rho_minus_proper, determinant_ratio, cross_projection_ratio = sp.symbols(
        "rho_minus_proper B Q_cross", positive=True
    )
    rho_minus_effective = determinant_ratio * rho_minus_proper
    proper_weighted = determinant_ratio * cross_projection_ratio * rho_minus_proper
    effective_weighted = cross_projection_ratio * rho_minus_effective
    diff = sp.simplify(proper_weighted - effective_weighted)
    return SymbolicCheck("Effective branch absorbs Q_det", is_zero(diff), str(diff))


def check_cross_projection_factor_isolation() -> SymbolicCheck:
    rho_plus, rho_minus_abs, determinant_ratio, projection_plus, projection_minus = sp.symbols(
        "rho_plus rho_minus_abs B A_plus A_minus", positive=True
    )
    cross_projection_ratio = projection_minus / projection_plus
    source = projection_plus * rho_plus - determinant_ratio * projection_minus * rho_minus_abs
    expected = projection_plus * (
        rho_plus - determinant_ratio * cross_projection_ratio * rho_minus_abs
    )
    diff = sp.simplify(source - expected)
    return SymbolicCheck("Cross-sector optical projection factor isolation", is_zero(diff), str(diff))


def check_equal_projection_cross_factor() -> SymbolicCheck:
    projection = sp.symbols("A", positive=True)
    cross_projection_ratio = projection / projection
    diff = sp.simplify(cross_projection_ratio - 1)
    return SymbolicCheck("Equal-projection cross factor", is_zero(diff), str(diff))


def check_raw_flrw_lapse_cross_factor() -> SymbolicCheck:
    a_plus, a_minus, k_eta = sp.symbols("a_plus a_minus k_eta", positive=True)
    projection_plus = (a_plus * k_eta) ** 2
    projection_minus = (a_minus * k_eta) ** 2
    cross_projection_ratio = projection_minus / projection_plus
    expected = (a_minus / a_plus) ** 2
    diff = sp.simplify(cross_projection_ratio - expected)
    return SymbolicCheck("Raw FLRW lapse cross factor", is_zero(diff), str(diff))


def check_raw_flrw_negative_lensing_weight_stack() -> SymbolicCheck:
    a_plus, a_minus = sp.symbols("a_plus a_minus", positive=True)
    determinant_ratio = (a_minus / a_plus) ** 4
    cross_projection_ratio = (a_minus / a_plus) ** 2
    weight = determinant_ratio * cross_projection_ratio
    expected = (a_minus / a_plus) ** 6
    diff = sp.simplify(weight - expected)
    return SymbolicCheck("Raw FLRW negative lensing weight stack", is_zero(diff), str(diff))


def check_relative_velocity_cross_factor() -> SymbolicCheck:
    beta = sp.symbols("beta", nonnegative=True)
    gamma_squared = 1 / (1 - beta**2)
    toward_factor = sp.simplify(gamma_squared * (1 - beta) ** 2)
    expected = (1 - beta) / (1 + beta)
    diff = sp.simplify(toward_factor - expected)
    return SymbolicCheck("Relative-velocity parallel cross factor", is_zero(diff), str(diff))


def check_standard_weak_lensing_prefactor_identity() -> SymbolicCheck:
    h0, omega, gravitational_constant, speed_of_light = sp.symbols("H0 Omega G c", positive=True)
    rho0 = 3 * h0**2 * omega / (8 * sp.pi * gravitational_constant)
    focusing = 4 * sp.pi * gravitational_constant * rho0 / speed_of_light**2
    expected = sp.Rational(3, 2) * omega * (h0 / speed_of_light) ** 2
    diff = sp.simplify(focusing - expected)
    return SymbolicCheck("Standard weak-lensing prefactor identity", is_zero(diff), str(diff))


def check_standard_dust_projection_factor() -> SymbolicCheck:
    z = sp.symbols("z", nonnegative=True)
    scale_factor = 1 / (1 + z)
    diff = sp.simplify((1 + z) - 1 / scale_factor)
    return SymbolicCheck("Standard dust lensing projection factor", is_zero(diff), str(diff))


def check_positive_flrw_null_geodesic_energy_scaling() -> SymbolicCheck:
    z = sp.symbols("z", nonnegative=True)
    scale_factor = 1 / (1 + z)
    k_eta = scale_factor**-2
    observed_energy = scale_factor * k_eta
    expected = 1 + z
    diff = sp.simplify(observed_energy - expected)
    return SymbolicCheck("Positive FLRW null-geodesic energy scaling", is_zero(diff), str(diff))


def check_positive_flrw_ricci_projection_scaling() -> SymbolicCheck:
    z = sp.symbols("z", nonnegative=True)
    energy_factor = 1 + z
    projection = energy_factor**2
    diff = sp.simplify(projection - (1 + z) ** 2)
    return SymbolicCheck("Positive FLRW Ricci projection scaling", is_zero(diff), str(diff))


def check_positive_flrw_jacobi_reduced_projection_factor() -> SymbolicCheck:
    a = sp.symbols("a", positive=True)
    physical_density = a**-3
    ricci_projection = a**-2
    affine_to_comoving_squared = a**4
    reduced = sp.simplify(physical_density * ricci_projection * affine_to_comoving_squared)
    diff = sp.simplify(reduced - a**-1)
    return SymbolicCheck("Positive FLRW Jacobi-reduced projection factor", is_zero(diff), str(diff))


def check_open_angular_kernel_to_comoving_kernel() -> SymbolicCheck:
    a_lens, a_source, d_lens, d_lens_source, d_source = sp.symbols(
        "a_l a_s D_l D_ls D_s", positive=True
    )
    angular_kernel = (a_lens * d_lens) * (a_source * d_lens_source) / (
        a_source * d_source
    )
    comoving_kernel = d_lens * d_lens_source / d_source
    diff = sp.simplify(angular_kernel - a_lens * comoving_kernel)
    return SymbolicCheck("Open angular kernel to comoving kernel", is_zero(diff), str(diff))


def run_checks() -> list[SymbolicCheck]:
    return [
        check_m18_deceleration(),
        *check_variable_constant_gauge(),
        check_two_sector_newtonian_matrix(),
        check_two_sector_poisson_rhs(),
        check_linearized_00_poisson_normalization(),
        check_zero_anisotropic_stress_lensing_potential(),
        check_comoving_perfect_fluid_t00_density_only(),
        check_boosted_perfect_fluid_t00(),
        check_determinant_ratio_linearization(),
        check_flrw_determinant_ratio_factor(),
        check_coupled_determinant_ratio_reciprocity(),
        check_coupled_stationary_limit_sign_matrix(),
        check_determinant_weighted_positive_source(),
        check_null_einstein_contraction(),
        check_positive_optical_source_signed_density_limit(),
        check_positive_effective_density_convention(),
        check_effective_branch_absorbs_qdet(),
        check_cross_projection_factor_isolation(),
        check_equal_projection_cross_factor(),
        check_raw_flrw_lapse_cross_factor(),
        check_raw_flrw_negative_lensing_weight_stack(),
        check_relative_velocity_cross_factor(),
        check_standard_weak_lensing_prefactor_identity(),
        check_standard_dust_projection_factor(),
        check_positive_flrw_null_geodesic_energy_scaling(),
        check_positive_flrw_ricci_projection_scaling(),
        check_positive_flrw_jacobi_reduced_projection_factor(),
        check_open_angular_kernel_to_comoving_kernel(),
    ]


def main() -> None:
    checks = run_checks()
    for check in checks:
        status = "OK" if check.ok else "FAIL"
        print(f"{status}: {check.name} -> {check.expression}")
    if not all(check.ok for check in checks):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
