import numpy as np
import pytest

from janus_lab.compact_objects import (
    central_pressure,
    circular_orbit_angular_frequency,
    compactness,
    constant_density_mass,
    constant_density_pressure,
    critical_impact_parameter,
    integrate_tov,
    leading_deflection,
    leading_shapiro_delay,
    photon_sphere_radius,
    trace_null_equatorial,
    periastron_advance_per_orbit,
    binary_shapiro_delay,
    orbital_period_derivative,
    schwarzschild_isco_frequency,
    stable_turning_point_mask,
    surface_redshift,
)


def test_constant_density_surface_and_buchdahl_divergence():
    radius = 1.0
    density = 0.05
    assert constant_density_pressure(radius, radius, density) == pytest.approx(0.0)
    critical_density = (8.0 / 9.0) * 3.0 / (8.0 * np.pi * radius**2)
    below = central_pressure(radius, critical_density * (1.0 - 1.0e-5))
    assert below > 1000.0 * critical_density
    with pytest.raises(ValueError):
        central_pressure(radius, critical_density)


def test_mass_and_compactness_are_consistent():
    mass = constant_density_mass(2.0, 0.01)
    assert compactness(mass, 2.0) == pytest.approx(2.0 * mass / 2.0)


def test_generic_tov_integrator_reaches_a_surface():
    result = integrate_tov(0.02, lambda p: 0.1 + p, dr=1.0e-3, max_radius=5.0)
    assert result["radius"] < 5.0
    assert result["pressures"][-1] == 0.0
    assert 0.0 < result["compactness"] < 1.0


def test_turning_point_stability_mask():
    rho = np.array([1.0, 2.0, 3.0, 4.0])
    masses = np.array([1.0, 2.0, 2.5, 2.4])
    mask = stable_turning_point_mask(rho, masses)
    assert mask[0]
    assert not mask[-1]


def test_schwarzschild_observables():
    mass = 2.0
    assert photon_sphere_radius(mass) == 6.0
    assert critical_impact_parameter(mass) == pytest.approx(6.0 * np.sqrt(3.0))
    assert surface_redshift(mass, 5.0) == pytest.approx(np.sqrt(5.0) - 1.0)
    assert circular_orbit_angular_frequency(mass, 20.0) == pytest.approx(np.sqrt(2 / 20**3))
    assert leading_deflection(mass, 100.0) == pytest.approx(0.08)
    assert leading_shapiro_delay(mass, 1000.0, 1000.0, 10.0) > 0.0


def test_null_ray_classifies_capture_escape_and_surface():
    mass = 1.0
    captured = trace_null_equatorial(mass, 4.0, dphi=1.0e-3)
    escaped = trace_null_equatorial(mass, 8.0, dphi=1.0e-3)
    surface = trace_null_equatorial(mass, 4.0, surface_radius=2.5, dphi=1.0e-3)
    assert captured["status"] == "captured"
    assert escaped["status"] == "escaped"
    assert escaped["closest_approach"] > 3.0
    assert surface["status"] == "surface"


def test_binary_gr_reference_signs_and_limits():
    assert periastron_advance_per_orbit(2.0, 100.0, 0.2) > 0.0
    assert binary_shapiro_delay(1.0, 0.0, 1.0) == pytest.approx(0.0)
    assert orbital_period_derivative(1.0, 1.0, 100.0, 0.0) < 0.0
    assert schwarzschild_isco_frequency(2.0) > 0.0


def test_eccentric_binary_decays_faster_than_circular_reference():
    circular = orbital_period_derivative(1.0, 1.0, 100.0, 0.0)
    eccentric = orbital_period_derivative(1.0, 1.0, 100.0, 0.6)
    assert abs(eccentric) > abs(circular)
