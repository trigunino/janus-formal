"""GR compact-object baselines in geometric units G=c=1."""

from __future__ import annotations

from collections.abc import Callable

import numpy as np


def constant_density_mass(radius: float, density: float) -> float:
    if radius <= 0 or density <= 0:
        raise ValueError("radius and density must be positive")
    return 4.0 * np.pi * density * radius**3 / 3.0


def compactness(mass: float, radius: float) -> float:
    if mass < 0 or radius <= 0:
        raise ValueError("mass must be nonnegative and radius positive")
    return 2.0 * mass / radius


def constant_density_pressure(
    r: np.ndarray | float, radius: float, density: float
) -> np.ndarray:
    mass = constant_density_mass(radius, density)
    c = compactness(mass, radius)
    if c >= 8.0 / 9.0:
        raise ValueError("finite-pressure solution requires 2M/R < 8/9")
    r_array = np.asarray(r, dtype=float)
    if np.any((r_array < 0) | (r_array > radius)):
        raise ValueError("r must lie in [0,R]")
    local = np.sqrt(1.0 - c * (r_array / radius) ** 2)
    surface = np.sqrt(1.0 - c)
    return density * (local - surface) / (3.0 * surface - local)


def central_pressure(radius: float, density: float) -> float:
    return float(constant_density_pressure(0.0, radius, density))


def tov_rhs(r: float, mass: float, pressure: float, density: float) -> tuple[float, float]:
    if r <= 0 or r <= 2.0 * mass:
        raise ValueError("TOV step requires r>2m and r>0")
    dm = 4.0 * np.pi * r**2 * density
    dp = -(density + pressure) * (mass + 4.0 * np.pi * r**3 * pressure)
    dp /= r * (r - 2.0 * mass)
    return dm, dp


def integrate_tov(
    central_pressure_value: float,
    density_of_pressure: Callable[[float], float],
    dr: float = 1.0e-3,
    max_radius: float = 100.0,
) -> dict[str, np.ndarray | float]:
    if central_pressure_value <= 0 or dr <= 0 or max_radius <= dr:
        raise ValueError("invalid TOV integration inputs")
    density0 = float(density_of_pressure(central_pressure_value))
    r = dr
    mass = 4.0 * np.pi * density0 * r**3 / 3.0
    pressure = central_pressure_value
    radii, masses, pressures = [r], [mass], [pressure]

    def rhs(radius: float, state: np.ndarray) -> np.ndarray:
        m, p = state
        rho = float(density_of_pressure(max(p, 0.0)))
        return np.asarray(tov_rhs(radius, m, p, rho))

    while pressure > 0 and r < max_radius:
        y = np.array([mass, pressure], dtype=float)
        k1 = rhs(r, y)
        k2 = rhs(r + dr / 2, y + dr * k1 / 2)
        k3 = rhs(r + dr / 2, y + dr * k2 / 2)
        k4 = rhs(r + dr, y + dr * k3)
        y_next = y + dr * (k1 + 2 * k2 + 2 * k3 + k4) / 6
        r += dr
        mass, pressure = float(y_next[0]), float(y_next[1])
        radii.append(r)
        masses.append(mass)
        pressures.append(max(pressure, 0.0))
    return {
        "radius": r,
        "mass": mass,
        "compactness": compactness(mass, r),
        "radii": np.asarray(radii),
        "masses": np.asarray(masses),
        "pressures": np.asarray(pressures),
    }


def stable_turning_point_mask(central_densities: np.ndarray, masses: np.ndarray) -> np.ndarray:
    rho = np.asarray(central_densities, dtype=float)
    mass = np.asarray(masses, dtype=float)
    if rho.ndim != 1 or rho.shape != mass.shape or rho.size < 3 or np.any(np.diff(rho) <= 0):
        raise ValueError("need matching arrays with strictly increasing density")
    return np.gradient(mass, rho) > 0


def surface_redshift(mass: float, radius: float) -> float:
    c = compactness(mass, radius)
    if c >= 1:
        raise ValueError("surface must lie outside the Schwarzschild radius")
    return 1.0 / np.sqrt(1.0 - c) - 1.0


def photon_sphere_radius(mass: float) -> float:
    return 3.0 * mass


def critical_impact_parameter(mass: float) -> float:
    return 3.0 * np.sqrt(3.0) * mass


def circular_orbit_angular_frequency(mass: float, radius: float) -> float:
    if mass <= 0 or radius <= 3.0 * mass:
        raise ValueError("timelike circular orbit requires r>3M")
    return np.sqrt(mass / radius**3)


def leading_deflection(mass: float, impact_parameter: float) -> float:
    if mass < 0 or impact_parameter <= 0:
        raise ValueError("invalid lensing inputs")
    return 4.0 * mass / impact_parameter


def leading_shapiro_delay(mass: float, r_emitter: float, r_receiver: float, impact: float) -> float:
    if min(r_emitter, r_receiver, impact) <= 0:
        raise ValueError("distances must be positive")
    argument = 4.0 * r_emitter * r_receiver / impact**2
    if argument <= 1:
        raise ValueError("leading logarithmic approximation requires argument>1")
    return 2.0 * mass * np.log(argument)


def trace_null_equatorial(
    mass: float,
    impact_parameter: float,
    surface_radius: float | None = None,
    r_start_factor: float = 1000.0,
    dphi: float = 2.0e-4,
    phi_max: float = 12.0,
) -> dict[str, np.ndarray | str | float]:
    """Trace `u=1/r` with `u''+u=3Mu^2` from a distant incoming ray."""
    if mass <= 0 or impact_parameter <= 0 or dphi <= 0:
        raise ValueError("mass, impact parameter and dphi must be positive")
    horizon = 2.0 * mass
    if surface_radius is not None and surface_radius <= horizon:
        raise ValueError("material surface must satisfy R>2M")
    r_start = max(r_start_factor * mass, 20.0 * impact_parameter)
    u = 1.0 / r_start
    radicand = 1.0 / impact_parameter**2 - u**2 + 2.0 * mass * u**3
    if radicand <= 0:
        raise ValueError("initial radius is not in the incoming domain")
    velocity = np.sqrt(radicand)
    phi = 0.0
    phis, radii = [phi], [r_start]
    status = "max_phi"
    closest = r_start

    def acceleration(value: float) -> float:
        return -value + 3.0 * mass * value**2

    while phi < phi_max:
        k1u, k1v = velocity, acceleration(u)
        k2u = velocity + dphi * k1v / 2.0
        k2v = acceleration(u + dphi * k1u / 2.0)
        k3u = velocity + dphi * k2v / 2.0
        k3v = acceleration(u + dphi * k2u / 2.0)
        k4u = velocity + dphi * k3v
        k4v = acceleration(u + dphi * k3u)
        u += dphi * (k1u + 2 * k2u + 2 * k3u + k4u) / 6.0
        velocity += dphi * (k1v + 2 * k2v + 2 * k3v + k4v) / 6.0
        phi += dphi
        if u <= 0:
            status = "escaped"
            break
        radius = 1.0 / u
        phis.append(phi)
        radii.append(radius)
        closest = min(closest, radius)
        if surface_radius is not None and radius <= surface_radius:
            status = "surface"
            break
        if radius <= horizon:
            status = "captured"
            break
        if velocity < 0 and radius >= 0.99 * r_start:
            status = "escaped"
            break
    return {
        "status": status,
        "phi": np.asarray(phis),
        "radius": np.asarray(radii),
        "closest_approach": closest,
        "impact_parameter": impact_parameter,
    }


def periastron_advance_per_orbit(total_mass: float, semi_major_axis: float, eccentricity: float) -> float:
    if total_mass <= 0 or semi_major_axis <= 0 or not 0 <= eccentricity < 1:
        raise ValueError("invalid bound-orbit inputs")
    return 6.0 * np.pi * total_mass / (semi_major_axis * (1.0 - eccentricity**2))


def binary_shapiro_delay(companion_mass: float, inclination: float, orbital_phase: float) -> float:
    if companion_mass < 0:
        raise ValueError("companion mass must be nonnegative")
    argument = 1.0 - np.sin(inclination) * np.sin(orbital_phase)
    if argument <= 0:
        raise ValueError("singular superior-conjunction geometry")
    return -2.0 * companion_mass * np.log(argument)


def eccentricity_enhancement(eccentricity: float) -> float:
    if not 0 <= eccentricity < 1:
        raise ValueError("eccentricity must lie in [0,1)")
    numerator = 1.0 + 73.0 * eccentricity**2 / 24.0 + 37.0 * eccentricity**4 / 96.0
    return numerator / (1.0 - eccentricity**2) ** 3.5


def orbital_period_derivative(mass1: float, mass2: float, period: float, eccentricity: float) -> float:
    if mass1 <= 0 or mass2 <= 0 or period <= 0:
        raise ValueError("masses and period must be positive")
    total = mass1 + mass2
    chirp = (mass1 * mass2) ** (3.0 / 5.0) / total ** (1.0 / 5.0)
    return (
        -192.0
        * np.pi
        / 5.0
        * (2.0 * np.pi * chirp / period) ** (5.0 / 3.0)
        * eccentricity_enhancement(eccentricity)
    )


def schwarzschild_isco_frequency(total_mass: float) -> float:
    if total_mass <= 0:
        raise ValueError("mass must be positive")
    return 1.0 / (2.0 * np.pi * 6.0 ** 1.5 * total_mass)
