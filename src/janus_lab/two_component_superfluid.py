"""Two-component Gross-Pitaevskii analogue model in dimensionless units."""

from __future__ import annotations

import numpy as np


def homogeneous_interaction_energy(
    density1: float, density2: float, g1: float, g2: float, g12: float
) -> float:
    if density1 < 0 or density2 < 0:
        raise ValueError("densities must be nonnegative")
    return 0.5 * g1 * density1**2 + 0.5 * g2 * density2**2 + g12 * density1 * density2


def interaction_eigenvalues(g1: float, g2: float, g12: float) -> np.ndarray:
    return np.linalg.eigvalsh(np.array([[g1, g12], [g12, g2]], dtype=float))


def miscible_stable(g1: float, g2: float, g12: float) -> bool:
    return bool(g1 > 0 and g2 > 0 and g12**2 < g1 * g2)


def bogoliubov_frequency_squared(
    wave_number: np.ndarray | float,
    density: float,
    mass: float,
    g: float,
    g12: float,
) -> tuple[np.ndarray, np.ndarray]:
    if density <= 0 or mass <= 0:
        raise ValueError("density and mass must be positive")
    k = np.asarray(wave_number, dtype=float)
    epsilon = k**2 / (2.0 * mass)
    common = epsilon * (epsilon + 2.0 * density * (g + g12))
    relative = epsilon * (epsilon + 2.0 * density * (g - g12))
    return common, relative


def sound_speeds_squared(density: float, mass: float, g: float, g12: float) -> tuple[float, float]:
    if density <= 0 or mass <= 0:
        raise ValueError("density and mass must be positive")
    return density * (g + g12) / mass, density * (g - g12) / mass


def healing_lengths(density: float, mass: float, g: float, g12: float) -> tuple[float, float]:
    common_c2, relative_c2 = sound_speeds_squared(density, mass, g, g12)
    if common_c2 <= 0 or relative_c2 <= 0:
        raise ValueError("stable healing lengths require both channels positive")
    return 1.0 / np.sqrt(2.0 * mass**2 * common_c2), 1.0 / np.sqrt(
        2.0 * mass**2 * relative_c2
    )


def imaginary_time_ground_state(
    points: int = 256,
    length: float = 20.0,
    steps: int = 1000,
    dt: float = 2.0e-4,
    g: float = 1.0,
    g12: float = 0.5,
    seed: int = 0,
) -> dict[str, np.ndarray]:
    """Periodic split-step relaxation of a symmetric miscible condensate."""
    if points < 16 or length <= 0 or steps < 1 or dt <= 0 or not miscible_stable(g, g, g12):
        raise ValueError("invalid or unstable ground-state inputs")
    rng = np.random.default_rng(seed)
    dx = length / points
    k = 2.0 * np.pi * np.fft.fftfreq(points, d=dx)
    kinetic = np.exp(-dt * k**2 / 2.0)
    psi1 = 1.0 + 1.0e-2 * rng.normal(size=points)
    psi2 = 1.0 + 1.0e-2 * rng.normal(size=points)
    target_norm = float(points)
    for _ in range(steps):
        psi1 = np.fft.ifft(kinetic * np.fft.fft(psi1)).real
        psi2 = np.fft.ifft(kinetic * np.fft.fft(psi2)).real
        n1, n2 = psi1**2, psi2**2
        psi1 *= np.exp(-dt * (g * n1 + g12 * n2))
        psi2 *= np.exp(-dt * (g * n2 + g12 * n1))
        psi1 *= np.sqrt(target_norm / np.sum(psi1**2))
        psi2 *= np.sqrt(target_norm / np.sum(psi2**2))
    return {"x": np.arange(points) * dx, "psi1": psi1, "psi2": psi2}


def acoustic_step_scattering(impedance_left: float, impedance_right: float) -> dict[str, float]:
    if impedance_left <= 0 or impedance_right <= 0:
        raise ValueError("impedances must be positive")
    denominator = impedance_left + impedance_right
    reflection_amplitude = (impedance_right - impedance_left) / denominator
    transmission_amplitude = 2.0 * impedance_right / denominator
    reflection_flux = reflection_amplitude**2
    transmission_flux = 4.0 * impedance_left * impedance_right / denominator**2
    return {
        "reflection_amplitude": reflection_amplitude,
        "transmission_amplitude": transmission_amplitude,
        "reflection_flux": reflection_flux,
        "transmission_flux": transmission_flux,
    }


def mode_conversion_probability(mixing_angle: float, phase_difference: float) -> float:
    return float(np.sin(2.0 * mixing_angle) ** 2 * np.sin(phase_difference / 2.0) ** 2)
