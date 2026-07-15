"""Generic two-mode GW propagation; no Janus fit or P-derived coupling."""

from __future__ import annotations

import numpy as np


def group_velocity(k: np.ndarray | float, mass: float) -> np.ndarray:
    k_array = np.asarray(k, dtype=float)
    if mass < 0:
        raise ValueError("mass must be nonnegative")
    return np.abs(k_array) / np.sqrt(k_array**2 + mass**2)


def flat_delay(distance: float, k: float, mass: float) -> float:
    if distance < 0 or k == 0:
        raise ValueError("distance must be nonnegative and k nonzero")
    velocity = float(group_velocity(k, mass))
    return distance * (1.0 / velocity - 1.0)


def mixing_matrix(theta: float) -> np.ndarray:
    c, s = np.cos(theta), np.sin(theta)
    return np.array([[c, s], [-s, c]])


def conversion_probability(theta: float, phase_difference: float) -> float:
    return float(np.sin(2.0 * theta) ** 2 * np.sin(phase_difference / 2.0) ** 2)


def propagate_modes(
    visible_hidden: np.ndarray, theta: float, phases: np.ndarray
) -> np.ndarray:
    state = np.asarray(visible_hidden, dtype=complex)
    phase_array = np.asarray(phases, dtype=float)
    if state.shape != (2,) or phase_array.shape != (2,):
        raise ValueError("state and phases must each have shape (2,)")
    rotation = mixing_matrix(theta).astype(complex)
    eigenmodes = rotation @ state
    propagated = np.exp(-1j * phase_array) * eigenmodes
    return rotation.T @ propagated


def flrw_massive_phase(
    redshift: np.ndarray, hubble: np.ndarray, observed_k: float, mass: float
) -> float:
    """Integrate the massive-minus-massless phase on a supplied FLRW history."""
    z = np.asarray(redshift, dtype=float)
    h = np.asarray(hubble, dtype=float)
    if z.ndim != 1 or z.shape != h.shape or z.size < 2:
        raise ValueError("redshift and hubble must be matching 1D grids")
    if np.any(np.diff(z) <= 0) or np.any(h <= 0) or observed_k <= 0 or mass < 0:
        raise ValueError("require increasing z, H>0, k>0 and mass>=0")
    physical_k = observed_k * (1.0 + z)
    delta_omega = np.sqrt(physical_k**2 + mass**2) - physical_k
    integrand = delta_omega / ((1.0 + z) * h)
    return float(np.trapezoid(integrand, z))
