"""Periodic weak-field Poisson helpers for the Janus two-sector limit."""

from __future__ import annotations

import numpy as np

from .signed_sector import Sector, newtonian_coupling_sign


def effective_density_grid(
    positive_density_abs: np.ndarray,
    negative_density_abs: np.ndarray,
    test_sector: Sector,
) -> np.ndarray:
    """Effective source density seen by one metric sector."""

    positive = np.asarray(positive_density_abs, dtype=float)
    negative = np.asarray(negative_density_abs, dtype=float)
    if positive.shape != negative.shape:
        raise ValueError("density grids must have the same shape.")
    if np.any(positive < 0.0) or np.any(negative < 0.0):
        raise ValueError("absolute density grids must be non-negative.")
    return (
        newtonian_coupling_sign(Sector.POSITIVE, test_sector) * positive
        + newtonian_coupling_sign(Sector.NEGATIVE, test_sector) * negative
    )


def _wave_numbers_2d(shape: tuple[int, int], box_size: float) -> tuple[np.ndarray, np.ndarray]:
    if len(shape) != 2:
        raise ValueError("density grid must be two-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny = shape
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    return np.meshgrid(kx, ky, indexing="ij")


def _wave_numbers_3d(
    shape: tuple[int, int, int],
    box_size: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    if len(shape) != 3:
        raise ValueError("density grid must be three-dimensional.")
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    nx, ny, nz = shape
    kx = 2.0 * np.pi * np.fft.fftfreq(nx, d=box_size / nx)
    ky = 2.0 * np.pi * np.fft.fftfreq(ny, d=box_size / ny)
    kz = 2.0 * np.pi * np.fft.fftfreq(nz, d=box_size / nz)
    return np.meshgrid(kx, ky, kz, indexing="ij")


def solve_periodic_poisson_2d(
    effective_density: np.ndarray,
    box_size: float,
    gravitational_constant: float = 1.0,
    subtract_mean: bool = True,
) -> np.ndarray:
    """Solve `Delta Phi = 4*pi*G*rho_eff` on a periodic 2D box."""

    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    density = np.asarray(effective_density, dtype=float)
    kx, ky = _wave_numbers_2d(density.shape, box_size)
    source = density - np.mean(density) if subtract_mean else density
    source_hat = np.fft.fftn(4.0 * np.pi * gravitational_constant * source)
    k2 = kx**2 + ky**2
    potential_hat = np.zeros_like(source_hat, dtype=complex)
    nonzero = k2 > 0.0
    potential_hat[nonzero] = -source_hat[nonzero] / k2[nonzero]
    return np.real(np.fft.ifftn(potential_hat))


def solve_periodic_poisson_3d(
    effective_density: np.ndarray,
    box_size: float,
    gravitational_constant: float = 1.0,
    subtract_mean: bool = True,
) -> np.ndarray:
    """Solve `Delta Phi = 4*pi*G*rho_eff` on a periodic 3D box."""

    if gravitational_constant < 0.0:
        raise ValueError("gravitational_constant must be non-negative.")
    density = np.asarray(effective_density, dtype=float)
    kx, ky, kz = _wave_numbers_3d(density.shape, box_size)
    source = density - np.mean(density) if subtract_mean else density
    source_hat = np.fft.fftn(4.0 * np.pi * gravitational_constant * source)
    k2 = kx**2 + ky**2 + kz**2
    potential_hat = np.zeros_like(source_hat, dtype=complex)
    nonzero = k2 > 0.0
    potential_hat[nonzero] = -source_hat[nonzero] / k2[nonzero]
    return np.real(np.fft.ifftn(potential_hat))


def acceleration_from_potential_2d(
    potential: np.ndarray,
    box_size: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Return acceleration components `-grad Phi` on a periodic 2D box."""

    phi = np.asarray(potential, dtype=float)
    kx, ky = _wave_numbers_2d(phi.shape, box_size)
    phi_hat = np.fft.fftn(phi)
    ax = np.real(np.fft.ifftn(-1j * kx * phi_hat))
    ay = np.real(np.fft.ifftn(-1j * ky * phi_hat))
    return ax, ay


def acceleration_from_potential_3d(
    potential: np.ndarray,
    box_size: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return acceleration components `-grad Phi` on a periodic 3D box."""

    phi = np.asarray(potential, dtype=float)
    kx, ky, kz = _wave_numbers_3d(phi.shape, box_size)
    phi_hat = np.fft.fftn(phi)
    ax = np.real(np.fft.ifftn(-1j * kx * phi_hat))
    ay = np.real(np.fft.ifftn(-1j * ky * phi_hat))
    az = np.real(np.fft.ifftn(-1j * kz * phi_hat))
    return ax, ay, az
