"""Diagnostic weak-field metric/tetrad helpers."""

from __future__ import annotations

import numpy as np


def periodic_derivative_1d(values: np.ndarray, box_size: float) -> np.ndarray:
    if box_size <= 0.0:
        raise ValueError("box_size must be positive.")
    data = np.asarray(values, dtype=float)
    if data.ndim != 1:
        raise ValueError("values must be one-dimensional.")
    k = 2.0 * np.pi * np.fft.fftfreq(data.size, d=box_size / data.size)
    return np.real(np.fft.ifft(1j * k * np.fft.fft(data)))


def weakfield_metric_1p1(phi: np.ndarray, psi: np.ndarray | None = None) -> np.ndarray:
    """Return diagonal 1+1 metric components `g00,g11` for a weak-field diagnostic."""

    phi_arr = np.asarray(phi, dtype=float)
    psi_arr = phi_arr if psi is None else np.asarray(psi, dtype=float)
    if phi_arr.shape != psi_arr.shape:
        raise ValueError("phi and psi must have the same shape.")
    g00 = -(1.0 + 2.0 * phi_arr)
    g11 = 1.0 - 2.0 * psi_arr
    if np.any(g00 >= 0.0) or np.any(g11 <= 0.0):
        raise ValueError("weak-field metric left Lorentzian diagonal branch.")
    return np.stack([g00, g11], axis=0)


def diagonal_tetrad_1p1(metric_components: np.ndarray) -> np.ndarray:
    """Return diagonal tetrad components reproducing `diag(g00,g11)`."""

    metric = np.asarray(metric_components, dtype=float)
    if metric.shape[0] != 2:
        raise ValueError("metric_components must have leading dimension 2.")
    g00, g11 = metric[0], metric[1]
    if np.any(g00 >= 0.0) or np.any(g11 <= 0.0):
        raise ValueError("metric components must be Lorentzian diagonal.")
    return np.stack([np.sqrt(-g00), np.sqrt(g11)], axis=0)


def metric_from_diagonal_tetrad_1p1(tetrad_components: np.ndarray) -> np.ndarray:
    tetrad = np.asarray(tetrad_components, dtype=float)
    if tetrad.shape[0] != 2:
        raise ValueError("tetrad_components must have leading dimension 2.")
    return np.stack([-(tetrad[0] ** 2), tetrad[1] ** 2], axis=0)


def diagonal_tetrad_map_1p1(
    target_tetrad_components: np.ndarray,
    source_tetrad_components: np.ndarray,
) -> np.ndarray:
    """Return diagnostic `L_geom=e_target^{-1} e_source` for diagonal 1+1 tetrads."""

    target = np.asarray(target_tetrad_components, dtype=float)
    source = np.asarray(source_tetrad_components, dtype=float)
    if target.shape != source.shape or target.shape[0] != 2:
        raise ValueError("target and source tetrads must share shape with leading dimension 2.")
    if np.any(target == 0.0):
        raise ValueError("target tetrad components must be non-zero.")
    ratio = source / target
    maps = np.zeros((ratio.shape[1], 2, 2), dtype=float)
    maps[:, 0, 0] = ratio[0]
    maps[:, 1, 1] = ratio[1]
    return maps


def max_lorentz_residual_1p1(maps: np.ndarray) -> float:
    """Return max residual of batched `L.T eta L - eta` for eta=diag(-1,+1)."""

    matrices = np.asarray(maps, dtype=float)
    if matrices.ndim == 2:
        matrices = matrices[None, :, :]
    if matrices.ndim != 3 or matrices.shape[1:] != (2, 2):
        raise ValueError("maps must have shape (2,2) or (n,2,2).")
    eta = np.asarray([[-1.0, 0.0], [0.0, 1.0]])
    residuals = np.transpose(matrices, (0, 2, 1)) @ eta @ matrices - eta
    return float(np.max(np.abs(residuals)))


def derivative_tetrad_map_1p1(maps: np.ndarray, box_size: float) -> np.ndarray:
    """Differentiate a batched 1+1 tetrad map component-wise on a periodic grid."""

    matrices = np.asarray(maps, dtype=float)
    if matrices.ndim != 3 or matrices.shape[1:] != (2, 2):
        raise ValueError("maps must have shape (n,2,2).")
    derivative = np.zeros_like(matrices)
    for row in range(2):
        for col in range(2):
            derivative[:, row, col] = periodic_derivative_1d(matrices[:, row, col], box_size)
    return derivative


def max_lie_algebra_residual_1p1(maps: np.ndarray, d_maps: np.ndarray) -> float:
    """Return max residual of `Omega=L^{-1}dL` satisfying `Omega.T eta + eta Omega=0`."""

    matrices = np.asarray(maps, dtype=float)
    derivatives = np.asarray(d_maps, dtype=float)
    if matrices.shape != derivatives.shape or matrices.ndim != 3 or matrices.shape[1:] != (2, 2):
        raise ValueError("maps and d_maps must share shape (n,2,2).")
    eta = np.asarray([[-1.0, 0.0], [0.0, 1.0]])
    omegas = np.linalg.inv(matrices) @ derivatives
    residuals = np.transpose(omegas, (0, 2, 1)) @ eta + eta @ omegas
    return float(np.max(np.abs(residuals)))


def gamma1_00_static_1d(phi: np.ndarray, psi: np.ndarray | None, box_size: float) -> np.ndarray:
    """Return `Gamma^1_00` for static diagonal 1+1 weak-field metric."""

    metric = weakfield_metric_1p1(phi, psi)
    dphi = periodic_derivative_1d(np.asarray(phi, dtype=float), box_size)
    return dphi / metric[1]


def slow_geodesic_acceleration_1d(phi: np.ndarray, psi: np.ndarray | None, box_size: float) -> np.ndarray:
    """Return slow-limit geodesic acceleration `-Gamma^1_00`."""

    return -gamma1_00_static_1d(phi, psi, box_size)


def weakfield_b4vol_1p1(phi: np.ndarray, psi: np.ndarray | None = None) -> np.ndarray:
    """Diagnostic 1+1 determinant factor, not the full Janus 4-volume law."""

    metric = weakfield_metric_1p1(phi, psi)
    return np.sqrt(-metric[0] * metric[1])


def dlog_weakfield_b4vol_1p1(phi: np.ndarray, psi: np.ndarray | None, box_size: float) -> np.ndarray:
    """Return diagnostic `D log B4vol` in the 1+1 weak-field branch."""

    return periodic_derivative_1d(np.log(weakfield_b4vol_1p1(phi, psi)), box_size)
