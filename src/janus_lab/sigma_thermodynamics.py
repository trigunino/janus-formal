"""Conditional linear irreversible thermodynamics at Sigma."""

from __future__ import annotations

import numpy as np


def total_energy_residual(
    plus_rate: float, minus_rate: float, sigma_rate: float = 0.0, external_power: float = 0.0
) -> float:
    return plus_rate + minus_rate + sigma_rate - external_power


def onsager_casimir_residual(matrix: np.ndarray, parities: np.ndarray) -> np.ndarray:
    transport = np.asarray(matrix, dtype=float)
    epsilon = np.asarray(parities, dtype=float)
    if transport.ndim != 2 or transport.shape[0] != transport.shape[1]:
        raise ValueError("transport matrix must be square")
    if epsilon.shape != (transport.shape[0],) or np.any(np.abs(epsilon) != 1):
        raise ValueError("parities must be a matching vector of +/-1")
    return transport - epsilon[:, None] * epsilon[None, :] * transport.T


def entropy_production(matrix: np.ndarray, forces: np.ndarray) -> float:
    transport = np.asarray(matrix, dtype=float)
    force = np.asarray(forces, dtype=float)
    if transport.shape != (force.size, force.size):
        raise ValueError("matrix and force dimensions do not match")
    return float(force @ transport @ force)


def symmetric_transport_eigenvalues(matrix: np.ndarray) -> np.ndarray:
    transport = np.asarray(matrix, dtype=float)
    if transport.ndim != 2 or transport.shape[0] != transport.shape[1]:
        raise ValueError("transport matrix must be square")
    symmetric = (transport + transport.T) / 2.0
    return np.linalg.eigvalsh(symmetric)


def second_law_satisfied(matrix: np.ndarray, tolerance: float = 1.0e-12) -> bool:
    return bool(np.min(symmetric_transport_eigenvalues(matrix)) >= -tolerance)


def linear_flux(matrix: np.ndarray, forces: np.ndarray) -> np.ndarray:
    transport = np.asarray(matrix, dtype=float)
    force = np.asarray(forces, dtype=float)
    if transport.shape != (force.size, force.size):
        raise ValueError("matrix and force dimensions do not match")
    return transport @ force


def moving_interface_residual(
    plus_flux: float,
    minus_flux: float,
    speed: float,
    plus_density: float,
    minus_density: float,
    sigma_source: float = 0.0,
) -> float:
    return plus_flux - minus_flux - speed * (plus_density - minus_density) - sigma_source


def relax_linear(
    matrix: np.ndarray, initial_forces: np.ndarray, times: np.ndarray
) -> np.ndarray:
    """Exact spectral evolution `X(t)=exp(-L t)X(0)` for symmetric L."""
    transport = np.asarray(matrix, dtype=float)
    initial = np.asarray(initial_forces, dtype=float)
    time = np.asarray(times, dtype=float)
    if transport.shape != (initial.size, initial.size) or not np.allclose(transport, transport.T):
        raise ValueError("relaxation matrix must be symmetric and dimensionally compatible")
    if time.ndim != 1 or np.any(time < 0):
        raise ValueError("times must be a nonnegative 1D array")
    eigenvalues, eigenvectors = np.linalg.eigh(transport)
    coefficients = eigenvectors.T @ initial
    return np.asarray(
        [eigenvectors @ (np.exp(-eigenvalues * t) * coefficients) for t in time]
    )


def quadratic_lyapunov(forces: np.ndarray) -> float:
    force = np.asarray(forces, dtype=float)
    return float(force @ force / 2.0)


def von_neumann_entropy(density_matrix: np.ndarray, tolerance: float = 1.0e-12) -> float:
    rho = np.asarray(density_matrix, dtype=complex)
    if rho.ndim != 2 or rho.shape[0] != rho.shape[1] or not np.allclose(rho, rho.conj().T):
        raise ValueError("density matrix must be square Hermitian")
    eigenvalues = np.linalg.eigvalsh(rho)
    if np.min(eigenvalues) < -tolerance or not np.isclose(np.sum(eigenvalues), 1.0):
        raise ValueError("density matrix must be positive with unit trace")
    positive = eigenvalues[eigenvalues > tolerance]
    return float(-np.sum(positive * np.log(positive)))


def partial_trace_two_qubit(density_matrix: np.ndarray, trace_out: int) -> np.ndarray:
    rho = np.asarray(density_matrix, dtype=complex)
    if rho.shape != (4, 4) or trace_out not in (0, 1):
        raise ValueError("require a 4x4 two-qubit state and trace_out 0 or 1")
    tensor = rho.reshape(2, 2, 2, 2)
    if trace_out == 0:
        return np.trace(tensor, axis1=0, axis2=2)
    return np.trace(tensor, axis1=1, axis2=3)


def two_qubit_mutual_information(density_matrix: np.ndarray) -> float:
    plus = partial_trace_two_qubit(density_matrix, 1)
    minus = partial_trace_two_qubit(density_matrix, 0)
    return von_neumann_entropy(plus) + von_neumann_entropy(minus) - von_neumann_entropy(density_matrix)
