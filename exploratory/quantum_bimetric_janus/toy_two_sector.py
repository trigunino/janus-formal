"""Minimal two-sector quantum toy model.

This is not yet a Janus gravity model: g_plus/g_minus only label the sectors.
The purpose is to test whether an inter-sector coupling can create entanglement.
"""

from __future__ import annotations

import numpy as np


I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.array([[1, 0], [0, -1]], dtype=complex)


def kron(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return np.kron(a, b)


def hamiltonian(omega_plus: float = 1.0, omega_minus: float = 1.0,
                coupling: float = 0.2) -> np.ndarray:
    """H = H+ + H- + lambda V+- with an XX inter-sector coupling."""
    return (
        0.5 * omega_plus * kron(Z, I)
        + 0.5 * omega_minus * kron(I, Z)
        + coupling * kron(X, X)
    )


def evolve(state: np.ndarray, h: np.ndarray, time: float) -> np.ndarray:
    values, vectors = np.linalg.eigh(h)
    unitary = vectors @ np.diag(np.exp(-1j * values * time)) @ vectors.conj().T
    return unitary @ state


def concurrence(state: np.ndarray) -> float:
    """Pure-state concurrence, clipped to [0, 1]."""
    matrix = state.reshape(2, 2)
    value = 2.0 * abs(np.linalg.det(matrix))
    return float(np.clip(value, 0.0, 1.0))


def chsh_bound(state: np.ndarray) -> float:
    """Maximum quantum CHSH value for a two-qubit pure state."""
    rho = np.outer(state, state.conj())
    correlations = np.array([
        [np.trace(rho @ kron(a, b)).real for b in (X, Y, Z)]
        for a in (X, Y, Z)
    ])
    eigenvalues = np.linalg.eigvalsh(correlations.T @ correlations)
    return float(2.0 * np.sqrt(eigenvalues[-1] + eigenvalues[-2]))


def run(time: float = 1.0, coupling: float = 0.2) -> dict[str, float]:
    initial = np.array([1, 0, 0, 0], dtype=complex)  # |0>+ |0>-
    state = evolve(initial, hamiltonian(coupling=coupling), time)
    return {
        "norm": float(np.vdot(state, state).real),
        "concurrence": concurrence(state),
        "chsh_max": chsh_bound(state),
    }


if __name__ == "__main__":
    print(run())
