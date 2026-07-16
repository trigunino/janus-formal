"""Fock-space stability test for positive-energy, PT-signed sectors.

This is an exploratory finite truncation, not a covariant Janus QFT.
"""

from __future__ import annotations

import numpy as np


def ladder(cutoff: int) -> np.ndarray:
    if cutoff < 2:
        raise ValueError("cutoff must be at least 2")
    result = np.zeros((cutoff, cutoff), dtype=complex)
    for n in range(1, cutoff):
        result[n - 1, n] = np.sqrt(n)
    return result


def operators(cutoff: int, omega: float = 1.0) -> dict[str, np.ndarray]:
    if omega <= 0:
        raise ValueError("omega must be positive")
    a = ladder(cutoff)
    identity = np.eye(cutoff, dtype=complex)
    number = a.conj().T @ a
    x = (a + a.conj().T) / np.sqrt(2.0 * omega)
    return {
        "n_plus": np.kron(number, identity),
        "n_minus": np.kron(identity, number),
        "x_plus": np.kron(x, identity),
        "x_minus": np.kron(identity, x),
        "identity": np.kron(identity, identity),
    }


def positive_hamiltonian(
    cutoff: int, omega: float = 1.0, coupling: float = 0.2
) -> np.ndarray:
    """Two positive oscillators with a PT-even bilinear interaction.

    The continuum quadratic form is positive for ``abs(coupling) < omega**2``.
    """
    if abs(coupling) >= omega**2:
        raise ValueError("unstable continuum quadratic form")
    op = operators(cutoff, omega)
    free = omega * (op["n_plus"] + op["n_minus"] + op["identity"])
    return free + coupling * (op["x_plus"] @ op["x_minus"])


def normal_mode_frequencies(omega: float = 1.0, coupling: float = 0.2) -> tuple[float, float]:
    """Exact symmetric/antisymmetric frequencies of the continuum model."""
    if omega <= 0 or abs(coupling) >= omega**2:
        raise ValueError("unstable continuum quadratic form")
    return (float(np.sqrt(omega**2 + coupling)), float(np.sqrt(omega**2 - coupling)))


def exact_ground_energy(omega: float = 1.0, coupling: float = 0.2) -> float:
    return 0.5 * sum(normal_mode_frequencies(omega, coupling))


def pt_odd_source_operator(cutoff: int, omega: float = 1.0) -> np.ndarray:
    """Signed gravitational coordinate Q = x_plus - x_minus."""
    op = operators(cutoff, omega)
    return op["x_plus"] - op["x_minus"]


def sourced_positive_hamiltonian(
    cutoff: int,
    omega: float = 1.0,
    coupling: float = 0.2,
    field: float = 0.0,
) -> np.ndarray:
    """Stable model in an external PT-odd field, H(field) = H0 - field*Q."""
    return positive_hamiltonian(cutoff, omega, coupling) - field * pt_odd_source_operator(
        cutoff, omega
    )


def ground_state(hamiltonian: np.ndarray) -> tuple[float, np.ndarray]:
    values, vectors = np.linalg.eigh(hamiltonian)
    return float(values[0]), vectors[:, 0]


def exact_signed_susceptibility(omega: float = 1.0, coupling: float = 0.2) -> float:
    """d<Q>/d(field) for the PT-odd normal mode."""
    normal_mode_frequencies(omega, coupling)
    return 2.0 / (omega**2 - coupling)


def ghost_hamiltonian(cutoff: int, omega: float = 1.0) -> np.ndarray:
    """Opposite energy signs, retained only as the instability control."""
    op = operators(cutoff, omega)
    return omega * (op["n_plus"] - op["n_minus"])


def signed_charge(cutoff: int, omega: float = 1.0) -> np.ndarray:
    """PT-odd sector charge; it does not change either kinetic sign."""
    op = operators(cutoff, omega)
    return op["n_plus"] - op["n_minus"]


def swap_operator(cutoff: int) -> np.ndarray:
    swap = np.zeros((cutoff**2, cutoff**2), dtype=complex)
    for i in range(cutoff):
        for j in range(cutoff):
            swap[j * cutoff + i, i * cutoff + j] = 1.0
    return swap


def ground_energy(hamiltonian: np.ndarray) -> float:
    return ground_state(hamiltonian)[0]


def stability_scan(cutoffs: tuple[int, ...] = (4, 6, 8, 10)) -> dict[str, list[float]]:
    return {
        "positive": [ground_energy(positive_hamiltonian(n)) for n in cutoffs],
        "ghost": [ground_energy(ghost_hamiltonian(n)) for n in cutoffs],
    }


if __name__ == "__main__":
    print(stability_scan())
