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
    return float(np.linalg.eigvalsh(hamiltonian)[0])


def stability_scan(cutoffs: tuple[int, ...] = (4, 6, 8, 10)) -> dict[str, list[float]]:
    return {
        "positive": [ground_energy(positive_hamiltonian(n)) for n in cutoffs],
        "ghost": [ground_energy(ghost_hamiltonian(n)) for n in cutoffs],
    }


if __name__ == "__main__":
    print(stability_scan())
