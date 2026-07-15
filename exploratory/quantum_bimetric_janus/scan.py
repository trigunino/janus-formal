"""Small parameter scan for the two-sector toy model."""

from toy_two_sector import concurrence, chsh_bound, evolve, hamiltonian
import numpy as np


def measure(omega_minus: float, coupling: float, time: float = 1.0) -> tuple[float, float]:
    initial = np.array([1, 0, 0, 0], dtype=complex)
    state = evolve(initial, hamiltonian(omega_minus=omega_minus, coupling=coupling), time)
    return concurrence(state), chsh_bound(state)


if __name__ == "__main__":
    print("omega_minus coupling concurrence chsh_max")
    for omega_minus in (1.0, -1.0):
        for coupling in (0.0, 0.1, 0.2, 0.5):
            c, s = measure(omega_minus, coupling)
            print(f"{omega_minus:11.1f} {coupling:8.1f} {c:11.6f} {s:8.6f}")
