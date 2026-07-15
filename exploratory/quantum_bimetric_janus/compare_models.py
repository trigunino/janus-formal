"""Compare the three first toy-model hypotheses."""

import numpy as np

from toy_two_sector import concurrence, chsh_bound, evolve, hamiltonian


def evaluate(omega_minus: float, coupling: float, time: float = 1.0) -> dict[str, float]:
    initial = np.array([1, 0, 0, 0], dtype=complex)
    state = evolve(initial, hamiltonian(omega_minus=omega_minus, coupling=coupling), time)
    return {
        "norm_error": abs(float(np.vdot(state, state).real) - 1.0),
        "concurrence": concurrence(state),
        "chsh_max": chsh_bound(state),
    }


if __name__ == "__main__":
    cases = {
        "decoupled": (1.0, 0.0),
        "coupled_positive": (1.0, 0.2),
        "coupled_negative_energy": (-1.0, 0.2),
    }
    for name, parameters in cases.items():
        print(name, evaluate(*parameters))
