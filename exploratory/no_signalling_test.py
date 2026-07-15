"""Check the standard no-signalling condition for the toy state."""

import numpy as np

from action_ansatz import induced_coupling_from_action
from toy_two_sector import evolve, hamiltonian


def reduced_minus(rho: np.ndarray) -> np.ndarray:
    return np.trace(rho.reshape(2, 2, 2, 2), axis1=0, axis2=2)


def nonselective_plus_measurement(rho: np.ndarray) -> np.ndarray:
    p0 = np.diag([1.0, 0.0])
    p1 = np.diag([0.0, 1.0])
    result = np.zeros_like(rho)
    for p in (np.kron(p0, np.eye(2)), np.kron(p1, np.eye(2))):
        result += p @ rho @ p
    return result


if __name__ == "__main__":
    initial = np.array([1, 0, 0, 0], dtype=complex)
    coupling = induced_coupling_from_action(1.5)
    state = evolve(initial, hamiltonian(coupling=coupling), 1.0)
    rho = np.outer(state, state.conj())
    difference = np.linalg.norm(reduced_minus(rho) - reduced_minus(nonselective_plus_measurement(rho)))
    print({"reduced_state_difference": difference})
    assert difference < 1e-12
