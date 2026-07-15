"""Check no-signalling for a local nonselective measurement."""

import numpy as np

from action_ansatz import induced_coupling_from_action
from toy_two_sector import evolve, hamiltonian


def reduced_minus(rho: np.ndarray) -> np.ndarray:
    return np.trace(rho.reshape(2, 2, 2, 2), axis1=0, axis2=2)


def measured_plus(rho: np.ndarray) -> np.ndarray:
    result = np.zeros_like(rho)
    for projector in (np.diag([1.0, 0.0]), np.diag([0.0, 1.0])):
        p = np.kron(projector, np.eye(2))
        result += p @ rho @ p
    return result


if __name__ == "__main__":
    initial = np.array([1, 0, 0, 0], dtype=complex)
    state = evolve(initial, hamiltonian(coupling=induced_coupling_from_action(1.5)), 1.0)
    rho = np.outer(state, state.conj())
    difference = np.linalg.norm(reduced_minus(rho) - reduced_minus(measured_plus(rho)))
    print({"reduced_state_difference": difference})
    assert difference < 1e-12
