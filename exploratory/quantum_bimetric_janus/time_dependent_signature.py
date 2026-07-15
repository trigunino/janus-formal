"""First distinctive test: a time-dependent minisuperspace ratio r(t)."""

import numpy as np

from hassan_rosen_minisuperspace import effective_coupling
from toy_two_sector import concurrence, hamiltonian


def r_of_t(t: float, epsilon: float = 0.5, hubble: float = 0.2) -> float:
    return 1.0 + epsilon * np.exp(-hubble * t)


def step(state: np.ndarray, coupling: float, dt: float) -> np.ndarray:
    h = hamiltonian(coupling=coupling)
    values, vectors = np.linalg.eigh(h)
    return vectors @ np.diag(np.exp(-1j * values * dt)) @ vectors.conj().T @ state


def trajectory(t_final: float = 5.0, steps: int = 500) -> list[tuple[float, float]]:
    state = np.array([1, 0, 0, 0], dtype=complex)
    dt = t_final / steps
    output = []
    for index in range(steps + 1):
        t = index * dt
        if index:
            coupling = effective_coupling(r_of_t(t - dt / 2.0))
            state = step(state, coupling, dt)
        output.append((t, concurrence(state)))
    return output


def constant_trajectory(coupling: float, t_final: float = 5.0, steps: int = 500) -> list[tuple[float, float]]:
    state = np.array([1, 0, 0, 0], dtype=complex)
    dt = t_final / steps
    output = []
    for index in range(steps + 1):
        if index:
            state = step(state, coupling, dt)
        output.append((index * dt, concurrence(state)))
    return output


if __name__ == "__main__":
    values = trajectory()
    constant = constant_trajectory(effective_coupling(r_of_t(0.0)))
    print({
        "initial_concurrence": values[0][1],
        "final_concurrence": values[-1][1],
        "max_concurrence": max(value for _, value in values),
        "constant_initial_coupling_final_concurrence": constant[-1][1],
        "norm_error": abs(np.vdot(step(np.array([1, 0, 0, 0], dtype=complex), 0.1, 1.0), step(np.array([1, 0, 0, 0], dtype=complex), 0.1, 1.0)).real - 1.0),
    })
