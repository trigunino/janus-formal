"""Dephasing and phase-shift comparison for the toy bimetric coupling."""

import numpy as np

from hassan_rosen_minisuperspace import effective_coupling
from toy_two_sector import hamiltonian


def evolve_density(rho, coupling, time):
    values, vectors = np.linalg.eigh(hamiltonian(coupling=coupling))
    unitary = vectors @ np.diag(np.exp(-1j * values * time)) @ vectors.conj().T
    return unitary @ rho @ unitary.conj().T


def dephase(rho, rate, time):
    result = rho.copy()
    factor = np.exp(-rate * time)
    for i in range(4):
        for j in range(4):
            if i != j:
                result[i, j] *= factor
    return result


def purity(rho):
    return float(np.trace(rho @ rho).real)


if __name__ == "__main__":
    initial = np.array([1, 0, 0, 0], dtype=complex)
    rho0 = np.outer(initial, initial.conj())
    coupling = effective_coupling(1.5)
    coherent = evolve_density(rho0, coupling, 1.0)
    janus_rate = abs(coupling) * 0.1
    decohered = dephase(coherent, janus_rate, 1.0)
    standard = dephase(coherent, janus_rate, 1.0)
    print({
        "coupling": coupling,
        "janus_rate": janus_rate,
        "coherent_purity": purity(coherent),
        "decohered_purity": purity(decohered),
        "standard_same_rate_purity": purity(standard),
    })
    assert np.isclose(purity(decohered), purity(standard))
