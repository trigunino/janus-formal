"""Dephasing comparison."""
import numpy as np
from hassan_rosen_minisuperspace import effective_coupling
from toy_two_sector import hamiltonian

def evolve_density(rho, coupling, time):
    values, vectors = np.linalg.eigh(hamiltonian(coupling=coupling))
    u = vectors @ np.diag(np.exp(-1j*values*time)) @ vectors.conj().T
    return u @ rho @ u.conj().T

def dephase(rho, rate, time):
    result = rho.copy(); factor = np.exp(-rate*time)
    for i in range(4):
        for j in range(4):
            if i != j: result[i,j] *= factor
    return result

def purity(rho): return float(np.trace(rho@rho).real)

if __name__ == "__main__":
    state = np.array([1,0,0,0], dtype=complex)
    rho = np.outer(state, state.conj())
    coupling = effective_coupling(1.5)
    coherent = evolve_density(rho, coupling, 1.0)
    rate = abs(coupling)*0.1
    janus = dephase(coherent, rate, 1.0)
    standard = dephase(coherent, rate, 1.0)
    print({"coupling":coupling,"rate":rate,"coherent_purity":purity(coherent),"decohered_purity":purity(janus)})
    assert np.isclose(purity(janus), purity(standard))
