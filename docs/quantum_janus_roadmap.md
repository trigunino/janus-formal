# Quantum Janus Roadmap

Status: planning document. The quantum layer must stay isolated from PM, Vlasov,
lensing and cosmology solvers until each bridge is explicitly derived and tested.

## Goal

Build a complete Janus-based quantum model in controlled stages:

1. keep the two-sector/bimetric structure explicit;
2. preserve positive kinetic mass in the effective Schrodinger layer;
3. put Janus signs in gravitational source/potential terms;
4. avoid direct `+/-` quantum mixing unless a source-derived rule is added;
5. compare predictions against standard quantum/Newtonian baselines.

## Current Baseline

Implemented:

- `src/janus_lab/quantum_sector.py`
- `tests/test_quantum_sector.py`

Current scope:

- nonrelativistic 1D effective model;
- positive and negative sector wavefunctions on one grid;
- block-diagonal bimetric Hamiltonian;
- Janus-signed external point-source potentials;
- normalization, probability, energy expectation;
- exact finite-dimensional unitary evolution for static Hamiltonians.
- Gaussian packet builder;
- position, momentum, variance and probability-current observables;
- harmonic-oscillator validation scaffold.
- explicit Dirichlet/periodic boundary-condition labels;
- free-packet drift validation.
- periodic 1D Schrodinger-Poisson prototype from quantum sector densities;
- conjugate self-consistent potentials `Phi_- = -Phi_+`;
- explicit frozen-potential nonlinear step preserving sector probabilities.
- Schrodinger-Poisson energy functional with interaction double-counting corrected;
- short-run diagnostics for probability, energy drift and sector-centroid separation.
- `scripts/diagnose_quantum_janus_1d.py` comparing free, Janus Schrodinger-Poisson and all-attractive controls.

Current guardrail:

- no Dirac/QFT solver;
- no calibrated self-gravity beyond the 1D periodic prototype;
- no stochastic collapse/decoherence model;
- no cross-sector quantum transition term;
- no coupling to particle-mesh, Vlasov, lensing, or cosmological modules.

Complex-reality boundary candidate workbench:

- `active_throat_S2`: direct geometric route, blocked by active
  `Omega_Sigma` pullback;
- `CP1_spinor_frame_orbit`: cleanest finite Hilbert-space candidate, blocked by
  Janus/PT derivation and `j -> alpha_m`;
- `aroundSigma_cross_compact_phase`: action-angle route, blocked by missing
  compact phase.

## Phase 1: Clean Effective Quantum Kernel

Purpose: make the current 1D effective model robust enough to serve as a testbed.

Tasks:

- add expectation values for position, momentum and variance;
- add probability current for each sector;
- add Gaussian wavepacket constructors;
- add free-particle and harmonic-oscillator validation cases;
- add convergence tests under grid refinement;
- add explicit boundary-condition labels.

Acceptance tests:

- free packet norm is conserved;
- static Hamiltonian energy is conserved;
- same-sector attractive potential lowers energy relative to free case;
- cross-sector repulsive potential raises energy relative to free case;
- no probability leaks between sectors when mixing is disabled.

## Phase 2: Janus Schrodinger-Poisson

Purpose: replace fixed external sources with wavefunction-generated densities.

Core equations to prototype:

```text
rho_+(x) = m |psi_+(x)|^2
rho_-(x) = m |psi_-(x)|^2

Delta Phi_+ = 4 pi G (rho_+ - rho_-)
Delta Phi_- = 4 pi G (-rho_+ + rho_-)

i hbar d_t psi_+ = [-hbar^2/(2m) Delta + m Phi_+] psi_+
i hbar d_t psi_- = [-hbar^2/(2m) Delta + m Phi_-] psi_-
```

Tasks:

- implement 1D periodic Poisson helper for quantum densities;
- add self-consistent Hamiltonian builder;
- add split-step or Crank-Nicolson evolution;
- track total norm and energy drift;
- add same-sector focusing / cross-sector separation diagnostics.

Acceptance tests:

- balanced equal densities cancel both potentials;
- conjugate potentials satisfy `Phi_- = -Phi_+` under the current weak-field convention;
- total sector probabilities are conserved;
- short-run energy drift stays bounded;
- opposite-sector packets separate in expectation value.

## Phase 3: Model Comparison

Purpose: test whether the Janus quantum model produces distinguishable or better behavior.

Baselines:

- free Schrodinger evolution;
- attractive single-sector Newton-Schrodinger;
- all-attractive two-label control;
- fixed external Janus potential.

Metrics:

- norm conservation;
- energy drift;
- packet separation/focusing;
- interference fringe displacement;
- scattering phase shift;
- bound-state spectrum shift;
- runtime and grid convergence.

Outputs:

- deterministic scripts under `scripts/`;
- compact reports under `outputs/reports/`;
- tests for numerical invariants, not fitted conclusions.

## Phase 4: Cross-Sector Coupling Gate

Purpose: decide whether any direct quantum transition term is admissible.

Default rule:

```text
H = diag(H_+, H_-)
```

Allowed only if derived:

```text
H = [[H_+, K],
     [K*,  H_-]]
```

Required before adding `K`:

- source anchor or explicit local derivation;
- Hermiticity proof;
- probability conservation test;
- symmetry statement;
- physical interpretation of transition probability;
- clear separation from gravitational interaction.

Rejection rule:

- no fitted cross-sector mixing term;
- no arbitrary oscillation term just to improve output.

## Phase 5: Relativistic Quantum Route

Purpose: decide whether Janus needs a Dirac/Klein-Gordon layer.

Tasks:

- map positive/negative sectors to metric sheets;
- identify whether the relevant source claims concern negative mass, negative energy, antimatter, or conjugated states;
- build a symbolic sign ledger before code;
- decide if a curved-metric Dirac prototype is necessary;
- keep it separate from the nonrelativistic module.

Acceptance gates:

- no contradiction with current two-geodesic Janus convention;
- no negative kinetic-energy instability introduced by accident;
- clear distinction from standard antimatter;
- tests cover Hermiticity/unitarity.

## Phase 6: Observables

Candidate observables:

- scattering by positive vs negative sector source;
- bound-state energy shifts;
- phase shift through a Janus potential well/barrier;
- two-packet segregation time;
- interference pattern displacement;
- self-gravitating packet stability.

Rules:

- every observable gets a standard-control comparison;
- no claim of superiority without a metric and baseline;
- no cosmology/lensing conclusion from the 1D quantum sandbox.

## Work Order

Recommended next commits:

1. Add wavepacket builders and expectation values.
2. Add free/harmonic validation tests.
3. Add 1D Schrodinger-Poisson prototype.
4. Add comparison script against standard controls.
5. Add report generator for first quantum diagnostics.
6. Only then consider a relativistic/Dirac branch.

## Open Questions

- Are negative-sector quantum states independent species, conjugated states, or an effective sector label?
- Should `m_hat proportional a` from the variable-constants gauge affect quantum mass in cosmological settings?
- Is there any source-derived direct `+/-` transition operator?
- Which observable is the first realistic target: scattering, interference, bound states, or self-gravity?
