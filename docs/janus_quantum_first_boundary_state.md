# Janus Quantum-First Boundary State Branch

## Target

Test the reversed construction:

`Quantum boundary state -> CP1/TQFT phase space -> prequantization -> alpha spectrum -> classical Janus limit`.

This is not a paper-native Janus recreation. It is a possible extension route for
turning `alpha_m` from a continuous state label into a derived quantum sector.

## Current Result

The branch can build a conditional quantum spectrum:

- `CP1 ~= SU(2)/U(1)` gives a compact KKS orbit;
- `Integral_CP1 Omega_j = 4*pi*j`;
- prequantization gives `2*j/hbar in Z`;
- therefore labels can be discrete if the boundary state is accepted.

The branch does not yet predict `alpha_m`.

## Hard Blocker

The missing object is not another topological label. It is the energy map:

`quantum label -> boundary mass/charge -> alpha_m`.

Without a boundary Hamiltonian or mass operator derived from the quantum state,
the branch only gives:

`alpha_j = -2*pi*G*M_j/c^2 if M_j is supplied`.

## Classical Limit

If `alpha` is supplied by a quantum boundary mass law, the paper-native classical
background can be recovered conditionally:

- `a(u) = alpha*cosh(u)^2`;
- `q0 = -1/(2*sinh(u0)^2)`;
- large quantum number limit should approximate the continuous alpha sector.

## Deeper Mass-Operator Audit

The branch now audits the obvious mass routes:

- CP1 moment-map Hamiltonian: needs a selected time generator and energy unit.
- CP1 Casimir Hamiltonian: needs a dimensionful coefficient and physical map
  from `J^2` to boundary energy.
- CP1 area-gap-like route: needs an area-to-mass law for the throat.
- Closed TQFT/Chern-Simons route: gives sectors, but its Hamiltonian is
  topological/constraint-like unless a boundary time generator or nonzero
  charge map is derived.

So quantum-first reaches a stronger conclusion: it can discretize labels, but
prequantization alone cannot turn those labels into mass.

## Verdict

`final_branch_status = exhausted_conditional_spectrum_no_alpha_prediction`.

Next non-rustine targets:

- derive the boundary mass operator from the quantum boundary state/action;
- derive primitive sector selection;
- derive a dimensionful energy unit without importing `H0`, observations, or a fitted alpha.
