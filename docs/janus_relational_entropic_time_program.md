# Janus relational entropic time — isolated research program

## Status

This is a separate exploratory program. It is not imported by a supported
Janus head and does not close the missing physical-clock law.

Scientific trigger:

- Giovanni Barontini, *Testing the problem of time with cold atoms*, Physical
  Review Research 8, L022047 (2026), arXiv:2509.07745.

The experiment shows that a coarse-grained entropy of an observed sector can
serve as an internal parameter that orders measured events and supports an
effective Schrödinger equation. It tests a relational clock construction; it
does not establish that fundamental time is literally created by ignorance.

## Why this matters for Janus

The current Janus clock audits already establish that two scale factors or a
bimetric determinant ratio do not by themselves select a physical clock. The
missing datum is a state-dependent law that supplies:

1. an ordering of events;
2. an orientation;
3. a rate relative to visible matter observables;
4. continuity through the PT/boundary regime.

An entropy clock is therefore relevant because it proposes exactly a
state-dependent law rather than another geometric ratio.

## Three notions that must not be conflated

### Coarse-grained exchange entropy

For a chosen observable algebra and coarse graining, define sector entropies
`S_plus` and `S_minus`. A classical closed-exchange model may satisfy

```text
dS_plus/dlambda + dS_minus/dlambda = 0.
```

An oriented local clock can then use `d tau/dlambda = epsilon dS_plus/dlambda`.
It advances only where this quantity is positive and stalls at exchange
equilibrium.

### Quantum reduced entropy

For a bipartite quantum state `rho_pm`, use

```text
S_plus  = -Tr rho_plus log rho_plus,
S_minus = -Tr rho_minus log rho_minus,
I(+:-)  = S_plus + S_minus - S_total.
```

For a globally pure state, `S_plus=S_minus`; these are entanglement entropies,
not opposite thermodynamic fluxes. The classical conservation equation above
must therefore not be imported into the quantum model without derivation.

### Modular or thermal time

A faithful state on an observable algebra can define a modular flow. This is
the conceptually strongest route because the state and algebra generate the
flow, rather than entropy merely relabeling an already known trajectory. A
finite-dimensional toy would start from a full-rank reduced density matrix and
test whether its modular flow agrees with the visible Janus dynamics.

## Minimal mathematical result

Lean entry:

```text
JanusFormal/Experimental/JanusRelationalEntropyClock.lean
```

Common-clock bridge:

```text
JanusFormal/Experimental/JanusCommonRelationalClockBridge.lean
```

Two-qubit modular candidate:

```text
JanusFormal/Experimental/JanusTwoQubitModularClock.lean
```

Modular/bimetric lapse audit:

```text
JanusFormal/Experimental/JanusModularBimetricLapseAudit.lean
```

Global entangled clock state:

```text
JanusFormal/Experimental/JanusGlobalEntangledClockState.lean
```

The module proves:

- strict monotonicity of sector entropy gives a valid event ordering;
- equal entropy at two ordered events obstructs a global entropy clock;
- closed two-sector exchange can have zero total entropy rate while one
  oriented sector supplies a local clock;
- the clock stalls when exchange stops.

It stores actual entropy histories and exchange-rate functions rather than a
structure containing only readiness propositions.

## Main obstruction

Entropy alone is generally not a global clock. Expansion/recollapse,
equilibration, fluctuations or recurrence can produce two distinct events with
the same entropy. Then `S` is not injective and cannot order the full history.

The Janus candidate must therefore be one of:

```text
local branch clock:       tau = epsilon S_plus,
cumulative activity:      tau = integral |J_S|,
clock with branch label:  tau = (branch, S_plus),
modular flow parameter:   tau = s_mod.
```

The cumulative option is monotone but risks being circular because its
integral is initially defined using an external parameter. The modular route
best addresses this criticism, but requires a real state and observable
algebra.

## Required derivation chain

```text
Janus action
  -> Hilbert/state space and plus/minus observable algebras
  -> reduced states or justified coarse graining
  -> entropy/information functional
  -> monotonicity or branch-labelled ordering theorem
  -> effective generator in internal time
  -> agreement with visible matter and photon clocks
  -> continuity through the PT boundary
```

## Falsification gates

The route fails if any of the following occurs:

- no canonical plus/minus algebra or coarse graining exists;
- the entropy candidate repeats without an independently derived branch label;
- the clock rate changes sign unpredictably;
- the effective internal-time evolution is not unitary/consistent where
  required;
- different observables infer incompatible internal times;
- the construction only reparametrizes a solution using laboratory time and
  provides no state-generated flow.

## Recommended next calculation

Do not modify the cosmological programs yet. Build a finite quantum Janus clock
with:

1. a bipartite Hilbert space `H_plus tensor H_minus`;
2. a constrained or globally stationary state;
3. explicit reduced density matrices;
4. mutual information and modular flow;
5. a comparison between modular time and conditional Page–Wootters evolution.

The decisive result would be either a derived common flow for both sectors or
a no-go showing that PT exchange and a faithful monotone clock are
incompatible.

## Source audit: the Janus common time marker

The historical 2001 two-fold presentation introduces one dimensionless
chronological marker `tau`, then explicitly allows different sector cosmic
times

```text
t_plus  = T_plus tau,
t_minus = T_minus tau.
```

The same text states that the marker is an arbitrary chronological choice with
no intrinsic physical meaning. It then proposes an elementary orbital clock
and relates its turn count to entropy per baryon. This is a genuine precursor
of the relational-entropic question, but not a derivation of a unique clock
from the bimetric action.

The 2024 EPJC construction uses a stronger FLRW ansatz. Equations (92a-b) use
one common chronological coordinate `x0` and write both temporal metric
coefficients as unity:

```text
ds_plus^2  = dx0^2 - a_plus(x0)^2 dSigma_plus^2,
ds_minus^2 = dx0^2 - a_minus(x0)^2 dSigma_minus^2.
```

This synchronizes both lapses. A common coordinate alone does not imply this:
the general shared-coordinate form is

```text
ds_plus^2  = N_plus(tau)^2 dtau^2 - a_plus(tau)^2 dSigma_plus^2,
ds_minus^2 = N_minus(tau)^2 dtau^2 - a_minus(tau)^2 dSigma_minus^2.
```

With only diagonal diffeomorphism invariance, one time reparametrization can
fix one lapse convention. Fixing both to unity additionally requires a
dynamical lapse-ratio equation or a synchronization law. Program B's
secondary-constraint/lapse-ratio work is therefore directly relevant.

The Lean bridge proves the kinematic core:

- one monotone common clock supports two distinct lapse rates;
- plus proper time can increase while PT-opposite minus proper time decreases;
- setting both lapses to one fixes their ratio and is extra data.

## Updated next calculation

The immediate target is no longer merely `tau=S`. It is a synchronization
equation:

```text
state/algebra -> common modular flow tau_J,
Hamiltonian constraints -> N_minus/N_plus,
tau_J + lapse ratio -> t_plus(tau_J), t_minus(tau_J).
```

The clean finite model should test whether one bipartite state can generate a
common modular parameter whose restrictions to the two sector algebras have
opposite PT orientation. If successful, the next bridge is to compare its
relative modular rate with the lapse ratio selected by the reduced bimetric
secondary constraint.

## Two-qubit modular result

The first finite quantum test uses the faithful reduced state

```text
rho_plus = diag(p,1-p),  0<p<1,
rho_minus = diag(1-p,p).
```

The second state is the normalized reciprocal/PT swap of the first. Their
modular Hamiltonians `K=-log(rho)` obey

```text
K_plus + K_minus = central scalar * identity.
```

Consequently central terms drop from commutators and Lean proves, for every
two-level observable `A`,

```text
[K_minus,A] = -[K_plus,A].
```

This is the desired finite mechanism: one modular parameter, opposite PT
sector flows. The modular gaps also satisfy

```text
Delta_minus = -Delta_plus,
|Delta_minus|/|Delta_plus| = 1
```

whenever the flow is nontrivial. Thus exact PT reciprocity naturally supplies
a unit relative modular rate, matching the `N_plus=N_minus=1` synchronization
used in the 2024 FLRW ansatz at this toy level.

There is also a sharp failure point: at `p=1/2` the reduced state is maximally
mixed, the modular gap vanishes and the internal clock stalls. Entanglement or
ignorance alone is therefore insufficient; the reduced state must be faithful
and nontracial.

This does not yet derive cosmological lapses. The next bridge must compare the
modular rate ratio with the lapse ratio obtained from Program B's secondary
constraint. Exact PT predicts ratio one; a non-unit dynamical lapse ratio would
require broken PT reciprocity, unequal sector states, or a state-dependent
clock calibration.

## Comparison with the current bimetric lapse constraint

The reduced Program P/B Hamiltonian has

```text
H = N_plus C_plus + N_minus C_minus.
```

Preservation of the secondary constraint is linear in the lapses. The only
current exact nondegenerate witness fixes

```text
N_minus = 2 N_plus.
```

Lean proves that this witness is incompatible with the reciprocal modular
ratio one for nonzero `N_plus`. This is not a physical Janus no-go: the witness
was deliberately constructed with unrestricted reduced parameters outside the
PT/exchange-flat family.

Conversely, the synchronized 2024 ansatz `N_plus=N_minus=1` is exactly
compatible with every faithful nontrivial reciprocal two-qubit modular state.
But Program P's PT-flat vacuum no-go shows that the symmetric vacuum point is
rank-degenerate; the reduced secondary chain does not currently derive the
unit ratio there.

The honest status is therefore:

```text
modular PT prediction:             N_minus/N_plus = 1,
2024 FLRW ansatz:                  N_minus/N_plus = 1,
non-PT reduced rank witness:       N_minus/N_plus = 2,
physical PT matter/curved branch:  not yet derived.
```

The next useful calculation is to extend the reduced secondary-constraint
analysis to a nonvacuum or curved PT-symmetric branch. Only that branch can
decide whether the modular clock predicts the bimetric synchronization rather
than merely agreeing with an ansatz.

## PT matter-supported branch result

Program P now supplies the previously missing nonvacuum gate
`P0EFTJanusMatterCurvatureFLRWConstraintBranch`. Its exact witness has:

```text
beta1=1, beta2=0,
M_plus^2=M_minus^2=1,
a_plus=a_minus=1,
p_plus=p_minus=1,
dust_plus=dust_minus=1/12,
k_plus=k_minus=0.
```

Both extended primary constraints vanish, the dynamical secondary constraint
vanishes with nonzero potential factor, and the three constraint covectors
have a nonzero Jacobian minor `145/144`. This removes the vacuum rank
degeneracy at the displayed point.

Secondary preservation gives exactly

```text
(145/12) (N_plus-N_minus)=0,
```

hence

```text
N_minus/N_plus=1
```

for nonzero lapse. The experimental bridge now proves in Lean that this
matter-supported PT witness is compatible with every faithful nontrivial
reciprocal two-qubit modular clock.

This is the first actual P-to-modular-clock match, not merely agreement with
the 2024 coordinate ansatz. Its scope remains finite-dimensional: the dust
terms are displayed reduced Hamiltonian inputs, not yet derived from a
covariant matter action, and no full ADM/BD theorem follows.

## Global-state derivation

The reciprocal reduced states are no longer independent inputs. Define the
single pure bipartite state

```text
|Psi_p> = sqrt(p) |0>_+ |1>_- + sqrt(1-p) |1>_+ |0>_-.
```

Lean proves for `0<=p<=1` that it is normalized and that its two partial traces
are exactly

```text
rho_plus  = diag(p,1-p),
rho_minus = diag(1-p,p).
```

For `0<p<1`, its Schmidt determinant is nonzero, so it is genuinely entangled.
Thus one global correlated state supplies both PT-reciprocal modular
Hamiltonians and their opposite flows. This removes the previous freedom of
choosing the two reduced clock states separately.

The remaining quantum gap is dynamical: the state has been constructed, but
not derived as a stationary/constrained state of a Janus Hamiltonian. A future
finite Hamiltonian must select this crossed Schmidt structure and determine
the weight `p`; otherwise the clock rate remains state-dependent.

## Sources for the common-clock audit

- J.-P. Petit, P. Midy and F. Landsheat, *Twin matter against dark matter*,
  Marseille Cosmology Conference (2001), sections 11, 14 and 16.
- J.-P. Petit, F. Margnat and H. Zejli, *A bimetric cosmological model based on
  Andrei Sakharov's twin universe approach*, European Physical Journal C 84,
  1226 (2024), equations (92a-b).
