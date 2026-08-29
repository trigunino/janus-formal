# Program P scalar analytic architecture

## Status

This document describes the long-form scalar analytic development on
`dev-branch` after the global cut-bulk Green--Stokes theorem.

Validation on 2026-07-26 is green: the focused aggregate below builds
successfully (`9317` jobs), the Program P facade build is green (`9863` jobs),
and `scripts/audit_janus_program_p.py` passes with `0/14` terminal gates.

Compilation validates the import graph and every checked Lean declaration. It
does not turn the aggregate marker theorem into an inhabitance proof for the
conditional physical interfaces described below.

## Implemented architecture

### Geometric-to-Hilbert bridge

The branch now contains interfaces connecting the already constructed global
scalar Green boundary form to:

- the antisymmetric defect of a physical bulk operator pairing;
- the Hilbert symplectic form of value and normal traces;
- a concrete physical bulk `L²` space;
- the physical throat `L²` trace space;
- the physical graph-`H¹` completion.

### Closed operator realization

The closure of the algebraic graph is treated first as a closed relation in
`Ambient × Ambient`.  Under the explicit single-valuedness/closability
hypothesis, it is transported to a genuine closed operator domain with:

- ambient inclusion;
- operator map;
- completed paired trace;
- exact Green identity.

### Boundary conditions

Closed Lagrangian boundary conditions are represented abstractly in the paired
Hilbert trace space.  Implemented constructors include:

- Dirichlet;
- Neumann;
- nondegenerate separated conditions;
- constant real Robin conditions;
- graph conditions `normal = B value` for bounded symmetric `B`;
- direct sums of boundary conditions;
- symplectic transport by quarter-turns and symmetric shears.

Every such condition has a pulled-back closed graph domain, symmetry of the
restricted operator and equality with its boundary-adjoint domain.

### Resolvent and compact spectral theory

For every closed Lagrangian realization the branch defines:

- shifted operator;
- real resolvent set and real spectrum;
- algebraic and bounded resolvents;
- coercive construction of the bounded inverse;
- compact-resolvent package;
- Fredholm alternative;
- finite multiplicity of nonreference eigenspaces;
- spectral completeness of the compact ambient resolvent;
- resolvent identity and commutation;
- propagation of compactness between resolvent parameters;
- equivalence between operator and resolvent eigenspaces;
- semibounded spectral lower bounds.

### Variational theory

The branch defines the Jacobi pairing, mass pairing, quadratic functional,
constrained functional and Rayleigh quotient on the actual closed domain.

Implemented results include:

- exact affine Taylor formulas;
- first variation;
- weak stationarity iff the strong equation under dense inclusion;
- source equation and unique coercive minimizer;
- Gaussian on-shell generating functional;
- finite spectral Galerkin packets;
- finite Morse index and nullity;
- Courant--Fischer min--max interface.

### Boundary reduction

For the completed graph the branch constructs:

- bounded value lifts;
- coercive Dirichlet resolvents;
- Poisson operators;
- Dirichlet-to-Neumann/Weyl maps;
- Calderon projectors;
- Cauchy-data Lagrangians;
- Robin Schur operators;
- Krein resolvent formulas;
- relative Robin resolvent formulas;
- coercive Schur inverses;
- reduced classical boundary actions;
- sourced reduced actions and unique minimizers;
- finite Galerkin Schur reductions;
- finite and regularized determinant interfaces;
- one-loop effective boundary actions.

In finite trace dimension, a continuous value-boundary lift is constructed
automatically from surjectivity.

### Gluing and two-sector structure

The branch contains:

- direct sums of two Hilbert Green systems;
- common-boundary gluing of two bulks;
- interface Schur operator `M_left + M_right - J`;
- equivalence of its kernel with glued homogeneous bulk pairs;
- coercive sourced interface solution;
- finite interface determinant and one-loop term;
- exchange involution on two identical sectors;
- even/odd projections;
- symmetric cross-sector mixing;
- exact diagonal/relative quadratic decomposition;
- sourced two-sector parent action and diagonalized Euler equations;
- a physical two-sector analytic facade.

### Perturbation, bifurcation and dynamics

Implemented abstract or finite-mode layers include:

- bounded symmetric perturbations;
- Birman--Schwinger kernel equivalence;
- finite and convergent Neumann-series inverse interfaces;
- parameterized Lyapunov--Schmidt reduction;
- exact pitchfork normal form;
- quartic pitchfork potential and branch stability;
- PT symmetry and PT-even/PT-odd sectors;
- finite-mode heat dynamics;
- finite-mode wave dynamics and energy conservation.

### Spectral invariants

The branch now names the remaining analytic interfaces for:

- positive spectral enumeration;
- heat trace;
- spectral zeta series;
- zeta continuation at zero;
- zeta-regularized determinant;
- Fredholm boundary determinant;
- relative Robin determinant;
- crossing forms;
- boundary spectral flow;
- Maslov index;
- Morse-index change.

## Current physical frontier

The aggregate imports both generic analytic interfaces and concrete physical
facades. It must not be read as an inhabitance theorem for every abstract input.
In particular,
`scalarProgramPFullAnalyticArchitecture_available : True` is only an aggregate
import marker.

### Closed concretely

The canonical scalar development now proves, without an additional physical
axiom:

- spherical coarea, the physical value trace and its continuous extension;
- smooth physical `L²` density and shrinking zero-Cauchy collar cutoffs;
- the smooth cut bulk with boundary and the exact oriented measured
  Green--Stokes identity;
- Green--Stokes closure on the physical Dirichlet, PT-fixed and PT-projected
  sectors, while retaining the generally nonzero unrestricted boundary flux;
- coercivity, source inversion, the unique minimizer, Gaussian positivity,
  self-adjointness and Fredholm index zero in the positive time-static sector;
- compact resolvent at every finite smooth-mode Galerkin cutoff;
- the canonical full graph-`H¹` coercive regulator, physical Rellich compactness
  `H¹ → L²`, its compact response and the associated positive self-adjoint
  elliptic operator/action with compact zero-resolvent.

The intrinsic graph-`H¹` regulator is a proved elliptic realization. It is not
identified with the unrestricted Lorentzian action Hessian.

### Still conditional for the general Lorentzian realization

The remaining scalar work is operator-specific:

1. instantiate the unrestricted off-shell local-divergence/Green package for
   the exact Lorentzian Euler/Jacobi operator and its completed Cauchy trace;
2. prove the required graph/Gårding and higher normal-regularity estimates for
   that operator, sufficient for its closed domain and Hilbert adjoint;
3. realize the Dirichlet condition already derived from Program P boundary
   tangency as a closed Lagrangian operator domain (or justify another physical
   domain), then prove one positive/coercive real shift or an equivalent
   resolvent theorem;
4. construct the continuous physical Poisson solution operator and prove
   uniqueness at the selected parameter; this is the concrete input still
   exposed by the Poisson/DtN facade;
5. derive Lorentzian compact-resolvent and infinite-dimensional spectral
   asymptotics, determinant and parameter-regularity results from that actual
   realization;
6. derive the nonlinear Euler remainder and reduced bifurcation coefficients
   from the full parent bulk/junction action.

Rellich compactness itself is no longer an external obligation. The static and
intrinsic elliptic closures above also show that Program P is not blocked on a
new axiom; the unresolved statements require the indicated operator and domain
estimates.

## Remaining beyond the scalar sector

Even after completing every physical scalar input above, Program P still needs
parallel analytic closure for:

- metric/tensor perturbations;
- gauge-fixed gravitational Hessians;
- gauge and ghost Hilbert complexes;
- BRST/BV-compatible domains and adjoints;
- determinant/superdeterminant cancellation;
- coupled scalar--metric Schur complements;
- the full nonlinear parent bulk plus junction action;
- Lorentzian causal well-posedness where required;
- renormalized infinite-dimensional one-loop quantities.

The existing finite D9 gauge--ghost packet work supplies algebraic models for
some of these steps, but not yet the physical infinite-dimensional realization.

## Validation

The focused aggregate target is:

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
P0EFTJanusMappingTorusScalarProgramPFullAnalyticArchitecture4D
```

Result on 2026-07-26: `Build completed successfully (9317 jobs)`.

The Program P facade and integrity audit were also validated:

```text
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
python scripts/audit_janus_program_p.py
```

Results: facade build successful (`9863` jobs); integrity audit successful,
terminal gates `0/14`.

The canonical active backlog and its terminal-gate semantics are maintained in
[`program_p_operational_todo.md`](program_p_operational_todo.md).
