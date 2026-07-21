# Program P scalar analytic architecture

## Status

This document describes the long-form scalar analytic development on
`dev-branch` after the global cut-bulk Green--Stokes theorem.

The new leaves are intentionally **not yet build-validated**.  They were added
while local Lean builds were unavailable.  The declarations therefore form a
large proposed architecture that must be compiled and repaired in dependency
order before it can be merged into the trusted main head.

No Codex task, Codex CLI session or manually triggered GitHub Actions workflow
was used to create this development.

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

## Exact remaining physical inputs

The generic architecture does not itself prove that the current concrete Janus
scalar Euler operator satisfies the required analysis.  The principal remaining
results are the following.

### 1. Identify the concrete physical operator

Construct the exact physical scalar Euler/Jacobi operator as a linear map on the
smooth quotient-field core and prove that its bulk pairing defect is the global
Green boundary form already formalized.

### 2. Construct the concrete normal trace

Define the physical normal derivative in the canonical throat `L²` space and
prove that its Hilbert symplectic pairing is exactly the oriented global boundary
current.

### 3. Paired trace graph estimate

Prove a bound of the form

```text
‖(γ₀u, γ₁u)‖ ≤ C ‖(u, Au)‖graph.
```

This extends the paired trace to the completed graph.

### 4. Closability and closedness

Prove that the first projection of the completed graph is injective, equivalently
that the concrete smooth operator is closable in the physical bulk `L²` space.

### 5. Intrinsic Sobolev identification

Relate the current physical graph-`H¹` completion to an intrinsic Sobolev space
on the mapping torus/cut bulk.  The present graph space is operational but not
yet identified with the expected intrinsic geometric space.

### 6. Density of boundary domains

For the chosen Dirichlet, Neumann, Robin or general Lagrangian condition, prove
that its actual closed operator domain is dense in the bulk Hilbert space.

### 7. Actual Hilbert adjoint characterization

Prove that the domain of the genuine unbounded Hilbert adjoint is exactly the
boundary-adjoint test supplied by the Green identity.  Lagrangian maximality
then gives self-adjointness automatically.

### 8. Dirichlet coercivity and surjectivity

At at least one real spectral parameter, prove the lower graph-norm estimate and
surjectivity of the completed Dirichlet shifted operator.  This constructs the
Dirichlet resolvent and therefore the Poisson, Weyl and Calderon objects.

### 9. Schur coercivity or Fredholm alternative

For a selected Robin/junction operator, prove either:

- coercivity plus surjectivity of the Schur operator; or
- a Fredholm theorem with a controlled kernel/cokernel.

This produces the Krein resolvent and unique reduced-action minimizer away from
crossings.

### 10. Compact embedding / compact resolvent

Prove compactness of the relevant closed-domain inclusion into physical bulk
`L²`, or directly prove compactness of one bounded resolvent.

### 11. Semibounded quadratic form

Establish an explicit lower bound for the physical Jacobi quadratic form.  A
strictly positive bound gives zero-resolvent invertibility and the Gaussian
source solution.

### 12. Spectral asymptotics

Construct an eigenvalue enumeration, prove Weyl/counting estimates, heat-trace
summability and the analytic continuation needed for the zeta determinant.

### 13. Infinite-dimensional Fredholm determinant

Construct a trace-class or relative determinant for the physical boundary Schur
family and prove the zero/kernel correspondence required by the one-loop and
spectral-flow interfaces.

### 14. Parameter regularity

Prove continuity/differentiability/analyticity in the spectral and geometric
parameters for Dirichlet resolvents, Poisson maps, Weyl functions and Schur
operators.  This is needed for crossing forms, spectral flow and perturbation
expansions.

### 15. Concrete nonlinear remainder

Derive the actual nonlinear Euler map from the parent bulk/junction action,
identify its linearization, construct the Lyapunov--Schmidt complement solver and
compute the reduced cubic/quartic coefficients.

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

## Future validation order

When local builds resume, validate in the following order rather than compiling
the aggregate head immediately:

1. `ScalarCompletedBoundaryDomains4D`;
2. `ScalarClosedGraphRealization4D`;
3. `ScalarClosedSeparatedRealization4D`;
4. `ScalarClosedResolvent4D`;
5. `ScalarAbstractLagrangianBoundary4D`;
6. compact spectral and variational leaves;
7. graph Poisson/DtN/Calderon/Krein leaves;
8. physical bridge/facade leaves;
9. two-sector and interface leaves;
10. determinant, zeta, perturbation and nonlinear leaves;
11. `ScalarProgramPFullAnalyticArchitecture4D` last.

The aggregate target is:

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
P0EFTJanusMappingTorusScalarProgramPFullAnalyticArchitecture4D
```
