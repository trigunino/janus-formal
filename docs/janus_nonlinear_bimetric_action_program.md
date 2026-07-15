# Janus Nonlinear Bimetric Action and Junction Program

## Purpose

Derive the finite PT bridge, quasi-local mass reversal and the relation

```text
A = R_s,
E_global = -3 M_bridge/(4 pi)
```

from one covariant two-metric action, including all boundary terms and
constraints.

This program determines the **relational geometry**.  It does not by itself
supply the dimensionful LL charge unit required to fix the absolute value of
`A`.

## Published starting point

The 2024 Janus paper writes a two-sector action containing:

- an Einstein--Hilbert term for each metric;
- matter actions in each sector;
- two interaction functionals denoted schematically by `S_cross` and
  `Sbar_cross`;
- a relative coefficient `kappa`, chosen as `-1` in the Newtonian discussion to
  obtain the desired attraction/repulsion signs.

The explicit nonlinear forms of the cross interaction functionals are not
specified.  Therefore the published coupled equations are not yet a unique
nonlinear action completion.

Primary source: EPJC 84 (2024), DOI
`10.1140/epjc/s10052-024-13569-w`, especially Section 9 and Eqs. 80--104.

## Independent first variations

For a true action `S[g_plus,g_minus]`, stationarity under arbitrary independent
variations splits into two Euler--Lagrange equations.  Bulk equations alone are
insufficient when a nonzero boundary variation remains.

Lean file:

```text
P0EFTJanusTwoMetricFirstVariation.lean
```

A complete action must contain:

```text
S_EH[g_plus] + S_EH[g_minus]
+ S_matter_plus + S_matter_minus
+ S_common_interaction[g_plus,g_minus]
+ S_boundary_plus + S_boundary_minus
+ S_null_boundary
+ S_LL_worldvolume.
```

## Common-action integrability

Two cross-source equations cannot be selected independently if they are to come
from one common interaction functional.

In a linear two-variable reduction,

```text
J_plus  = a x + b y,
J_minus = c x + d y.
```

The work around an infinitesimal rectangle differs by

```text
(c - b) dx dy.
```

Path independence, equivalently the existence of one potential, therefore
requires

```text
b = c.
```

The nonlinear analogue is equality of mixed field-space variations and
closedness of the interaction one-form.

Lean file:

```text
P0EFTJanusBimetricActionIntegrability.lean
```

This is a mandatory acceptance test for any proposed explicit pair of Janus
cross tensors.

## Diagonal Noether identity

A common interaction invariant under diagonal diffeomorphisms gives a combined
exchange identity:

```text
Div_plus + Div_minus = 0.
```

It does not generically imply that both divergences vanish separately.  Separate
conservation is a special zero-exchange branch and must be justified rather than
silently imposed.

Lean file:

```text
P0EFTJanusDiagonalNoetherExchange.lean
```

## Relative kinetic-sign obstruction

The published choice `kappa = -1` places the two reduced spin-2 kinetic
directions at opposite signs if both metrics propagate conventionally.
For

```text
K = a x^2 + b y^2,
a > 0,
b < 0,
```

one direction has positive and one direction has negative quadratic energy.
The branch proves this elementary but unavoidable indefinite-sign result.

Lean file:

```text
P0EFTJanusRelativeKineticSignNoGo.lean
```

A viable completion must prove one of:

1. the second metric is auxiliary or constrained;
2. a gauge constraint removes the negative direction;
3. a PT/Krein quantization produces a positive spectrum and unitary physical
   subspace;
4. both Einstein--Hilbert kinetic terms are positive and the negative-mass sign
   is moved into matter charges or the interaction sector;
5. another explicit nonlinear Hamiltonian mechanism bounds the physical energy.

Without such a theorem, the sign choice is a ghost warning, not a completed
quantum gravitational action.

## Reciprocal ghost-free candidate interaction

A mathematically controlled candidate is the elementary-symmetric two-metric
potential familiar from ghost-free bimetric gravity.  On a proportional branch
`f = c^2 g`, write

```text
V(c) = beta0 + 4 beta1 c + 6 beta2 c^2 + 4 beta3 c^3 + beta4 c^4.
```

Under metric exchange and coefficient reversal:

```text
c^4 V_reversed(1/c) = V(c).
```

A PT-symmetric coefficient choice

```text
beta0 = beta4,
beta1 = beta3
```

is self-reciprocal.  These identities are proved in Lean.

Lean file:

```text
P0EFTJanusReciprocalBimetricPotential.lean
P0EFTJanusPTFlatBimetricVariationalBridge.lean
```

On the concrete one-dimensional positive PT-flat proportional branch, the
reduced interaction has its actual derivative, `c = 1` is stationary, and its
actual Hessian is twelve times the Fierz--Pauli mass combination. For
`beta1 > 0`, `beta2 >= 0`, the Hessian is positive and `c = 1` is the unique
global minimizer on `c > 0`. This is a reduced candidate-sector result, not a
variational or stability theorem for the full Janus metric field theory.

This is a candidate completion, not something already derived from the Janus
paper.  It must still pass:

- matrix square-root branch existence;
- nonlinear constraint/no-Boulware--Deser-ghost proof;
- Janus Newtonian sign matrix;
- local GR limit;
- correct determinant weights;
- finite null-boundary junction;
- stable cosmological branch.

Primary ghost-free bimetric references:
`arXiv:1109.3515`, `arXiv:1111.2070`, `arXiv:1106.3344`.

## PT quasi-local charge

Let PT act involutively on boundary states and let a quasi-local Hamiltonian
charge be PT odd:

```text
Q[PT state] = -Q[state].
```

For paired boundaries the signed charges are opposite.  If the bridge mass is
defined as the positive magnitude of the negative-sector charge, it equals the
positive-fold charge.

Lean file:

```text
P0EFTJanusPTQuasilocalChargePairing.lean
```

The algebraic sign reversal is closed.  The physical proof must construct the
covariant phase space, boundary symplectic potential, integrable Hamiltonian
charge, and its PT action with the correct normal/time orientations.

## Misner--Sharp reduction and finite bridge

For homogeneous signed density

```text
rho = E_global/a^3
```

inside a finite comoving sphere of areal radius `R=a r`, the Misner--Sharp mass
reduces to

```text
3 M_MS = 4 pi E_global r^3.
```

With PT mass reversal

```text
M_bridge = -M_MS
```

and the horizon compactness law

```text
c^2 R_boundary = 2 G M_bridge,
R_boundary = A r,
3 c^2 A = -8 pi G E_global,
```

positivity selects

```text
r = 1,
R_boundary = A,
4 pi E_global + 3 M_bridge = 0.
```

Lean file:

```text
P0EFTJanusMisnerSharpPTBridge.lean
```

Thus the previously ad hoc finite-boundary mass law is reduced to standard
homogeneous quasi-local mass plus the single Janus-specific PT-odd charge
statement.

## Acceptance criteria

The nonlinear program closes only after:

1. defining one common manifold/solder comparison for both metrics;
2. specifying the full action including all boundary and LL terms;
3. deriving both field equations by independent variation;
4. proving mixed-variation integrability;
5. deriving the diagonal Noether exchange law;
6. resolving the relative kinetic-sign problem;
7. closing the nonlinear constraint algebra;
8. proving a stable local-GR branch;
9. constructing integrable PT-odd quasi-local charges;
10. deriving the null junction and horizon compactness law;
11. recovering the finite-sphere bridge and `A=R_s` relation;
12. importing no observational scale.

## Verdict

This program can close the classical and geometric half of the alpha problem.
It cannot select an absolute length from dimensionless interaction coefficients
alone.  Even after a perfect nonlinear action is derived, a quantum or
microscopic normalization of the LL charge is still needed.
