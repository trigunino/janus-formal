# Program P — Variational Principle and Action Reconstruction

## Purpose

Programs D8–D11 identify the Janus topology, natural bundles, principal symbols,
elliptic complexes and determinant-line framework. They do **not** select one
physical action. Program P isolates that remaining problem:

> How can the Janus action be characterized, selected or reconstructed without
> fitting the desired radius or effective vacuum?

Program P has three routes:

```text
P-A  universal property / parent-bulk reduction
P-B  anomaly cancellation and discrete consistency selection
P-C  inverse calculus of variations / Helmholtz reconstruction
```

The routes are complementary. None is sufficient alone in its weakest form.

## Evidence labels

| Code | Meaning |
| --- | --- |
| **T** | exact algebra/theorem checked in Lean |
| **C** | conditional theorem from explicitly named inputs |
| **P** | physical or analytic derivation still open |
| **N** | no-go or correction |

## P0 — Moduli geometry does not select a potential

A metric on moduli does not select a scalar functional. A symplectic form does
not select a Hamiltonian. A Kähler-like package combines metric, complex and
symplectic structures but still leaves the moment map or potential as extra
data.

Lean:

```text
P0EFTJanusModuliGeometryNoGo.lean
```

Exact finite-dimensional witnesses prove:

```text
same metric + different potentials,
same metric + different gradients,
same symplectic form + different Hamiltonians.
```

### Verdict

```text
(Moduli, metric, symplectic form, complex structure)
  does not imply
one Janus action.
```

This removes the earlier speculative claim that a Kähler structure alone could
make the action inevitable.

---

# P-A — Relative universal property

## A.1 Hessian ambiguity

For a quadratic action

```text
S(x) = h*x^2/2 + l*x + c,
```

the Hessian fixes only `h`. Two actions with the same Hessian differ by an
affine functional:

```text
ΔS(x) = Δl*x + Δc.
```

Lean:

```text
P0EFTJanusUniversalActionProperty
  .same_hessian_difference_is_affine
  .fixed_hessian_supports_distinct_actions
```

This is the local one-loop version of the general freedom by boundary terms,
null Lagrangians, topological terms and finite counterterms.

## A.2 Relative unique-existence theorem

A quadratic action is uniquely fixed once all three items are supplied:

1. Hessian `h`;
2. critical point `x_*`;
3. reference value `S(x_*)`.

The canonical representative is

```text
S(x) = h*x^2/2 - h*x_* * x
       + S(x_*) + h*x_*^2/2.
```

The realization fiber is proved nonempty and subsingleton.

Lean:

```text
P0EFTJanusUniversalActionProperty
  .specification_fiber_unique_existence
```

### Interpretation

P-A gives a true universal/terminal property only **relative to a complete
specification**. It does not explain where the specification comes from.

## A.3 Strongest concrete source: parent-bulk on-shell action

The current strongest non-tautological source is a parent bulk action. At fixed
throat data:

1. solve the bulk Euler equation;
2. evaluate the bulk-plus-junction action on shell;
3. obtain the nonlocal boundary action;
4. identify its Hessian as a Schur complement or, for PDEs, a
   Dirichlet-to-Neumann/Calderón operator plus local terms.

In the quadratic proxy,

```text
S_bulk(X,q)
  = A*X^2/2 + B*X*q + C*q^2/2,

X_*(q) = -B*q/A,

S_boundary(q)
  = (C - B^2/A)*q^2/2.
```

Lean:

```text
P0EFTJanusBulkReducedPotential.lean
P0EFTJanusBulkUniversalHelmholtzSynthesis.lean
```

The on-shell boundary action is exactly the canonical P-A action associated to
the reduced Hessian, zero critical point and zero reference value.

### P-A verdict

```text
parent action + boundary problem
  -> relative canonical throat action.
```

But changing the parent action, its normalization or boundary terms changes the
throat action. P-A transfers the uniqueness problem to the parent theory; it
does not erase it.

---

# P-B — Anomaly cancellation and discrete selection

## B.1 What anomaly cancellation does

PT conjugation reverses the parity-odd anomaly and preserves parity-even data.
For one sector with anomaly coefficient `a`:

```text
a + (-a) = 0.
```

The same pairing doubles parity-even couplings and finite parity-even
counterterms.

Lean:

```text
P0EFTJanusAnomalySelection
  .pt_pair_anomaly_cancels
  .pt_pair_even_coupling_doubles
  .pt_pair_even_counterterm_doubles
```

## B.2 What anomaly cancellation does not do

Two distinct actions may both have zero anomaly but different parity-even
couplings. Adding any parity-even finite counterterm preserves anomaly
cancellation. A flat determinant line still has multiple constant
trivialization phases.

Lean:

```text
P0EFTJanusAnomalySelection
  .anomaly_cancellation_does_not_select_even_coupling
  .add_even_counterterm_preserves_anomaly
  .anomaly_free_line_has_nonunique_constant_trivialization
```

Thus:

```text
anomaly-free
  does not imply
unique action or unique partition section.
```

## B.3 Discrete arithmetic can be selected conditionally

If a regulator/bare level is independently fixed, anomaly minimality can select
multiplicity. In the current half-level proxy:

```text
2*(-2) + N = 1  ->  N = 5.
```

Lean:

```text
bare_minus_two_minimal_half_level_forces_five
```

This explains how P-B can constrain discrete field content. It does not prove
that the regulator level `-2`, the statistics signs or the complete field/ghost
complex are generated by Janus geometry.

### P-B verdict

P-B is a **consistency filter and discrete selector**, not a complete action
principle. It should be applied after candidate field content and regulator data
are derived.

---

# P-C — Hessian and Helmholtz reconstruction

P-C is the strongest mathematical route because it addresses the inverse
problem of the calculus of variations.

## C.1 Finite-dimensional Helmholtz theorem

For a two-field linear operator

```text
H = [[a,b],
     [c,d]],
```

the necessary and sufficient condition for it to be the Hessian of a quadratic
potential is

```text
b = c.
```

That is formal self-adjointness.

Lean:

```text
P0EFTJanusHessianHelmholtzReconstruction
  .helmholtz_realizability_iff
  .nonsymmetric_operator_is_not_variational
```

## C.2 Reconstruction ambiguity

Even when the Hessian is integrable, the potential is determined only modulo
an affine functional. For two fields:

```text
ΔS(x,y) = A*x + B*y + C.
```

Lean:

```text
equal_hessian_difference_affine
same_hessian_has_distinct_affine_completions
```

## C.3 PT plus normalization removes the quadratic ambiguity

If the action is PT-even around the selected background, the linear terms
vanish. One reference normalization removes the constant. Therefore:

```text
self-adjoint Hessian
+ PT evenness
+ S(0)=0
  -> unique quadratic action.
```

Lean:

```text
pt_normalized_reconstruction_unique_existence
```

This is a genuine one-loop reconstruction theorem.

## C.4 Nonlinear field theory: full Helmholtz problem

For a nonlinear local field theory, formal self-adjointness is necessary but is
not generally sufficient by itself. A complete reconstruction requires:

1. a local Euler–Lagrange source form;
2. compatible gauge/Noether identities;
3. full Helmholtz conditions on its linearization;
4. vanishing of the relevant variational-bicomplex obstruction;
5. classification of boundary terms and null Lagrangians;
6. PT/discrete symmetries;
7. normalization and finite counterterm laws.

Lean interface:

```text
LocalHelmholtzReconstructionStatus
localHelmholtzReconstructionClosed
```

### Critical distinction

A Hessian at one background reconstructs only the **quadratic one-loop action
near that background**. It cannot determine the full nonlinear action away from
the background. For that, the complete Euler–Lagrange family or equivalent
higher-variation data are required.

### P-C verdict

P-C is the preferred inverse route:

```text
Euler–Lagrange family
+ Helmholtz
+ variational cohomology
  -> action class modulo null terms;

PT + normalization + microscopic finite parts
  -> selected representative.
```

---

# Route matrix

| Route | What it can select | Main theorem | Remaining freedom | Role |
| --- | --- | --- | --- | --- |
| P-A | one action relative to a full specification or parent bulk action | realization fiber is unique; Schur-reduced action is canonical relative to parent | parent action, boundary terms, normalization | constructive source |
| P-B | anomaly-free subspace and sometimes discrete multiplicity | PT anomaly cancellation; conditional `N=5` arithmetic | parity-even dynamics, trivialization, finite counterterms | filter/selector |
| P-C | local action class from variational operator | Helmholtz realizability; PT-normalized quadratic uniqueness | nonlinear cohomology, null terms, finite parts | strongest inverse theorem |

## Recommended synthesis

```text
Parent bulk/microscopic law          P-A
             |
             v
full throat Euler–Lagrange family
             |
             v
Helmholtz + variational cohomology   P-C
             |
             v
action class modulo null terms
             |
     anomaly and PT constraints      P-B
             |
             v
normalization + finite-part law
             |
             v
selected renormalized Janus action
```

P-B should not be asked to generate parity-even dynamics. P-A should not be
called absolute unless the parent theory is derived. P-C should not be claimed
from a Hessian at one point when the desired conclusion is a global nonlinear
action.

# Stable Lean entry point

```text
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
```

Imported modules:

```text
P0EFTJanusModuliGeometryNoGo.lean
P0EFTJanusUniversalActionProperty.lean
P0EFTJanusAnomalySelection.lean
P0EFTJanusHessianHelmholtzReconstruction.lean
P0EFTJanusBulkUniversalHelmholtzSynthesis.lean
```

# Terminal research queue

1. Specify the exact Janus field space and choose induced, auxiliary or bulk
   metric formulation without double counting.
2. Classify all local `Diff × U(1) × PT × Z4` invariant densities up to a fixed
   derivative order.
3. Derive a parent bulk/junction action or another microscopic coefficient law.
4. Compute the complete throat Euler–Lagrange operator, including constraints
   and ghosts.
5. Prove the nonlinear Helmholtz conditions.
6. Compute the relevant variational-bicomplex cohomology on the one-sided
   SpinC throat.
7. Classify null Lagrangians, topological terms and boundary functionals.
8. Apply local and global anomaly cancellation to the already derived field
   content.
9. Fix the partition-section phase, overall normalization and finite
   counterterms without using the desired radius.
10. Prove that the resulting Hessian equals the natural Fredholm family from
    Programs D9–D11.
11. Compute the renormalized effective action and establish a unique stable
    vacuum.

# Final verdict

Program P has not produced a unique physical Janus action. It has produced a
sharp theorem architecture:

```text
moduli geometry alone: insufficient;
P-A: relative canonicity;
P-B: anomaly consistency and discrete filtering;
P-C: variational reconstruction, strongest route.
```

The best current strategy is the **P-A + P-C synthesis**, with P-B applied as an
independent consistency condition. The decisive missing theorem is a derived
parent/microscopic Euler–Lagrange law plus a full nonlinear Helmholtz and
variational-cohomology proof.
