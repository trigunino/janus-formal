# Program P.E-S — Structured jet groupoids and low-order normal forms

> Categorical theorem: [`program_pe_categorical_jet_equivalence.md`](program_pe_categorical_jet_equivalence.md)  
> Finite-jet proof architecture: [`program_pe_jet_universality_proof.md`](program_pe_jet_universality_proof.md)  
> Pairing globalization: [`program_pd_global_pairing_modules.md`](program_pd_global_pairing_modules.md)

## Objective

The categorical theorem reduces regular local finite-order natural operators to
equivariant maps once the structured jet presentation exists. The next geometric
lock is therefore not another abstract categorical lemma. It is the construction
and reduction of the structured jet groupoid

```text
Gamma_R  ==>  B_R
```

for decorated SpinC immersions.

This document records the first exact algebraic steps toward that construction
and states precisely what remains conditional.

## Current verdict

### Theorem S1 — proved in Lean: action-groupoid core

For any group `G` acting on a base `B`, the repository constructs arrows

```text
ActionArrow x y = { g : G // g . x = y }
```

with identity, composition and inverse. It proves the identity, associativity and
inverse laws. It also proves:

```text
End_ActionGroupoid(x)  ~=  Stabilizer_G(x),
```

and supplies the descent interface for a family of fibers transported along
groupoid arrows.

Lean:

```text
P0EFTJanusStructuredJetActionGroupoid.lean
```

Principal results:

```text
comp_id
id_comp
comp_assoc
inverse_comp
comp_inverse
endomorphismEquivStabilizer
equivariant_section_is_isotropy_fixed
```

This is a genuine algebraic groupoid theorem. It does **not** construct the
actual finite-dimensional smooth Janus jet base or the finite jet symmetry
group acting on it.

### Theorem S2 — proved in Lean: normalized immersion second-jet orbit

After the first derivative of an immersion has been normalized to the standard
tangent inclusion, split the quadratic term abstractly as

```text
Q = (Q_tangent, Q_normal).
```

A quadratic source-coordinate change translates `Q_tangent` and leaves
`Q_normal` fixed. The repository proves:

```text
Q_1 and Q_2 are source-reparametrization equivalent
  iff
Q_1.normal = Q_2.normal.
```

Every orbit meets the slice

```text
Q_tangent = 0
```

in exactly one point. The explicit change is `-Q_tangent`.

Lean:

```text
P0EFTJanusSecondJetNormalForm.lean
```

Principal results:

```text
chosen_change_reaches_normal_form
equivalent_iff_normal_eq
every_orbit_meets_normal_slice
normal_slice_representative_unique
```

The theorem is exact for the declared additive model. Its geometric
interpretation as the second fundamental form remains conditional on proving
that the actual source two-jet action has this translation form after adapted
first-order normalization.

### Theorem S3 — proved in Lean: abelian connection one-jet orbit

Decompose a local abelian connection one-jet into

```text
(A(0), symmetric derivative, curvature component).
```

A gauge two-jet changes the first two components and leaves curvature fixed. The
repository proves:

```text
connection jets are gauge equivalent
  iff
their curvature components agree.
```

Every orbit meets the curvature-only slice uniquely.

Lean:

```text
P0EFTJanusAbelianConnectionJetNormalForm.lean
```

Principal results:

```text
chosen_gauge_reaches_curvature_normal_form
curvature_is_gauge_invariant
gauge_equivalent_iff_curvature_eq
every_orbit_meets_curvature_slice
curvature_slice_representative_unique
```

Again, this is exact for the decomposed algebraic model. The actual geometric
step is to derive the decomposition from

```text
A -> A + d chi
```

and identify the alternating derivative with the curvature two-form.

### Executable exact audit

The Python audit uses rational arithmetic to instantiate both normal forms with
explicit matrices:

```text
python scripts/audit_janus_low_order_jet_normal_forms.py
pytest -q tests/test_janus_low_order_jet_normal_forms.py
```

It verifies exactly that:

- the quadratic source correction kills the tangent-valued immersion term;
- the normal-valued term is unchanged;
- the gauge gradient kills `A(0)`;
- the gauge Hessian kills the symmetric derivative;
- the residual derivative is alternating;
- the curvature matrix `D - D^T` is gauge invariant.

This is executable evidence, not a replacement for the smooth geometric theorem.

### Theorem S4 — proved in Lean: isotropy ranks can jump

The finite model has one fixed background and one free two-point orbit. The
field carries the sign representation.

At the fixed background, the nontrivial symmetry belongs to the isotropy group
and forces every invariant linear functional to vanish. On the free orbit, the
isotropy is trivial and every scalar multiple is allowed.

Lean:

```text
P0EFTJanusIsotropyStratification.lean
```

Principal results:

```text
fixed_background_invariant_iff_zero
false_background_every_coefficient_invariant
no_nonzero_invariant_on_fixed_stratum
nonzero_invariant_exists_on_free_stratum
orbit_stratification_and_invariant_jump
```

Therefore a classification on the principal orbit type need not extend to a
higher-isotropy stratum. The actual Janus pairing problem must be stratified.

## 1. Action groupoid required by the Janus problem

Fix source dimension `p`, ambient dimension `q`, signature and an order `R`.
A candidate object of `B_R` should include the admissible `R`-jet of:

```text
immersion i : Sigma -> M,
ambient metric and induced tangent/normal splitting,
SpinC principal data,
SpinC and U(1) connections,
normal orientation/root data,
chosen square-root or Z4 lift when present,
PT decoration,
BRST/ghost grading when it is part of the local category.
```

The arrow group should combine finite jets of:

```text
source coordinate changes,
ambient coordinate changes,
tangent and normal frame changes,
SpinC/U(1) gauge changes,
discrete PT/Z4 transformations.
```

The first serious theorem must show that these changes preserve the admissible
jet constraints and define a smooth action, or more generally a differentiable
groupoid when one global action presentation is insufficient.

## 2. Low-order immersion calculation to be promoted

Let

```text
A = d i_0 : V -> W,
Q = d^2 i_0 in Sym^2(V*) tensor W.
```

After choosing orthonormal adapted frames, normalize

```text
A(v) = (v,0) in V direct-sum N.
```

Write

```text
Q = Q_tangent + Q_normal.
```

A source coordinate change

```text
phi(x) = x + 1/2 C(x,x) + O(|x|^3)
```

changes the quadratic term by

```text
Q -> Q + A o C
```

up to the convention determined by precomposition with `phi` or `phi^{-1}`.
Because `A : V -> A(V)` is an isomorphism, choose `C` so that

```text
A o C = -Q_tangent.
```

The residual tensor is

```text
B = Q_normal in Sym^2(V*) tensor N.
```

The new Lean theorem proves exactly the additive orbit step after this formula
has been established. It does not yet formalize:

- symmetric bilinear maps `Sym^2(V*) tensor V` and `Sym^2(V*) tensor N`;
- the chain-rule computation for the actual second jet;
- first-order normalization by source/ambient orthogonal frames;
- the residual `O(V) x O(N)` or SpinC-compatible action.

## 3. Low-order connection calculation to be promoted

For a local `U(1)` connection

```text
A = A_i(x) dx^i,
```

a gauge parameter `chi` changes

```text
A_i(0) -> A_i(0) + partial_i chi(0),
partial_j A_i(0)
  -> partial_j A_i(0) + partial_j partial_i chi(0).
```

The gradient of `chi` kills `A(0)`. Its Hessian is symmetric and kills the
symmetric part of `partial_j A_i`. The alternating part is

```text
F_ji = partial_j A_i - partial_i A_j.
```

The new Lean theorem proves the resulting orbit classification after the
symmetric/alternating decomposition has been supplied. The Python audit verifies
the matrix formula exactly.

## 4. What is now demonstrated

The following statement is no longer conjectural at the abstract algebraic
level:

```text
an action groupoid organizes backgrounds, arrows and isotropy;
source/gauge-removable low-order jet components are orbit directions;
normal immersion curvature and abelian gauge curvature are quotient data;
isotropy can change the available invariant fibers between strata.
```

These facts materially narrow the geometric problem. They do not prove that the
full SpinC immersion jet quotient is represented by a finite list of curvature
tensors.

## 5. Remaining geometric locks

### Lock G1 — actual finite jet base

Construct `B_R` as a smooth finite-dimensional space or stratified space of
admissible jets. The immersion condition is open at first order, but metric,
SpinC, normal-root and compatibility constraints must be stated explicitly.

### Lock G2 — actual symmetry action

Construct the source, ambient, frame and gauge jet action on `B_R`. Prove the
action/groupoid laws and compatibility with truncation in `R`.

### Lock G3 — geometric second-jet theorem

Promote the abstract second-jet orbit theorem to the actual symmetric-tensor
model and prove that the residual object is the second fundamental form under
the residual tangent/normal frame group.

### Lock G4 — higher-order jet isomorphism theorem

Prove inductively that normalized higher jets are encoded by tensors such as

```text
ambient curvature and covariant derivatives,
second fundamental form and covariant derivatives,
normal curvature,
SpinC/twist curvature and covariant derivatives,
```

subject to Gauss--Codazzi--Ricci--Bianchi identities and formal integrability
conditions.

### Lock G5 — isotropy stratification

Classify orbit types and stabilizers. Compute invariant fiber ranks on each
stratum and prove when equivariant maps on the principal stratum extend smoothly
to singular strata.

### Lock G6 — effective descent

Prove that the declared natural tensor, spinor, twist and ghost sectors are
exactly equivariant bundles over the structured jet groupoid, with global
SpinC/root/holonomy data retained separately.

## 6. Counterexample discipline

The current results rule out three invalid shortcuts:

```text
one generic isotropy computation
  does not classify all strata;

one abstract action groupoid
  does not construct the geometric Janus jet action;

one low-order normal form
  does not prove finite generation at every order.
```

Any future finite-generation claim must first identify the residual group after
normalization. Compact residual groups permit strong invariant-theory tools;
noncompact pseudo-Riemannian residual groups require separate arguments.

## 7. Immediate theorem queue

1. Formalize the chain rule for a normalized second immersion jet in a concrete
   finite-dimensional symmetric-bilinear model.
2. Identify the residual orthogonal action on the normal quadratic tensor.
3. Formalize the gradient/Hessian decomposition of a concrete abelian connection
   one-jet and identify the alternating part with curvature.
4. Combine these two reductions into the first nontrivial structured background
   jet base.
5. Define its action groupoid using the abstract core already proved.
6. Compute the first orbit types and their stabilizers.
7. Classify scalar invariants and pairing covariants on this low-order model.
8. Attempt extension to one higher covariant derivative; stop and record the
   exact integrability obstruction if the induction fails.

## Evidence table

| Statement | Status |
| --- | --- |
| action-groupoid laws for an arbitrary group action | Lean theorem |
| endomorphisms equal stabilizer | Lean equivalence |
| abstract immersion second-jet orbit classified by normal part | Lean theorem |
| abstract abelian connection one-jet orbit classified by curvature | Lean theorem |
| explicit rational matrix normalizations | Python exact audit |
| isotropy can change invariant fiber freedom | Lean finite counterexample |
| actual smooth Janus jet base and action | open |
| actual second fundamental form quotient theorem in Lean | open |
| actual SpinC/twist connection jet reduction | open |
| higher-order jet isomorphism theorem | open |
| stratified extension theorem | open |
| effective descent for Janus natural bundles | open |
