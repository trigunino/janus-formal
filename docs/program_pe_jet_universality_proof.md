# Program P.E-J — Finite-Jet Universality Proof

> Master project map: [`program_master_roadmap.md`](program_master_roadmap.md)  
> Precise Lemma 2: [`program_pe_lemma2_naturality_equivariance.md`](program_pe_lemma2_naturality_equivariance.md)

## Question

Can one prove that every local natural theory attached to a decorated SpinC
immersion is determined, up to natural equivalence, by equivariant invariants of
a finite jet?

## Verdict

The original sentence is too strong. The strongest defensible theorem is:

> **Corrected local finite-jet universality theorem.** Fix natural source and
> target bundles over a category of decorated SpinC immersions. A regular local
> natural operator is locally represented by a smooth map from a finite jet
> bundle. Once holonomic jets are realizable, that representing map is unique,
> and naturality of the operator is equivalent to equivariance of the jet map
> under the adapted jet symmetry group. For scalar targets the map is an
> invariant smooth function; for nontrivial targets it is an equivariant
> covariant.

Four qualifications are essential:

1. Peetre–Slovák gives local finite order under regularity and locality;
2. one uniform global order requires a bounded region and finite subcover;
3. smooth equivariant dependence is not automatically polynomial;
4. naturality does not imply ellipticity or select field bundles.

## Proof architecture

### 1. Peetre–Slovák reduction

For a regular local sheaf morphism

```text
D : Gamma(F) -> Gamma(E),
```

Peetre–Slovák supplies locally an order `k` and smooth evaluator

```text
Phi : J^k(F) -> E
```

such that

```text
D(s)(x) = Phi(j_x^k s).
```

This analytic theorem is used as an interface and is not reproved in Mathlib.

### 2. Naturality implies equivariance

Choose an adapted frame and compatible actions on sections, jets and targets.
If jet realization is surjective and

```text
D = Phi o j^k,
```

then

```text
D natural  <->  Phi equivariant.
```

Lean:

```text
P0EFTJanusFiniteJetEquivariance
  .operator_natural_iff_evaluator_equivariant
```

The exact intrinsic/fiber-model statement and the order qualification for the
adapted jet group are documented separately in
`program_pe_lemma2_naturality_equivariance.md`.

### 3. Uniqueness

If two evaluators represent the same operator and every finite jet is
holonomically realizable, evaluate on a section realizing an arbitrary jet.
The evaluators agree everywhere.

Lean:

```text
P0EFTJanusFiniteJetEquivariance
  .evaluator_unique_of_surjective_jet
  .exists_unique_equivariant_evaluator
```

### 4. Local-to-uniform order

A finite collection of local orders has a common upper bound and lower-order
evaluators lift by jet truncation. An infinite family of componentwise finite
orders need not have one global bound.

Lean:

```text
P0EFTJanusFiniteOrderUniformization
  .lifted_evaluator_factorization
  .finite_local_orders_have_common_bound
  .componentwise_finite_order_has_no_uniform_bound
```

### 5. Scalar invariants versus covariants

For a trivial scalar target:

```text
Phi(g.j) = Phi(j).
```

For tensor, spinor or ghost targets:

```text
Phi(g.j) = g.Phi(j).
```

The second case is equivariant/covariant, not scalar-invariant.

### 6. Smooth is not automatically polynomial

The order-zero natural scalar operation

```text
D(s)(x) = exp(s(x))
```

is smooth and local but nonpolynomial. The Lean model proves

```text
Delta^n exp(x) = (exp(1)-1)^n exp(x),
```

so no finite forward difference vanishes.

Lean:

```text
P0EFTJanusSmoothNotPolynomial.lean
```

### 7. Ellipticity is independent

The zero operator is natural but has a noninjective symbol. Thus finite-jet
naturality does not imply ellipticity.

Lean:

```text
P0EFTJanusCorrectedJetUniversality
  .naturality_does_not_imply_symbol_injectivity
```

## Exact theorem currently formalized

Given:

- compatible actions on sections, jets and targets;
- equivariant jet prolongation;
- surjective jet realization;
- a factorized operator;

the repository proves:

```text
operator natural
  iff
unique jet evaluator equivariant.
```

Stable head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

## Janus specialization still open

1. Define the actual category of decorated Janus SpinC immersions.
2. Construct the adapted finite jet group, including tangent/ambient frame,
   SpinC/U(1), normal `Z4`, PT and BRST/Grassmann data.
3. Prove finite natural order of the selected source/target bundles.
4. Verify sheaf locality and regularity for each operator.
5. Specialize Peetre–Slovák to the chosen category.
6. Prove holonomic realization for the required jet fibers.
7. Specify a bounded Janus-background region for any uniform order claim.
8. Classify smooth equivariant maps on those finite jet fibers.
9. Add polynomial dependence only for a separately defined polynomial subclass.
10. Impose ellipticity, Helmholtz, anomaly and renormalization independently.

## Evidence matrix

| Claim | Status |
| --- | --- |
| finite-jet naturality/equivariance equivalence | proved in Lean model |
| evaluator uniqueness under jet surjectivity | proved in Lean model |
| finite local orders admit a common finite bound | proved in Lean model |
| local finite order need not have a global bound | proved in Lean model |
| smooth natural does not imply polynomial | explicit counterexample and Lean finite-difference proof |
| Peetre–Slovák for actual Janus category | analytic interface; specialization open |
| actual adapted SpinC jet group | open |
| full smooth equivariant-map classification | open |
| polynomial invariant classification | conditional on polynomial dependence |
| ellipticity | independent open theorem |

## Final statement

```text
regular + local + natural
  -> locally finite-jet
  -> unique smooth equivariant evaluator,
```

with global order, polynomiality, ellipticity and field-content selection kept as
separate hypotheses or theorems.

## Primary references

- J. Navarro and J. B. Sancho, *Peetre–Slovák's theorem revisited*.
- I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*.
- J. Navarro and J. B. Sancho, *Natural operations on differential forms*.
