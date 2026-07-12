# Program P.E-J — Finite-Jet Universality Proof

## Question

Can one prove that every local natural theory attached to a decorated SpinC
immersion is determined, up to natural equivalence, by equivariant invariants of
a finite jet?

## Verdict

The original sentence is too strong.  The strongest defensible theorem is:

> **Corrected local finite-jet universality theorem.**  Fix natural source and
> target bundles over a category of decorated SpinC immersions.  A regular local
> natural operator is locally represented by a smooth map from a finite jet
> bundle.  Once holonomic jets are realizable, that representing map is unique,
> and naturality of the operator is equivalent to equivariance of the jet map
> under the adapted jet symmetry group.  For scalar targets the map is an
> invariant smooth function; for nontrivial targets it is an equivariant
> covariant.

Four qualifications are essential:

1. the Peetre--Slovak theorem gives local finite order under regularity and
   locality hypotheses;
2. one uniform global order requires a bounded/compact family and a finite
   subcover in the relevant jet region;
3. smooth equivariant dependence is not automatically polynomial;
4. naturality does not imply ellipticity and does not choose the field bundles.

## Why the polynomial statement is false

On the trivial scalar bundle, define

```text
D(s)(x) = exp(s(x)).
```

This operation:

- is local of order zero;
- commutes with every pullback;
- is smooth;
- is not polynomial in the zero-jet variable.

The Lean model proves the exact finite-difference identity

```text
Delta^n exp(x) = (exp(1)-1)^n exp(x),
```

so no finite iterate of the forward difference vanishes.  Every ordinary
polynomial of finite degree has a vanishing sufficiently high finite
difference, hence the exponential operation lies outside the polynomial
subclass.

Lean:

```text
P0EFTJanusSmoothNotPolynomial.lean
```

## Proof architecture

### Step 1 — Peetre--Slovak reduction

Let `F` and `E` be smooth natural bundles and

```text
D : Gamma(F) -> Gamma(E)
```

a regular morphism of sheaves.  The Peetre--Slovak theorem supplies, locally in
the infinite jet space, an integer `k` and a smooth evaluator

```text
Phi : J^k(F) -> E
```

such that

```text
D(s)(x) = Phi(j_x^k s).
```

This analytic theorem is not reproved in Mathlib here.  Program P.E-J records
its hypotheses and formalizes everything downstream of the factorization.

### Step 2 — Equivariance from naturality

Choose an adapted SpinC immersion frame.  Let the local symmetry act on
sections, jets and the target fiber.  Suppose the jet realization map is
surjective.  If

```text
D = Phi o j^k,
```

then

```text
D natural  <->  Phi equivariant.
```

The reverse implication is immediate from equivariance of jet prolongation.
For the forward implication, realize an arbitrary jet by a section and apply
naturality to that section.

Lean:

```text
P0EFTJanusFiniteJetEquivariance
  .operator_natural_iff_evaluator_equivariant
```

### Step 3 — Uniqueness

If two evaluators represent the same operator and every finite jet is
holonomically realizable, evaluate both on a section realizing a chosen jet.
They agree on every jet.

Lean:

```text
P0EFTJanusFiniteJetEquivariance
  .evaluator_unique_of_surjective_jet
  .exists_unique_equivariant_evaluator
```

### Step 4 — Local-to-uniform order

A finite collection of local orders has a common upper bound.  Evaluators at
lower order can be lifted to that order by jet truncation.

Lean:

```text
P0EFTJanusFiniteOrderUniformization
  .lifted_evaluator_factorization
  .finite_local_orders_have_common_bound
```

But local finite order on infinitely many components need not admit a uniform
bound:

```text
local order on component n = n.
```

Lean:

```text
componentwise_finite_order_has_no_uniform_bound
```

Thus compactness of the throat base is not, by itself, enough if the operator
order varies over an unbounded configuration or jet region.

### Step 5 — Scalar invariants versus covariants

For a trivial scalar target, equivariance reduces to invariance:

```text
Phi(g.j) = Phi(j).
```

For tensor, spinor or ghost targets, the correct condition is instead

```text
Phi(g.j) = g.Phi(j).
```

Calling all such maps "invariants" loses the target representation and is
mathematically incorrect.

### Step 6 — Ellipticity is independent

The zero operator is natural under every symmetry, but its symbol is not
injective.  Therefore naturality and finite-jet classification do not imply
ellipticity.

Lean:

```text
P0EFTJanusCorrectedJetUniversality
  .naturality_does_not_imply_symbol_injectivity
```

## Exact theorem currently formalized

Given a finite-jet presentation with:

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

Head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

## What remains to specialize to Janus

1. Define the actual category of decorated Janus SpinC immersions.
2. Construct the adapted finite jet group, including:
   - tangent Spin(3) or O(3) data;
   - the normal orientation character and its Z4 lift;
   - the primitive U(1) twist;
   - PT and BRST/Grassmann grading.
3. Prove the chosen natural source and target bundles have finite order.
4. Verify regularity and sheaf locality for each candidate operator.
5. Import or formalize the Peetre--Slovak theorem for the relevant smooth
   bundle category.
6. Prove holonomic realization for the required jet fibers.
7. Specify a bounded neighborhood of the Janus background if one global order
   is required.
8. Classify smooth equivariant maps on those finite jet fibers.
9. Add a polynomial dependence hypothesis only for the polynomial subclass.
10. Impose ellipticity, Helmholtz, anomaly and renormalization constraints
    separately.

## Evidence matrix

| Claim | Status |
| --- | --- |
| finite-jet naturality/equivariance equivalence | proved in Lean |
| evaluator uniqueness under jet surjectivity | proved in Lean |
| finite local orders admit a common finite bound | proved in Lean |
| local finite order need not have a global bound | proved in Lean |
| smooth natural does not imply polynomial | explicit order-zero counterexample; finite-difference proof in Lean |
| Peetre--Slovak for the actual Janus category | analytic theorem interface; specialization open |
| actual adapted SpinC jet group | open |
| full smooth equivariant-map classification | open |
| polynomial invariant classification | conditional on polynomial dependence |
| ellipticity of selected operators | independent open theorem |

## Final statement

The proof program does not support the original unrestricted polynomial
conjecture.  It supports a sharper and standard-compatible statement:

```text
regular + local + natural
  -> locally finite-jet
  -> unique smooth equivariant evaluator,
```

with global order, polynomiality, ellipticity and field-content selection
explicitly separated as additional hypotheses or theorems.

## Primary references

- J. Navarro and J. B. Sancho, *Peetre--Slovak's theorem revisited*.
- I. Kolar, P. W. Michor and J. Slovak, *Natural Operations in Differential
  Geometry*.
- J. Navarro and J. B. Sancho, *Natural operations on differential forms*.
