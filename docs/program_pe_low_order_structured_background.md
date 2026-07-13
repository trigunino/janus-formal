# Program P.E-S2 — First combined low-order structured background quotient

> Structured-jet roadmap: [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md)  
> Categorical theorem: [`program_pe_categorical_jet_equivalence.md`](program_pe_categorical_jet_equivalence.md)  
> Pairing modules: [`program_pd_global_pairing_modules.md`](program_pd_global_pairing_modules.md)

## Objective

The structured-jet program needs more than an abstract action groupoid. It needs
an explicit quotient calculation showing which Taylor coefficients are genuine
geometric data and which are coordinate or gauge directions.

The first nontrivial target is the low-order local background

```text
normalized immersion 2-jet
  + abelian connection 1-jet.
```

The expected quotient data are

```text
B  = normal quadratic immersion tensor,
F  = abelian curvature two-form.
```

This document records the exact theorem now formalized and separates it from the
remaining smooth SpinC geometry.

## 1. Concrete second-order chain rule

### Definition

A formal map two-jet is represented by

```text
(A,Q),
A : V -> W,
Q : V x V -> W.
```

A source two-jet is represented by

```text
(L,C),
L : V -> V,
C : V x V -> V.
```

The second-order precomposition law is

```text
(A,Q) o (L,C)
  = (A o L,
     (x,y) |-> Q(Lx,Ly) + A(C(x,y))).
```

This is the Taylor-coefficient form of the second derivative chain rule.

Lean:

```text
P0EFTJanusConcreteSecondJetChainRule.precomposeTwoJet
```

### Normalized immersion

After first-order normalization, the derivative is encoded as

```text
A(x) = (x,0) in V x N.
```

Write the quadratic coefficient as

```text
Q(x,y) = (Q_tangent(x,y), Q_normal(x,y)).
```

For an identity-linear quadratic source change `(id,C)`, the formal chain rule
becomes exactly

```text
Q_tangent -> Q_tangent + C,
Q_normal  -> Q_normal.
```

### Theorem S2.1 — proved in Lean

```text
quadratic_precomposition_formula
```

proves that the concrete two-jet precomposition formula agrees with the earlier
abstract additive source action.

### Theorem S2.2 — proved in Lean

```text
concrete_change_reaches_normal_form
```

uses the explicit choice

```text
C = -Q_tangent
```

and reaches the unique zero-tangential representative.

### Theorem S2.3 — proved in Lean

```text
concrete_equivalent_iff_normal_eq
```

states:

```text
two normalized immersion two-jets differ by quadratic precomposition
  iff
their normal quadratic tensors agree.
```

This is now a theorem about the declared second-order chain-rule model, not only
about a pre-split additive orbit relation.

## 2. Residual tangent/normal frame action

Let `G_T` act on the tangent model `V` and let `G_N` act on the normal model `N`.
The residual product action on a normal-valued two-tensor is

```text
((g_T,g_N) . B)(x,y)
  = g_N . B(g_T^(-1) x, g_T^(-1) y).
```

Lean:

```text
actOnNormalTensor
actOnNormalTensor_one
actOnNormalTensor_mul
normal_tensor_action_preserves_symmetry
```

The full split quadratic jet also carries a residual action. Under a distributive
tangent action, the repository proves the normalization compatibility

```text
g . (Q + C)
  = (g . Q) + (g . C),
```

in the exact form

```text
residual_action_commutes_with_quadratic_source_change.
```

It also proves that the zero-tangential slice is stable:

```text
normal_form_is_residual_equivariant.
```

Thus the residual frame action descends to the quotient represented by `B`.

## 3. Concrete abelian connection one-jets

### Definition

A local abelian connection one-jet is represented by

```text
A_i(0),
D_ij = partial_i A_j(0).
```

A genuine scalar gauge two-jet is represented by

```text
g_i = partial_i chi(0),
H_ij = partial_i partial_j chi(0),
H_ij = H_ji.
```

The gauge action is

```text
A_i -> A_i + g_i,
D_ij -> D_ij + H_ij.
```

The curvature is

```text
F_ij = D_ij - D_ji.
```

Lean:

```text
P0EFTJanusConcreteAbelianConnectionJet.applyGauge
P0EFTJanusConcreteAbelianConnectionJet.curvature
```

### Theorem S2.4 — proved in Lean

```text
curvature_applyGauge
```

proves that a symmetric gauge Hessian leaves curvature unchanged.

### Theorem S2.5 — proved in Lean

The explicit gauge

```text
g = -A(0),
H = -Sym(D)
```

reaches

```text
A(0) = 0,
D = Alt(D) = F/2.
```

The relevant results are

```text
concrete_normalizing_gauge_reaches_curvature_form
curvature_concrete_normal_form.
```

### Theorem S2.6 — proved in Lean

```text
concrete_gauge_equivalent_iff_curvature_eq
```

states:

```text
two concrete abelian connection one-jets are gauge equivalent
  iff
their curvature two-forms agree.
```

The converse is constructive. If `F_1=F_2`, the derivative difference

```text
D_2-D_1
```

is symmetric and is used as the Hessian of the gauge two-jet; the connection
value difference is used as its gradient.

This is stronger than the previous decomposed model because the
symmetric/alternating split is derived from the concrete derivative formula.
The compatibility theorem

```text
decomposition_commutes_with_gauge
```

then maps the concrete calculation back to the abstract normal-form gate.

## 4. First combined quotient

### Unreduced background

The combined low-order structured jet is

```text
J_low = (immersion two-jet, abelian connection one-jet).
```

### Reduced background

The reduced data are

```text
R_low = (B,F),
```

where `F` carries the alternating identity

```text
F(y,x) = -F(x,y).
```

Lean:

```text
P0EFTJanusLowOrderStructuredBackground.LowOrderStructuredJet
P0EFTJanusLowOrderStructuredBackground.LowOrderReducedData
P0EFTJanusLowOrderStructuredBackground.reduceLowOrderJet
```

### Canonical section

The quotient map has the canonical representative

```text
Q_tangent = 0,
Q_normal  = B,
A(0)      = 0,
D         = F/2.
```

The repository proves

```text
reduce_reducedSlice : reduceLowOrderJet (reducedSlice data) = data.
```

### Theorem S2.7 — proved in Lean

```text
combined_equivalent_iff_reduced_eq
```

states:

```text
J_1 and J_2 are related by a quadratic source change and an abelian gauge two-jet
  iff
(B_1,F_1) = (B_2,F_2).
```

Thus the fibers of the reduction map are exactly the combined low-order orbit
classes.

### Theorem S2.8 — proved in Lean

```text
combined_invariant_iff_factors_through_reduced
combined_invariant_has_unique_reduction
```

prove the universal property:

> A function on the unreduced low-order background is invariant under the
> source/gauge orbit directions if and only if it factors through `(B,F)`. The
> reduced function is unique.

This is the first exact nontrivial quotient theorem of the structured-jet
program.

## 5. Residual action on `(B,F)`

The quotient data carry the residual action

```text
(g_T,g_N) . (B,F)
  = ((g_T,g_N) . B,
     pullback(g_T,F)).
```

The Lean module proves identity and multiplication laws:

```text
actOnReducedData_one
actOnReducedData_mul.
```

The alternating curvature identity is preserved by construction.

Therefore the first low-order structured problem has the exact staged form

```text
unreduced Taylor coefficients
  / (quadratic source changes x gauge two-jets)
  = (B,F)
  with residual tangent/normal frame action.
```

## 6. Executable audit

The rational Python audit now checks:

- removal of the tangential quadratic immersion coefficient;
- preservation of the normal quadratic coefficient;
- removal of connection value and symmetric derivative;
- preservation of curvature;
- constructive recovery of the exact gauge between two equal-curvature jets;
- rejection when the curvatures differ.

Run:

```text
python scripts/audit_janus_low_order_jet_normal_forms.py
pytest -q tests/test_janus_low_order_jet_normal_forms.py
```

## 7. Exact evidence boundary

### Demonstrated

- the second-order precomposition formula in the formal Taylor-coefficient model;
- exact classification of normalized immersion quadratic orbits by the normal
  tensor;
- generic residual `G_T x G_N` transformation law on that tensor;
- exact concrete abelian connection one-jet classification by curvature;
- exact combined quotient by `(B,F)`;
- unique factorization of invariant observables through `(B,F)`;
- residual action on the reduced data.

### Not yet demonstrated

- finite-dimensional vector-space and smooth-manifold realizations of all types;
- first-order normalization of an arbitrary immersion derivative by adapted
  orthonormal frames;
- identification of the normal quadratic coefficient with the geometric second
  fundamental form defined using the ambient Levi-Civita connection;
- construction of the actual `O(p) x O(q-p)` or SpinC-compatible residual group;
- local trivialization and jet group of the determinant-line connection;
- a differentiable structured-jet groupoid;
- global SpinC, square-root and `Z4` sectors;
- higher covariant derivatives and Gauss--Codazzi--Ricci--Bianchi constraints.

The current theorems are exact but algebraic. They do not yet prove the full
smooth jet-isomorphism theorem for decorated SpinC immersions.

## 8. Relation to the classical jet-isomorphism strategy

The classical metric jet-isomorphism theorem reconstructs normal-coordinate
metric jets from curvature jets and their covariant derivatives. The present
result is the extrinsic/gauge low-order analogue one would expect at the first
nontrivial order:

```text
immersion two-jet modulo source normalization -> B,
abelian connection one-jet modulo gauge       -> F.
```

A full Janus theorem must combine this with ambient metric jets, normal
connections, SpinC connections and formal integrability identities.

## 9. Next theorem queue

1. Instantiate `Tangent = Fin p -> R` and `Normal = Fin r -> R` and replace raw
   functions by linear and symmetric-bilinear maps.
2. Construct the residual group explicitly as

   ```text
   O(p) x O(r)
   ```

   or the precise oriented/SpinC fiber product required by the category.
3. Prove first-order normalization of an injective immersion derivative using
   adapted orthonormal frames.
4. Identify `B` with the geometric second fundamental form and prove its
   coordinate/frame transformation law.
5. Instantiate the connection theorem for a local determinant-line `U(1)`
   connection and its gauge-jet group.
6. Construct the finite-dimensional smooth reduced base containing `(B,F)` and
   its residual action groupoid.
7. Classify scalar invariants and pairing covariants of this compact residual
   representation.
8. Extend to one covariant derivative and determine the first
   Gauss--Codazzi--Ricci/Bianchi integrability constraints.

## 10. Lean correspondence

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusConcreteSecondJetChainRule.lean
  P0EFTJanusConcreteAbelianConnectionJet.lean
  P0EFTJanusLowOrderStructuredBackground.lean
```

These modules are imported by the focused
`FundamentalGeometryPEJetUniversality` head, so the principal P.E workflow must
compile them before the results are promoted.
