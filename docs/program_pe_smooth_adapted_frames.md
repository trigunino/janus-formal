# Program P.E-S5 — Smooth projectors and local adapted orthonormal frames

> Pointwise second fundamental form: [`program_pe_second_fundamental_form_jet.md`](program_pe_second_fundamental_form_jet.md)  
> Low-order quotient: [`program_pe_low_order_structured_background.md`](program_pe_low_order_structured_background.md)  
> Structured-jet roadmap: [`program_pe_structured_jet_reduction.md`](program_pe_structured_jet_reduction.md)

## Objective

The preceding stages proved the tangent/normal splitting, the identity `B = II`
and residual `O(T) x O(N)` equivariance at one point. Program P.E-S5 asks for a
local smooth version:

```text
smooth tangent frame
  -> smooth tangent and normal projectors
  -> smooth local normal orthonormal frame
  -> smooth local adapted orthonormal frame.
```

The current implementation works in a finite-dimensional local coordinate
model over a normed base space. Packaging the result as actual sections and
endomorphisms of manifold vector bundles remains a separate interface step.

# S5.1 — Smooth tangent and normal projectors

## 1. Tangent projector

Given a finite smooth orthonormal tangent frame

```text
e_i : Base -> Ambient,
```

define

```text
P_T(x,v) = sum_i <e_i(x),v> e_i(x).
```

The complementary projector is

```text
P_N(x,v) = v - P_T(x,v).
```

Lean module:

```text
P0EFTJanusSmoothProjectorField.lean
```

## 2. Joint smoothness

### Theorem S5.1.1 — proved in Lean

```text
tangentProjector_contDiff
normalProjector_contDiff
```

prove that

```text
(x,v) |-> P_T(x,v),
(x,v) |-> P_N(x,v)
```

are `C-infinity` jointly in the base point and vector argument whenever every
frame vector `e_i` is smooth.

Consequently:

```text
tangentProjector_apply_contDiff
normalProjector_apply_contDiff
```

prove that projecting any smooth vector field produces a smooth vector field.

## 3. Projector identities

For a pointwise orthonormal tangent frame, Lean proves:

```text
tangentProjector_frame
normalProjector_frame
inner_tangent_normalProjector_eq_zero
tangent_add_normal_projector
tangentProjector_idempotent
normalProjector_idempotent.
```

Thus the explicit finite sum is genuinely the tangent orthogonal projector, and
`P_N` is its complementary normal projector.

## 4. Projected normal seeds

Given smooth ambient seed fields

```text
s_k : Base -> Ambient,
```

define

```text
n'_k(x) = P_N(x,s_k(x)).
```

Lean proves:

```text
projectedNormalSeed_contDiff.
```

Hence all projected seeds are smooth.

## 5. Openness of independence

Linear independence of a finite family in a finite-dimensional normed space is
an open condition. Combining this Mathlib theorem with smoothness of the
projected seeds gives:

```text
eventually_projectedNormalSeed_linearIndependent.
```

If the projected normal seeds are independent at one base point, they remain
independent on a neighborhood of that point.

This closes the coordinate core of S5.1.

# S5.2 — Smooth adapted orthonormal frame

Lean module:

```text
P0EFTJanusSmoothAdaptedFrame.lean
```

## 6. Smooth Gram--Schmidt theorem

Let

```text
f_k : Base -> Ambient
```

be a finite smooth family. On a set `U` where the family is pointwise linearly
independent, Lean proves:

```text
varyingGramSchmidt_contDiffOn
varyingGramSchmidtNormed_contDiffOn.
```

The proof follows the recursive Gram--Schmidt formula. At each step:

- all earlier Gram--Schmidt vectors are smooth by well-founded induction;
- inner products and norm squares are smooth;
- independence implies the norm denominators are nonzero;
- division and finite sums therefore preserve smoothness.

This is an actual smoothness proof, not an interface assumption.

The pointwise normalized family is orthonormal:

```text
varyingGramSchmidtNormed_orthonormal.
```

## 7. Open normal independence locus

For projected normal seeds define

```text
U_N = {x | the family P_N(x,s_k(x)) is linearly independent}.
```

Lean proves:

```text
normalIndependenceLocus_isOpen.
```

The normalized Gram--Schmidt normal frame

```text
n_k(x) = GramSchmidtNormed(P_N(x,s_j(x)))_k
```

satisfies:

```text
smoothNormalFrame_contDiffOn
smoothNormalFrame_orthonormal.
```

## 8. Tangent-normal orthogonality

Lean proves that every Gram--Schmidt normal vector remains in the span of the
projected normal seeds:

```text
smoothNormalFrame_mem_projected_span.
```

Since each projected seed is orthogonal to the tangent frame, the entire normal
Gram--Schmidt span is orthogonal to the tangent frame:

```text
tangent_inner_smoothNormalFrame_eq_zero.
```

## 9. Combined adapted frame

The tangent and normal families are combined using the disjoint index type

```text
Sum tangentIndex normalIndex.
```

Lean proves:

```text
combinedAdaptedFrame_orthonormal.
```

If the number of tangent and normal vectors equals the ambient dimension, the
combined family spans the ambient space:

```text
combinedAdaptedFrame_span_eq_top.
```

Therefore it is an orthonormal basis at every point of the independence locus.

## 10. Local existence theorem

### Theorem S5.2.1 — proved in Lean

```text
exists_open_smooth_adapted_frame
```

Assume:

1. a finite smooth pointwise orthonormal tangent frame;
2. finitely many smooth ambient seed fields;
3. independence of their normal projections at a base point;
4. tangent-rank plus normal-rank equals the ambient dimension.

Then there exists an open neighborhood of the base point on which:

- the normal frame obtained by projected Gram--Schmidt is smooth;
- the combined tangent/normal family is orthonormal;
- the combined family spans the ambient space.

This is the requested local adapted-frame theorem in coordinates.

# Exact evidence boundary

## Demonstrated in Lean

- explicit smooth tangent projector;
- explicit smooth normal projector;
- all projector identities;
- smooth projected normal seeds;
- openness and local persistence of projected-seed independence;
- smoothness of finite Gram--Schmidt on the independence locus;
- smoothness and orthonormality of the normal frame;
- tangent-normal orthogonality;
- spanning of the ambient space under the dimension identity;
- existence of an open neighborhood carrying a smooth adapted orthonormal
  frame.

## Still open as manifold packaging

- derive the tangent frame from an actual immersion chart and source tangent
  local frame;
- obtain the ambient seed frame from a compatible ambient tangent-bundle
  trivialization;
- express the coordinate construction as `IsLocalFrameOn` sections of the
  pulled-back ambient tangent bundle;
- prove compatibility under overlap changes of bundle trivialization;
- construct the oriented reduction and SpinC lift.

Mathlib already supplies smooth local frames from vector-bundle
trivializations. It does not yet provide the planned general orthonormal-frame
bundle API, so the repository proves the required finite-dimensional
Gram--Schmidt smoothness directly.

# Scientific consequence

The chain is now:

```text
pointwise tangent/normal splitting
  -> B = II
  -> smooth P_T and P_N
  -> open normal independence locus
  -> smooth normal Gram--Schmidt frame
  -> smooth adapted orthonormal frame.
```

The next lock is S5.3:

> Compute the two-jet transformation under this varying adapted frame and prove
> that the derivative-of-frame terms reproduce exactly the source and ambient
> connection corrections already formalized pointwise.

After S5.3, the remaining local geometric step is the oriented/SpinC lift and
determinant-line compatibility.

# Lean correspondence

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusSmoothProjectorField.lean
  P0EFTJanusSmoothAdaptedFrame.lean
```

Validation target:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```
