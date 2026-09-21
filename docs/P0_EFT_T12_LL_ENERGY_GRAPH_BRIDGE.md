# T12: positive LL energy / closed-graph bridge and weak shifts

Date: 2026-09-17.
Base: `dev-branch` at `53a70985e284e73952883ec648fa5056cea07598`.
Mathlib source API reviewed at the repository's pinned revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (v4.31.0).

## Validation and scope

This is a partial analytic support block, **not closure of terminal T12**.
The user reported a successful focused LL build (9,158 jobs), then a successful
local facade build on 2026-09-19 (11,737 jobs), following the fixes through
`5a4baef59a44995792144aee9cae8959aa372bbc`. This is user-reported validation of
the user's checkout, not an independently reproduced build or a CI result.

A focused local build through
`P0EFTJanusProgramPT12LLStrongJacobiShiftedInverseOnRange4D` passed all
9,516 jobs on 2026-09-21. No GitHub Actions or other CI/CD operation was run.
No workflow, build setting, or dependency configuration was changed.

The LL specialization uses `GlobalAnalysisData`, hence the existing strict
positivity assumption on `llMeasure`. Its shifted weak solutions cover
`0 <= shift`. No new claim for arbitrary-sign backgrounds is made here.
The operator `C` below is exactly `llJacobiClosedPMap` on the **reduced field
block**, not the full LL Jacobi and not a newly substituted realization.

## Added modules

All Lean paths have prefix
`JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple/Gates/`.

- `P0EFTJanusProgramPT12HilbertEnergyShift4D.lean`
  constructs the coercive form and bounded unique weak solution using
  Mathlib's Lax--Milgram equivalence.
- `P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D.lean`
  extends the same-action smooth pairing to the energy completion and then
  to the existing closed L2 graph. It constructs a graph-norm-continuous
  energy lift and the exact factorization of graph inclusion through H1.
- `P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D.lean`
  specializes weak solutions to LL, relates them to the existing closed
  shift, and identifies the precise remaining domain-membership obligation.
- `P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakAdjoint4D.lean`
  proves that every nonnegative shifted weak solution lies in the Hilbert
  adjoint domain and computes its adjoint value as `f - shift • u`.
- `P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D.lean`
  defines the inverse-response realization on `range (I I*)`, proves it dense,
  self-adjoint, closed, bijective and Fredholm with compact inverse, and proves
  the nonnegative shifted weak solutions are genuine right inverses there.
- `P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D.lean`
  constructs the injective dense finite-support core of the maximal spectral
  block and proves its exact diagonal action and pairing.
- `P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D.lean`
  combines that maximal spectral operator with the reduced LL Friedrichs
  realization into a dense self-adjoint closed Fredholm product.
- `P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D.lean`
  gives this product an injective dense finite-spectral/smooth-LL core with
  exact action and pairing formulas.
- `P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D.lean`
  embeds finite primitive SpinC matter modes with zero D9 component and proves
  that the product pairing is exactly the matter graph form plus the LL Hessian.
- `P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D.lean`
  quotients the full smooth LL core by its auxiliary/measure directions,
  identifies the quotient with the reduced smooth field, and embeds it densely
  and injectively into the canonical LL `L2` space.

The existing `P0EFTJanusProgramPT12LLStrongJacobiShiftedInverseOnRange4D.lean`
imports the weak-solution and adjoint modules. Its previous proof is unchanged.
The existing facade already imports this inverse-on-range module, so the new
support block is reached transitively without rewriting the large facade.

## Domain bridge actually implemented

Let `V` be the canonical positive LL energy completion, `H` the genuine
throat L2 space, and `I : V ->L H` its existing injective dense embedding.
The energy adjoint is denoted `I*`.

The smooth same-action identity gives

```
I* (C0 u) = u                   in V, for smooth u.
```

The condition `I (I* y) = x` is closed in `H x H`. Passing to the existing
smooth Jacobi graph closure therefore gives the exact identity

```
I (I* (C x)) = x                for x in D(C).
```

Thus `D(C)` has a canonical energy lift `x |-> I* (C x)`.
Continuity is stated on `C.graph` with its product/subspace (graph) norm,
NOT on `D(C)` equipped only with the L2 subspace norm.

This establishes `D(C) -> V`. It does not establish the converse domain
identification with the energy realization.

## Shifted weak solution and strong solvability

For every `shift >= 0`, the form

```
b_shift(u,v) = <u,v>_V + shift * <I u,I v>_H
```

is coercive in `V`. The new bounded map `W_shift : H ->L V` satisfies

```
b_shift(W_shift f,v) = <f,I v>_H  for all f in H and v in V.
```

It is the unique energy solution. Its actual L2 value is
`R_shift = I o W_shift`. At zero shift, `W_0 = I*`.
The graph bridge and uniqueness imply

```
R_shift ((C + shift) x) = x      for x in D(C).
```

The L2 solution map is injective, using the already established faithfulness
and density of `I`. Consequently a weak solution is a strong solution of the
SAME closed operator as soon as `R_shift f` belongs to `D(C)`.
The exact remaining obligation is recorded as

```
Surjective (C + shift)
  <-> for every f in H, R_shift f belongs to D(C).
```

This is an equivalence that isolates the missing regularity/operator-core
proof. It is NOT an unconditional surjectivity theorem for `C + shift`.
Closedness and symmetry alone do not supply that proof.

## Compactness: remaining concrete theorem and consequences

The concrete Rellich assertion

```
IsCompactOperator (canonicalLLH1ToFluxL2 period hPeriod analysis)
```

has NOT been proved in this block. It remains an explicit premise named
`hRellich`, never an axiom or an implicit field of a purported final
certificate. Given this premise, the new factorization proves compactness
of the closed graph inclusion into L2, and compactness of `R_shift` follows
by composition with the bounded energy solution map.

The next geometric proof must establish compactness for the actual throat,
actual energy norm, and actual canonical volume, rather than replacing them
with an unrelated compact spectral model. The next operator-domain proof
must place all these weak solutions in the closure of the SAME smooth
Jacobi graph. A weak extension without that identification is insufficient.

The previously proved infinite kernel of the full stationary LL Jacobi is
unchanged. No full-operator Fredholm, compact resolvent, heat-trace class,
or terminal T12 certificate is asserted by these additions.

## Suggested local compilation target

From the repository root, after pulling `dev-branch`:

```powershell
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D
```

This target imports both other new modules. Build the facade separately
after the focused target succeeds. Neither command was run by the author
of this support block.

## 2026-09-19: concrete frame-H1 and cutoff support block

Development base: `dev-branch` at
`5a4baef59a44995792144aee9cae8959aa372bbc`.
This is a further partial Rellich step, NOT the completed LL Rellich theorem.

Four modules are added:

- `P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D.lean`
- `P0EFTJanusProgramPT12LLCanonicalFrameH1Completion4D.lean`
- `P0EFTJanusProgramPT12LLCanonicalFiniteFiberCompactness4D.lean`
- `P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D.lean`

The inverse-on-range integration module imports the completion and finite-fiber
modules; those import the control and throat Rellich modules. The existing
facade therefore reaches all four transitively.

### Concrete estimates, not compactness premises

For the existing canonical frame `F` and canonical throat volume `mu`, define

```
S(u) = integral (norm(u)^2 + sum_i norm(D_F_i u)^2) dmu.
```

The scripts derive `S(u) <= K * norm(u)_V^2` on the actual smooth LL energy
core from the previously established Garding and positive L2 bounds. `K` is
background-dependent and independent of `u`. Positivity is exactly the
existing strict positivity of `llMeasure` carried by `GlobalAnalysisData`.

For each fixed smooth scalar cutoff `chi`, the scripts establish the genuine
manifold Leibniz rule, support and topological-support containment, and

```
S(chi * u) <= B_chi * S(u) <= B_chi * K * norm(u)_V^2.
```

The cutoff coefficient bound comes from continuity and compactness of the
actual throat. These estimates take no Rellich, chartwise compactness,
coordinate norm-equivalence, or operator-regularity premise.

### Completed first derivatives and joint approximation

Each `D_F_i u` is first constructed as its genuine canonical-volume L2 class.
The energy estimate makes the smooth map bounded, so it extends continuously
to the SAME LL energy completion. The combined value/derivative map

```
J : V ->L L2 x (Fin F.count -> L2)
J(u) = (I u, (D_i u)_i)
```

is injective, agrees exactly with the smooth first-jet map, and lands in the
closure of that smooth first-jet graph. For every `u : V` and `epsilon > 0`,
the scripts give a smooth `w` with

```
norm(w)_V <= norm(u)_V + 1,
norm(J_smooth(w) - J(u)) < epsilon.
```

This simultaneously controls the value and every first-derivative L2
coordinate. It is NOT second-order Jacobi graph approximation and does NOT
prove that an arbitrary energy vector or weak solution belongs to `D(C)`.

### Finite-fiber compactness reduction

The LL flux fiber is exactly `EuclideanSpace Real (Fin 4)`. Pointwise
coordinate projection and insertion on `L2` reconstruct the identity as a
finite sum. Hence the canonical vector-valued energy embedding is compact iff
each of its four scalar coordinate embeddings is compact. No compactness
premise is introduced.

The pre-existing finite smooth partition of unity on the actual throat is now
publicly reusable. Each closed partition support is compact and lies in its
selected chart. Transport to `EuclideanSpace Real (Fin 3)` gives, on every
patch, the unconditional compact supported Euclidean `H1 -> L2` inclusion.
The actual compact patch is now homeomorphic to that Hilbert support through
the quotient chart. Canonical throat volume is pulled back to the patch and
pushed forward exactly to coordinates; the coordinate measure is finite and
carried by the Rellich support. A continuous positive coordinate-density
certificate now yields the required finite two-sided Lebesgue comparison.
The finite throat generator indices, model basis, and local vectors are also
public, and every local vector is identified with the derivative of the
inverse preferred chart. The Lipschitz image-volume kernel now works in any
finite rank. Its rank-three specialization now proves the two-sided measured
stereographic comparison on every compact `ThroatCoverCoordinates` support.

The weighted finite partition frame is now compared exactly with the
canonical LL frame. Its smooth reconstruction coefficients have a uniform
bound on the compact throat, giving a single constant that controls the full
finite-frame derivative energy by the canonical derivative energy.

For each closed patch, a smooth plateau now extends every unweighted local
chart vector to a global smooth tangent section. Canonical-frame
reconstruction and compact coefficient bounds therefore control all inverse
chart directional derivatives on that patch by the canonical LL energy.

The open fundamental throat strip is now an injective measured
parametrization away from its null seam. Rank-three stereographic product
charts, together with time-shifted measure-preserving copies, form a finite
measured cover of every compact throat subset. Every closed partition patch
now has a finite compact refinement by these charts. Smooth transition maps
on the compact overlaps give uniform Lipschitz constants, and the finite sum
proves an unconditional two-sided comparison between canonical volume and
Lebesgue measure on each patch.

### What is still missing

The repository's Euclidean fixed-support Rellich theorem is available in
`RellichKondrachov/Analysis/FunctionalSpaces/Sobolev/Euclidean/Rellich.lean`.
It is not silently assumed to apply to the throat. The local compact operators
and finite cutoffs are now constructed. Exact bounded `L2` transports among
the quotient patch, canonical coordinates, and ambient Lebesgue space are
available, as is the derivative of the inverse Hilbert chart on its model
basis. Each partition-localized LL component now has a smooth compactly
supported Euclidean representative with its exact rank-three gradient. The
smooth supported `H1` localizer and its uniform value-and-gradient bounds are
now constructed from an explicit local-jet `L2` estimate and the cutoff frame-H1
bound. Its bounded extension to the completed energy space and agreement on the
dense smooth core are also constructed. The Euclidean `L2` return transport and
exact finite-patch reconstruction of every smooth scalar coordinate are now
proved. Completed-space factorization, compactness of every scalar coordinate,
and Rellich compactness of the full four-component LL embedding are proved.

Thus the previous `hRellich` premise is now discharged geometrically. The
closed-graph embedding and every nonnegative shifted weak solution operator now
have unconditional compactness corollaries in a downstream non-cyclic module.
The weak solution is now in the adjoint domain with the expected shifted
residual. The canonical Friedrichs realization extends the original closed
Jacobi graph and has compact inverse; all its nonnegative shifts are bijective
and their ambient resolvents are compact. The squared real shifts now form an
explicit spectral--LL family on one dense common domain. Its zero fibre is the
unshifted global Friedrichs product, every fibre is Fredholm under the existing
D9 hypothesis, every fibre is self-adjoint and closed, and the compact LL
resolvents vary continuously in operator norm. Because the shifted LL block is
bijective, the full family's kernel and range are exactly the lifted spectral
kernel and range; its kernel and cokernel dimensions are constant in the
parameter. The preferred actual operator at zero is also decomposed exactly on
the minimal matter--LL slice into this
Friedrichs pairing plus the explicit local seven-block residual. That residual
is now both expanded into its seven physical Hessians and identified with the
canonical stable-physical Riesz pairing. Consequently, agreement with the zero
Friedrichs fibre on this slice is equivalent exactly to vanishing of that Riesz
pairing.
Equality with the original closed Jacobi domain remains precisely the
essential-self-adjointness/graph-regularity step. The finite D9 graph,
primitive SpinC matter graph, and reduced LL smooth core now have an exact
separated pairing. The matter--LL slice survives the minimal physical kernel
quotient and embeds injectively in the local chart. At the same-action bridge
base point, that chart's local matter--LL Hessian is exactly the Friedrichs
product pairing. Embedding D9 in a compatible gauge-fixed chart, identifying
the remaining local seven-block residual, and terminal T12 remain. No new
axioms or proof placeholders are introduced.

### Focused build for these additions

```powershell
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiShiftedInverseOnRange4D
```

This focused target passed locally in a one-thread, 16 GB capped Lean run.
Equality with the original strong domain and terminal T12 remain separate.
