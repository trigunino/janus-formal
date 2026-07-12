# Program P.E — Lemma 2: Naturality implies finite-jet equivariance

## Status

This document records the precise statement used by Program P.E-J. It separates:

- the analytic finite-order input supplied by Peetre--Slovak;
- the formal naturality/equivariance argument proved in Lean;
- the additional hypotheses needed for the converse and uniqueness;
- the Janus-specific specialization that remains open.

## Setting

Let `E -> M` and `F -> M` be natural or gauge-natural bundles. Let

```text
D : Gamma(E) -> Gamma(F)
```

be an operator which has already been shown to factor through finite jets:

```text
D(s)(x) = delta(j_x^r s),
```

for a smooth bundle map

```text
delta : J^r E -> F.
```

The finite-order factorization is the conclusion of Lemma 1 under locality and
regularity hypotheses. Lemma 2 does not reprove Peetre--Slovak.

## Intrinsic theorem

Assume `D` is natural with respect to every admissible local symmetry `phi`:

```text
D(phi . s) = phi . D(s).
```

Jet prolongation satisfies

```text
j^r(phi . s) = J^rE(phi) . j^r(s).
```

Therefore, for every realizable jet,

```text
delta(J^rE(phi)(j_x^r s))
  = F(phi)(delta(j_x^r s)).
```

If every jet in the relevant fiber is holonomically realizable, then

```text
delta o J^rE(phi) = F(phi) o delta
```

on the full jet fiber. Thus the evaluator is equivariant.

The realizability hypothesis is needed when the conclusion is stated for every
abstract jet rather than only jets arising from sections.

## Fiber-model formulation

Choose an adapted local frame at a base point. The source and target fibers
become model spaces

```text
A_r = (J^r E)_0,
B   = F_0.
```

A sufficiently high jet of an admissible coordinate/gauge transformation acts
on both spaces. Denote the resulting adapted jet group by `G^q`.

The evaluator becomes

```text
delta_0 : A_r -> B
```

and naturality gives

```text
delta_0(g . a) = g . delta_0(a).
```

### Important order qualification

The symmetry order `q` is not automatically equal to the differential order
`r` of the operator. It must be high enough to determine:

- the action on the source natural bundle;
- the prolonged action on `J^r E`;
- the action on the target natural bundle.

Hence the correct statement is "for a sufficiently high adapted jet group
`G^q`", unless the natural orders of the bundles have already been fixed and an
explicit formula for `q` has been proved.

## Converse

Suppose a smooth evaluator

```text
delta_0 : A_r -> B
```

is `G^q`-equivariant. Transport it from the model fiber to every point using an
adapted local frame. Equivariance makes the resulting value independent of the
chosen frame. Defining

```text
D_delta(s)(x) = delta(j_x^r s)
```

then gives a natural differential operator of order at most `r`.

Thus, after fixing the natural source/target bundles, their symmetry actions and
the required regularity:

```text
natural finite-order operators
  <->
smooth equivariant finite-jet evaluators.
```

## Uniqueness

If two evaluators define the same operator and every finite jet is realizable by
a section, evaluate both on a section realizing an arbitrary chosen jet. The
evaluators agree on every jet.

This is the role of the surjective jet-realization hypothesis in the Lean
formalization.

## Scalar targets versus nontrivial targets

For a trivial scalar target, equivariance reduces to invariance:

```text
delta_0(g . a) = delta_0(a).
```

For tensor, spinor, ghost or other nontrivial targets, the target action must be
retained:

```text
delta_0(g . a) = rho_B(g) delta_0(a).
```

Such maps are covariants, not scalar invariants.

## What the lemma does not prove

The lemma does not imply that the evaluator is:

- polynomial;
- rational;
- unique without jet realizability;
- globally of one uniform finite order on an unbounded configuration space;
- elliptic;
- generated only by curvature, torsion and second fundamental form;
- physically selected.

These are separate results or hypotheses.

## Janus specialization

For decorated Janus SpinC immersions, the adapted symmetry must eventually
include compatible pieces for:

- tangent coordinate/frame transformations;
- ambient coordinate/frame transformations;
- SpinC and `U(1)` gauge transformations;
- the normal orientation character and its `Z4` lift;
- `PT`;
- BRST/ghost grading when the target contains gauge-fixed fields.

The repository has not yet constructed this complete adapted jet group. The
abstract naturality/equivariance theorem is proved; the Janus-specific group and
bundle actions remain a specialization theorem.

## Lean correspondence

The formal finite-set/action model is in:

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusFiniteJetEquivariance.lean
```

The principal results are:

```text
operator_natural_iff_evaluator_equivariant
evaluator_unique_of_surjective_jet
exists_unique_equivariant_evaluator
```

Stable build:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

## Evidence classification

| Statement | Status |
| --- | --- |
| finite-jet factorization under Peetre--Slovak hypotheses | external analytic theorem/interface |
| naturality implies equivariance on realizable jets | formal consequence |
| equivariance on the full jet fiber | requires holonomic jet realization |
| converse construction of a natural operator | formal descent from an equivariant evaluator |
| evaluator uniqueness | requires surjective jet realization; proved in Lean model |
| complete adapted Janus SpinC jet group | open |
| polynomial invariant classification | open and not implied by smooth naturality |
| ellipticity | independent condition |

## Exact conclusion

The defensible Lemma 2 is:

> Once a regular local operator has a finite-jet presentation, its naturality is
> equivalent to equivariance of its smooth jet evaluator under the sufficiently
> high adapted jet symmetry group, provided the relevant holonomic jets are
> realizable. The evaluator is then unique when jet realization is surjective.
