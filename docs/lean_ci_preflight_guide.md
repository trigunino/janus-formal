# Lean CI preflight guide

This guide records the failure patterns encountered while formalizing the projected-seed/Riesz/structured-jet pipeline and turns them into a repeatable pre-push checklist.

## Goal

Reduce broken CI runs by catching the most common elaboration failures before pushing, while preserving a fast targeted diagnostic path when a genuinely new module is introduced.

## Working rule

Before every push, classify the change into one of three categories:

1. **Definitional cleanup** — use `rfl`, explicit projections, or a fully-qualified name.
2. **Elaboration repair** — add explicit types, namespaces, lambdas, or universe parameters.
3. **Mathematical extension** — add a new definition/theorem/module.

Do not mix category 3 with unresolved category 1 or 2 failures.

## Pre-push checklist

### 1. Check namespaces first

When a definition comes from another gate, either open the exact namespace or use its fully-qualified name.

Typical failures:

- `ContinuousSecondFundamentalForm` not found;
- `curvature` resolving to the wrong definition;
- theorem names found but with unexpected implicit parameters.

Preferred pattern:

```lean
open P0EFTJanusRieszShapeOperatorSmoothDependence
```

or, for ambiguous names:

```lean
P0EFTJanusConcreteAbelianConnectionJet.curvature
```

### 2. Make reusable type aliases explicitly parameterized

Avoid section-dependent `abbrev`s whose implicit parameter names may change during elaboration.

Fragile:

```lean
abbrev ContinuousConnectionDerivative :=
  Tangent →L[ℝ] Tangent →L[ℝ] ℝ
```

Preferred:

```lean
abbrev ContinuousConnectionDerivative
    (Tangent : Type u)
    [NormedAddCommGroup Tangent]
    [InnerProductSpace ℝ Tangent] :=
  Tangent →L[ℝ] Tangent →L[ℝ] ℝ
```

This makes downstream calls stable and prevents cascades of “invalid argument name” errors.

### 3. Match typeclass assumptions to the imported definition

Do not weaken assumptions in a wrapper alias unless the wrapped definition really supports it.

Example: `ContinuousSecondFundamentalForm` is used in an inner-product-space context. A wrapper requiring only `NormedSpace` may elaborate until a later line and then fail with confusing topology or continuity errors.

Rule: inspect the original declaration and copy its essential assumptions.

### 4. Prefer typed lambdas for smoothness proofs

Direct coercion from a `ContinuousLinearMap` to a function is sometimes ambiguous for `.contDiff`.

Fragile:

```lean
(myProjection).contDiff
```

Preferred:

```lean
have h : ContDiff ℝ ∞
    (fun x : Domain => myProjection x) := by
  fun_prop
```

For composite smooth maps, prove each typed component and combine with `prodMk` or `comp`.

### 5. Do not force a construction to be a CLM when only smoothness is needed

The continuous structured-jet reduction initially tried to package antisymmetrization as subtraction between operators on a space of operators. This introduced avoidable `HSub` and coercion problems.

Prefer the weakest structure required by the theorem.

If the pipeline only needs a smooth map, define:

```lean
def curvatureFromDerivative (dA : DerivativeSpace) : CurvatureSpace :=
  dA - flip dA
```

and prove:

```lean
theorem curvatureFromDerivative_contDiff :
    ContDiff ℝ ∞ curvatureFromDerivative := by
  change ContDiff ℝ ∞ (fun dA : DerivativeSpace => dA - flip dA)
  fun_prop
```

Upgrade to a continuous linear map only when a later theorem actually needs linearity as data.

### 6. Try definitional equality before automation

For record projections and transparent wrapper definitions, try `rfl` before `simp`, `rw`, or `fun_prop`.

Typical examples:

```lean
@[simp] theorem reduced_curvature_apply ... := by
  rfl
```

A failed `simp` on a definitionally equal statement often indicates that unfolding is not in the simp set, not that the theorem is difficult.

### 7. Avoid broad rewrites while the target is red

When a target fails:

1. read the exact targeted log;
2. identify the first non-cascade error;
3. fix all errors caused by the same root issue;
4. push one coherent correction;
5. do not add new mathematics before the target passes.

Large rewrites while red create new unknowns and make it hard to distinguish root errors from cascades.

### 8. Distinguish root errors from cascades

Common cascade pattern:

- missing namespace or wrong typeclass assumption;
- then many invalid field, projection, or implicit argument errors;
- then downstream theorem failures.

Fix the earliest declaration error first. Do not patch every downstream line independently.

### 9. Use `LEAN_TARGET` as a moving diagnostic pointer

Policy:

- while a new/failing module is under development, `LEAN_TARGET` contains exactly that module;
- once targeted and full builds pass, clear it;
- when the next new module is added, point it only to that module;
- never accumulate old targets.

The full focused build remains the regression gate.

### 10. Batch coherent work, not unrelated work

Good commit scope:

- one new interface plus its basic projection lemmas;
- one bridge plus all its definitional compatibility lemmas;
- one root elaboration fix across a module.

Bad commit scope:

- new geometry;
- workflow refactor;
- unrelated theorem cleanup;
- speculative optimization;

all at once.

## Recommended pre-push sequence

1. Re-read the imported declarations used by the new module.
2. Verify namespace openings and fully qualify ambiguous names.
3. Verify every reusable alias has explicit type parameters.
4. Verify wrapper assumptions match the wrapped definitions.
5. Replace ambiguous `.contDiff` coercions with typed lambdas and `fun_prop`.
6. Try `rfl` for projection/record equalities.
7. Ensure there is no `sorry` in the new gate.
8. Ensure `LEAN_TARGET` names only the new/failing gate.
9. Push one coherent commit.
10. Read the targeted log before touching the full build failures.

## Failure patterns observed in this PR

| Pattern | Symptom | Preferred repair |
|---|---|---|
| Missing namespace | unknown constant / wrong `curvature` | open exact namespace or fully qualify |
| Section-dependent alias | invalid named arguments, implicit parameter drift | explicit type parameters |
| Weak wrapper assumptions | topology/continuity instance failures | match original `InnerProductSpace` assumptions |
| CLM coercion ambiguity | `.contDiff` fails on a continuous linear map | typed lambda + `fun_prop` |
| Over-structured construction | `HSub`/coercion failures on operator spaces | use a smooth function unless CLM data is needed |
| Definitional projection | `simp` does not close a transparent equality | use `rfl` |
| Root error cascade | many unrelated-looking errors after one declaration | fix first declaration error only |
| Concurrent file update | GitHub 409 SHA mismatch | refetch current blob SHA before updating |

## Commit discipline for this branch

- Prefer fewer, larger coherent commits.
- Do not push every single line-level correction if several belong to the same root issue.
- Keep the targeted run fast.
- Once green, clear the target before moving to the next gate.
- Keep honest status ledgers for the genuinely unproved manifold/SpinC boundaries.
