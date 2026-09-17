# T12: positive LL energy / closed-graph bridge and weak shifts

Date: 2026-09-17.
Base: `dev-branch` at `53a70985e284e73952883ec648fa5056cea07598`.
Mathlib source API reviewed at the repository's pinned revision
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (v4.31.0).

## Validation and scope

This is a partial analytic support block, **not closure of terminal T12**.
Lean proof scripts have been added, but no Lean build, GitHub Actions run,
or other CI/CD operation was performed. Local compilation is still required.
No workflow or dependency configuration was changed.

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

The existing `P0EFTJanusProgramPT12LLStrongJacobiShiftedInverseOnRange4D.lean`
imports the new LL weak-solution module. Its previous proof is unchanged.
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
