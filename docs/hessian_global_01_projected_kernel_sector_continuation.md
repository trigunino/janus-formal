# HESSIAN-GLOBAL-01 — sectorwise projected-kernel continuation

## Status

This note records the continuation layers added after the local projected Gram
chart on PR #60.  It is a dependency and proof-obligation map.  It does **not**
claim that the current branch has completed final Lean elaboration cleanup.

The actual Candidate-A operator family, its true kernel, the five-sector Hilbert
completion and all downstream Fredholm–zeta/families-index data remain the same.
Only the choice and continuation of the finite kernel basis are refined.

## 1. Exact five-block determinant factorization

For the canonical projected vectors

```text
e~_i(a) = P_{s(i)} e_i(a),
```

vectors carrying different physical sector labels are orthogonal.  Hence their
full Gram matrix has no off-sector entries.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramFactorization4D.lean`
proves

```text
det G(a) = ∏ s : FivePhysicalSector, det G_s(a),
```

including sectors with no labelled zero modes, whose empty determinant is one.
It follows exactly that

```text
U_Gram = ⋂ s, U_s,
```

where

```text
U_s = {a | det G_s(a) ≠ 0}.
```

Every `U_s` is open and contains the H12 basepoint.

## 2. Sectorwise global continuation

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D.lean`
packages the exact pointwise condition

```text
∀ a s, det G_s(a) ≠ 0.
```

This condition gives immediately

```text
U_s = Real          for every sector s,
U_Gram = Real,
```

and therefore constructs the global projected physical basis, the replacement
named-kernel family closure and its inherited C1 ambient regularity.

Two sufficient routes are exposed:

1. prove every already-open `U_s` is also closed;
2. prove positive sector determinant margins

   ```text
   ε_s ≤ |det G_s(a)|.
   ```

The five margins combine into the full margin

```text
∏ s, ε_s ≤ |det G(a)|.
```

## 3. Linear-independence characterization

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorIndependence4D.lean`
identifies each sector block with the ordinary real Gram matrix of its projected
vectors.  Thus, for every parameter and sector,

```text
det G_s(a) ≠ 0
  ↔ projected sector vectors are linearly independent
  ↔ projected sector coefficient synthesis is injective.
```

The global no-crossing packet is therefore exactly five families of finite
linear-independence statements, not an additional determinant-line premise.

## 4. Quadratic coercivity route

`P0EFTJanusProgramPFiniteFamilyGramQuadratic4D.lean` proves the generic identity

```text
c · G(c) = ⟪S(c), S(c)⟫ = ‖S(c)‖².
```

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorCoercivity4D.lean`
uses it to show that sector estimates

```text
κ_s ‖c‖² ≤ c · G_s(a)c,
κ_s > 0,
```

force all sector synthesis maps to be injective.  This route bypasses explicit
determinant estimates and closes the same global projected physical family.

## 5. Projection as a finite perturbation

`P0EFTJanusProgramPFiniteFamilySynthesisPerturbation4D.lean` proves the generic
finite perturbation statement

```text
m ‖c‖ ≤ ‖S_ref(c)‖,
‖S_ref(c) - S_target(c)‖ ≤ δ ‖c‖,
δ < m
  ⇒ S_target is injective.
```

For Candidate-A,

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelProjectionLeakage4D.lean`
proves the exact synthesis identity

```text
S_projected,s(c) = P_s S_named,s(c).
```

The synthesis defect is therefore not abstract:

```text
S_named,s(c) - S_projected,s(c)
  = (1 - P_s) S_named,s(c).
```

A lower bound for the named sector family together with an off-sector leakage
bound smaller than that lower bound produces the global physical basis.

## 6. The named reference lower bound is automatic pointwise

`P0EFTJanusProgramPFiniteFamilySynthesisLowerBound4D.lean` proves that any
injective finite synthesis map has a positive norm lower bound, using finite-
dimensional anti-Lipschitzness.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNamedSectorReference4D.lean`
then proves:

```text
all named kernel vectors are linearly independent in the ambient Hilbert space;
every sector-labelled named subfamily is linearly independent;
its synthesis map is injective;
it has a canonically selected positive pointwise lower constant m(a,s).
```

Consequently, pointwise conditioning of the named reference family is not an
external mathematical premise.  What may still require an analytic proof is a
usable uniform or explicit estimate on that conditioning.

## 7. Strict physical projection angle

The same file exposes a determinant-free sufficient condition:

```text
c ≠ 0
  ⇒ ‖(1 - P_s) S_named,s(a,c)‖
       < ‖S_named,s(a,c)‖.
```

If a projected combination vanished, the leakage would equal the whole named
combination, contradicting this strict inequality.  Therefore the projected
sector synthesis is injective and all subsequent global closure results follow.

## 8. Canonically conditioned leakage frontier

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D.lean`
removes the separate named-reference lower-bound packet.  It is enough to prove
pointwise constants `δ(a,s)` satisfying

```text
0 ≤ δ(a,s) < m(a,s),

‖(1 - P_s) S_named,s(a,c)‖
  ≤ δ(a,s) ‖c‖,
```

where `m(a,s)` is the canonical positive lower constant already generated from
the named basis.

This produces the strict angle, sector no-crossing, the global physical basis,
the rebuilt named-kernel family closure and its C1 regularity.

## 9. Current irreducible physical estimate

The former global statement

```text
“the projected zero modes form a basis of ker H_a for every a”
```

has now been reduced to a concrete small-angle estimate:

```text
control the norm of (1 - P_s) on named-sector kernel combinations
strictly below the finite conditioning of those combinations.
```

Equivalent stronger routes remain available:

```text
sector determinant gap,
sector synthesis lower bound,
sector Gram quadratic coercivity.
```

No extra kernel, replacement operator, auxiliary completion or independent
families-index closure is introduced by any of these routes.

## 10. Terminal module of this continuation chain

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
```

Building that module imports the determinant factorization, sector no-crossing,
linear-independence, coercivity, finite perturbation, named-sector conditioning
and canonical leakage layers in dependency order.
