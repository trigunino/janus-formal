# HESSIAN-GLOBAL-01 — terminal D11 unitary Fredholm--Green chain

## Status

This note records the terminal continuation architecture added on PR #60 after
the projected-kernel and unitary-frame work.  It is a dependency and proof
frontier, not a claim that final Lean elaboration cleanup has completed.

The construction never changes the genuine Candidate-A operator family, its
H12/H14 Hilbert completion, its actual kernel, its relative heat/zeta family or
its spectral-cut atlas.

## 1. D11 geometric input

For each family parameter `a`, the represented D11 layer selects an admissible
isomorphism from the represented H12 object to the represented object at `a`.
The remaining geometric statements are now explicit:

```text
represented forward pullback is real-linear;
represented reverse pullback is real-linear;
forward and reverse pullbacks are mutual inverses;
reverse source and target pullbacks agree in the fixed Candidate-A Hilbert model;
reverse pullback preserves the Candidate-A Hilbert norm.
```

Functoriality derives the inverse equations.  D11 naturality derives

```text
H_a F_a = F_a H_0,
```

and the already implemented five-sector covariance derives

```text
F_a P_s = P_s F_a.
```

The two C1 inputs are

```text
a ↦ F_a e_i(0)
```

for every exact H12 zero mode and

```text
a ↦ F_a v
```

for every fixed `v ∈ (ker H_0)ᗮ`.

## 2. Actual kernel and canonical complement

The unitary basepoint frame defines

```text
U_ab = F_b F_a⁻¹.
```

The generic restriction theorem gives exact isometric transports

```text
ker H_a       ≃ₗᵢ ker H_b,
(ker H_a)ᗮ    ≃ₗᵢ (ker H_b)ᗮ,
```

with identity and cocycle laws.

The transported H12 basis is a complete basis of every actual kernel and is
fixed by its assigned physical projector.  The same frame, rather than an
independent choice, trivializes every orthogonal complement.

## 3. Uniform reduced gap

A basepoint estimate

```text
c ‖x‖ ≤ ‖H_0 x‖,
x ∈ (ker H_0)ᗮ,
```

is transported without loss:

```text
c ‖y‖ ≤ ‖H_a y‖,
y ∈ (ker H_a)ᗮ.
```

Thus every genuine reduced operator is injective and one constant controls the
whole unitarily trivialized family.

## 4. Transported Green family

Given the genuine H12 reduced Green operator `G_0`, define

```text
H_red,a = F_a H_red,0 F_a⁻¹,
G_a     = F_a G_0     F_a⁻¹.
```

The implementation proves:

```text
H_red,a x = H_a x;
H_red,a G_a = id;
G_a H_red,a = id;
‖G_a‖ ≤ ‖G_0‖.
```

Both maps are bundled as continuous linear endomorphisms of the current fibre
`(ker H_a)ᗮ`.

If the H12 estimate supplies

```text
‖G_0‖ ≤ c⁻¹,
```

then

```text
‖G_a‖ ≤ c⁻¹
```

for every parameter.

## 5. Exact fixed-coordinate trivialization

Pulling the reduced and Green operators back to the H12 complement gives
literal equalities

```text
F_a⁻¹ H_red,a F_a = H_red,0,
F_a⁻¹ G_a     F_a = G_0.
```

The fixed-coordinate vector families are therefore differentiable constants.
This removes any artificial derivative caused solely by changing reduced
fibres.  A nontrivial connection term must come from the derivative of the
moving frame itself, not from an unrelated identification of complements.

## 6. Route-independent terminal closure

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D.lean`

packages, from one D11 unitary frame, one H12 Green and one H12 gap:

* the globally sector-pure physical kernel family;
* C1 kernel vectors in the common ambient Hilbert space;
* pairwise unitary complement transports and their cocycle;
* C1 transported complement vectors;
* the uniform reduced gap;
* bundled two-sided Green operators;
* the uniform `gap⁻¹` Green bound;
* exact fixed-coordinate constancy;
* unchanged family-index, relative heat, zeta and spectral-cut data.

The terminal build facade is

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenTerminal4D
```

## 7. Current irreducible proofs

The remaining geometric/Fredholm content is now concentrated in the following
items:

1. construct the basepoint-to-parameter admissible D11 isomorphisms for the
   genuine Candidate-A represented objects;
2. prove real-linearity of their represented forward and reverse pullbacks;
3. prove reverse source/target pullback agreement;
4. prove preservation of the Candidate-A Hilbert norm;
5. prove the two C1 vector-family statements for kernel and complement vectors;
6. identify the already existing H14 gap and Green certificates with the
   generic basepoint `gap` and `green` packets used by this chain.

## 8. Remaining analytic/zeta work after the closure

The terminal closure settles the moving-fibre geometry and supplies bounded
Green operators.  The following analytic statements are still separate:

1. operator-topology regularity of the unitary frame, sufficient to define its
   connection generator;
2. the covariant derivative formula corresponding to

   ```text
   G'_a = -G_a H'_a G_a;
   ```

3. the analogous unitary trivialization and derivative control for the selected
   reference family;
4. intrinsic trace-class properties of

   ```text
   G_a H'_a - G_ref,a H'_ref,a;
   ```

5. identification of that intrinsic relative trace with the geometric
   Bismut--Freed one-form and, subsequently, the higher-dimensional
   families-index curvature.

The key change is that these statements now live on one canonical C1 unitary
Fredholm frame rather than on independently chosen kernel and complement
families.
