# HESSIAN-GLOBAL-01 — terminal H14–D11 unitary Fredholm–Green chain

## Status

This note records the terminal continuation architecture added on PR #60 after
the projected-kernel and unitary-frame work. It is a dependency and proof
frontier, not a claim that final Lean elaboration cleanup has completed.

The construction never changes the genuine Candidate-A operator family, its
H12/H14 Hilbert completion, its actual kernel, its relative heat/zeta family or
its spectral-cut atlas.

The concrete H14 gap and Green operator are now connected directly to the D11
unitary continuation. They are no longer independent inputs of the terminal
family package.

## 1. D11 geometric input

For each family parameter `a`, the represented D11 layer selects an admissible
isomorphism from the represented H12 object to the represented object at `a`.
The remaining geometric statements are explicit:

```text
represented forward pullback is real-linear;
represented reverse pullback is real-linear;
forward and reverse pullbacks are mutual inverses;
reverse source and target pullbacks agree in the fixed Candidate-A Hilbert model;
reverse pullback preserves the Candidate-A Hilbert norm.
```

Functoriality derives the inverse equations. D11 naturality derives

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
fixed by its assigned physical projector. The same frame, rather than an
independent choice, trivializes every orthogonal complement.

## 3. Concrete H14 basepoint data

The preferred H14 route already contains the exact analytic data required at
the unitary basepoint:

```text
closure.frontier.analytic.toActualKernelGap.gapData
```

is the gap on the orthogonal complement of the genuine kernel, and

```text
globalCandidateAActualKernelGreen
```

is the canonical reduced Green operator produced from that same gap.

The H12/H14 actual-kernel complement certificate proves

```text
H_red,0 G_0 = id;
G_0 H_red,0 = id;
‖G_0‖ ≤ gap⁻¹.
```

The selected family spells its zero member as

```text
input.familyIndex.baseFamily.actualOperator 0,
```

whereas the pointwise H14 files use the canonical Candidate-A operator spelling.
The existing field

```text
input.familyIndex.baseFamily.actual_zero
```

identifies them exactly.

`P0EFTJanusProgramPFiniteKernelComplementBasepointDataTransport4D.lean`
transports a gap and Green packet through this zero-fibre equality while
preserving the gap scalar, Green operator and operator norm exactly.

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14BasepointFredholmGreenAdapter4D.lean`
then constructs the generic unitary Fredholm–Green closure directly from the
concrete H14 data. No comparison estimate, second inverse or new analytic
premise is introduced.

## 4. Uniform reduced gap

The concrete H14 estimate

```text
c ‖x‖ ≤ ‖H_0 x‖,
x ∈ (ker H_0)ᗮ,
```

is transported without loss:

```text
c ‖y‖ ≤ ‖H_a y‖,
y ∈ (ker H_a)ᗮ.
```

Thus every genuine reduced operator is injective and the literal H14 constant
controls the whole unitarily trivialized family.

## 5. Transported Green family

Using the genuine H14 Green `G_0`, define

```text
H_red,a = F_a H_red,0 F_a⁻¹,
G_a     = F_a G_0     F_a⁻¹.
```

The implementation proves:

```text
H_red,a x = H_a x;
H_red,a G_a = id;
G_a H_red,a = id;
‖G_a‖ ≤ ‖G_0‖ ≤ c⁻¹.
```

Both maps are bundled as continuous linear endomorphisms of the current fibre
`(ker H_a)ᗮ`.

## 6. Exact fixed-coordinate trivialization

Pulling the reduced and Green operators back to the H12 complement gives
literal equalities

```text
F_a⁻¹ H_red,a F_a = H_red,0,
F_a⁻¹ G_a     F_a = G_0.
```

The fixed-coordinate vector families are therefore differentiable constants.
This removes any artificial derivative caused solely by changing reduced
fibres. A nontrivial connection term must come from the derivative of the
moving frame itself, not from an unrelated identification of complements.

## 7. Concrete terminal closure

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenClosure4D.lean`
instantiates the generic closure with the concrete H14 gap and Green and exports
in one theorem:

* the globally sector-pure physical kernel family;
* C1 kernel vectors in the common ambient Hilbert space;
* pairwise unitary complement transports and their cocycle;
* C1 transported complement vectors;
* the unchanged H14 reduced gap at every parameter;
* bundled two-sided Green operators;
* the uniform `gap⁻¹` Green bound;
* exact fixed-coordinate Green constancy;
* unchanged family-index, relative heat, zeta and spectral-cut data.

The concrete terminal build facade is

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenTerminal4D
```

The earlier generic facade remains available for users who intentionally supply
a different abstract basepoint packet.

## 8. Current irreducible geometric proofs

The H14-to-generic-gap/Green identification is now architecturally closed. The
remaining geometric content is concentrated in:

1. construct the basepoint-to-parameter admissible D11 isomorphisms for the
   genuine Candidate-A represented objects;
2. prove real-linearity of their represented forward and reverse pullbacks;
3. prove reverse source/target pullback agreement;
4. prove preservation of the Candidate-A Hilbert norm;
5. prove the two C1 vector-family statements for kernel and complement vectors.

Once these five properties are supplied, the concrete H14 terminal theorem
produces the complete moving-kernel and moving-Green family without any further
Fredholm premise.

## 9. Remaining analytic/zeta work after the closure

The terminal closure settles the moving-fibre geometry and supplies bounded
Green operators. The following analytic statements remain separate:

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
   Bismut–Freed one-form and, subsequently, the higher-dimensional
   families-index curvature.

The key change is that these statements now live on one canonical C1 unitary
Fredholm frame whose basepoint Green and gap are the already existing H14
objects, rather than on independently chosen kernel, complement and inverse
families.
