# HESSIAN-GLOBAL-01 — unitary Fredholm-frame frontier

## Status

This note records the continuation layers added after the projected-kernel
noncrossing work on PR #60.  It is an architectural and mathematical dependency
map.  It does **not** claim that the newly added Lean files have completed final
elaboration cleanup.

The actual Candidate-A operator family, its H12/H14 completion, its true kernel,
its reduced Green data and all downstream heat/zeta/families-index structures
remain unchanged.

## 1. Why the kernel transport was not yet the whole C1 splitting

A linear equivalence intertwining

```text
H_b U_ab = U_ab H_a
```

maps `ker H_a` to `ker H_b`.  This is sufficient to transport the exact H12
zero-mode basis.

It does **not**, by itself, map the canonical reduced space

```text
(ker H_a)ᗮ
```

to `(ker H_b)ᗮ`.  Orthogonal complements depend on the Hilbert product.  The
ambient transport must therefore preserve that product.

## 2. Generic unitary restriction theorem

`P0EFTJanusProgramPFiniteUnitaryIntertwiningKernelComplementTransport4D.lean`

packages coherent linear isometric equivalences

```text
U_ab : E ≃ₗᵢ E
```

intertwining the operator family.  It proves that `U_ab` restricts to linear
isometric equivalences

```text
ker H_a       ≃ₗᵢ ker H_b,
(ker H_a)ᗮ    ≃ₗᵢ (ker H_b)ᗮ,
```

with exact identity and cocycle laws on both restrictions.

No projection back into a completion is used: both restrictions are subtypes of
the original common Candidate-A Hilbert space.

## 3. One basepoint frame is enough

`P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D.lean`

starts from one frame

```text
F_a : E ≃ₗᵢ E,
F_0 = id,
H_a F_a = F_a H_0.
```

It defines

```text
U_ab = F_b ∘ F_a⁻¹
```

and derives the pairwise identity, cocycle and operator-intertwining laws.
Consequently the same `F_a` gives canonical frames

```text
ker H_0       ≃ₗᵢ ker H_a,
(ker H_0)ᗮ    ≃ₗᵢ (ker H_a)ᗮ.
```

## 4. Candidate-A unitary Fredholm frame

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D.lean`

adds the physical Candidate-A requirements:

```text
F_a P_s = P_s F_a
```

for every one of the five H12/H14 sector projectors, together with the two C1
statements

```text
a ↦ F_a e_i(0)
```

for every exact H12 zero mode and

```text
a ↦ F_a v
```

for every fixed `v ∈ (ker H_0)ᗮ`.

The route-independent output contains

* the globally sector-pure physical named-kernel family;
* exact agreement with the action-generated basis at `a = 0`;
* the original family-index, heat, zeta and spectral-cut data;
* pairwise unitary transports of all orthogonal kernel complements;
* the exact complement cocycle;
* C1 ambient dependence of every fixed basepoint complement vector.

Thus the kernel and complement are not trivialized by unrelated choices.

## 5. Minimal represented D11 input

The D11 reduction is split into explicit layers.

### 5.1 Admissible isomorphisms

`P0EFTJanusAdmissibleMorphismIsomorphism.lean`

adds a first-class admissible isomorphism with forward and reverse admissible
morphisms and two inverse equations.

### 5.2 Linear represented pullbacks

`P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D.lean`

uses one admissible isomorphism from the represented H12 object to the object at
parameter `a`.  If represented forward and reverse source pullbacks are
real-linear, their inverse laws follow from section-pullback functoriality.
Reverse source/target pullback agreement and D11 naturality then give

```text
H_a F_a = F_a H_0.
```

The already implemented five-sector pullback covariance gives

```text
F_a P_s = P_s F_a.
```

### 5.3 Unitarity

`P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D.lean`

adds only

```text
‖F_a x‖ = ‖x‖.
```

This upgrades the represented linear frame to a `LinearIsometryEquiv` and hence
produces the canonical complement frame automatically.

### 5.4 Candidate-A closure

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D.lean`

adds C1 dependence on the H12 basis and the H12 complement, then exports the
complete physical unitary Fredholm-frame output.

## 6. Uniform reduced gap

`P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D.lean`

proves that a basepoint norm estimate

```text
c ‖x‖ ≤ ‖H_0 x‖,
x ∈ (ker H_0)ᗮ,
```

is transported without loss:

```text
c ‖y‖ ≤ ‖H_a y‖,
y ∈ (ker H_a)ᗮ.
```

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGapContinuation4D.lean`

combines this result with the Candidate-A unitary Fredholm frame.  The same
object therefore supplies

* the global physical finite kernel;
* the C1 unitary complement trivialization;
* one uniform reduced gap;
* injectivity of every actual operator on its canonical reduced fibre.

## 7. Current irreducible D11/Fredholm proof

The former request to independently choose

```text
a basis of ker H_a
```

and

```text
a trivialization of (ker H_a)ᗮ
```

has been replaced by the following geometric tasks:

1. construct, for every `a`, an admissible D11 isomorphism from the represented
   H12 object to the represented object at `a`;
2. prove that its represented forward and reverse pullbacks are real-linear;
3. identify reverse source and target pullback on the fixed Candidate-A Hilbert
   representation;
4. prove preservation of the Candidate-A Hilbert norm;
5. prove C1 dependence of `F_a e_i(0)` for every H12 zero mode;
6. prove C1 dependence of `F_a v` for every fixed
   `v ∈ (ker H_0)ᗮ`.

D11 naturality and the existing five-sector covariance then discharge all
operator-intertwining and sector-commutation equations automatically.

## 8. Remaining analytic continuation after the frame

The unitary frame closes the geometric C1 splitting and transports the gap.  It
does not by itself prove the later trace-class differentiation statements.  The
next analytic layer is to connect the transported reduced operators and Green
operators to the already selected Candidate-A family and establish, in the
required operator topology,

```text
G'_a = -G_a H'_a G_a
```

and the intrinsic relative trace-class properties used by the zeta connection.

## 9. Terminal module of the current chain

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
```

For the additional transported-gap output, the terminal module is

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
```
