# HESSIAN-GLOBAL-01 — projected physical kernel continuation frontier

## Status

This note records the projected-kernel continuation work added after the H12
basepoint Gram proof on PR #60.

It is an architectural and mathematical dependency map.  It does **not** claim
that the newly added Lean files elaborate successfully in the current branch;
final elaboration cleanup remains separate.

The operator family, the H12/H14 Hilbert completion, the actual kernel and the
family-index/spectral-cut data are unchanged throughout this route.

## 1. Starting point

For the existing named kernel basis `e_i(a)` and its fixed physical sector
assignment `s(i)`, define the canonical projected vector

```text
e~_i(a) = P_{s(i)} e_i(a).
```

The represented Candidate-A operator commutes with the fixed five physical
projectors.  Therefore every `e~_i(a)` is already

* a genuine element of `ker H_a`;
* fixed by its assigned physical projector;
* annihilated by the other physical projectors;
* differentiable in the common ambient Candidate-A Hilbert space;
* equal to the original action-generated H12 vector at `a = 0`.

The only missing fact was completeness of this projected family in the actual
kernel.

## 2. Basepoint closure

The coefficient synthesis of the projected vectors at `a = 0` is identified
with synthesis by the existing H12 basis.  Consequently:

```text
Gram(e~(0)) is injective;
coefficient synthesis at 0 is bijective;
e~_i(0) is a basis of ker H_0;
every zero mode at 0 has unique projected physical coordinates.
```

No new H12 premise is introduced.

## 3. Generic finite-dimensional persistence

`P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D.lean`

For a continuous finite family of vectors `v_i(a)` in one fixed real
inner-product space, the scalar Gram matrix is

```text
G(a)_{ij} = <v_j(a), v_i(a)>.
```

The file proves:

```text
finiteFamilyGramMap injective
  <-> det G != 0;

a |-> det G(a) is continuous;

Gram injective at a0
  -> Gram injective throughout a neighbourhood of a0.
```

This is a generic finite-dimensional theorem, independent of Candidate-A.

## 4. Candidate-A local physical basis

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramLocalPersistence4D.lean`

The Gram matrix computed in the varying subtype `ker H_a` is exactly the same
scalar matrix as the Gram matrix of the ambient projected vectors.  The generic
persistence theorem therefore gives

```text
for a near 0, Gram(e~(a)) is injective in the true kernel subtype.
```

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisLocal4D.lean`

Using the already established constant kernel rank, the local Gram statement is
upgraded to

```text
for a near 0, e~_i(a) is a basis of ker H_a;
coefficient synthesis is bijective;
every actual zero mode has unique projected physical coordinates.
```

## 5. Canonical open Fredholm chart

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D.lean`

defines

```text
U_Gram = {a : Real | det Gram(e~(a)) != 0}.
```

The implemented results are

```text
U_Gram is open;
0 belongs to U_Gram;
U_Gram is a neighbourhood of 0;

a belongs to U_Gram
  <-> the genuine projected Gram operator on ker H_a is injective.
```

At every point of `U_Gram`, the file constructs the canonical projected
physical basis and its unique coordinate map.

## 6. Exact transport on the regular chart

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularTransport4D.lean`

For `a,b in U_Gram`, transport keeps the fixed physical coordinates:

```text
T_ab = B_a.equivFun >> B_b.equivFun.symm.
```

It satisfies exactly

```text
T_ab(e~_i(a)) = e~_i(b);
T_aa = id;
T_bc o T_ab = T_ac.
```

Thus `U_Gram` carries a genuine local trivialization of the finite actual-kernel
bundle, not merely a collection of pointwise bases.

## 7. Exact global obstruction

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D.lean`

The former all-parameter projected-basis premise is now identified exactly with
one scalar no-crossing statement:

```text
U_Gram = Real
  <-> Gram(e~(a)) is injective for every a
  <-> the global projected Gram packet exists
  <-> the global projected physical kernel basis family exists.
```

The remaining global mathematical issue is therefore no longer “choose a good
basis family”.  It is precisely

```text
det Gram(e~(a)) never reaches zero along the genuine Candidate-A family.
```

## 8. Replacement of the arbitrary named family

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D.lean`

Assuming `U_Gram = Real`, the existing
`GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D` is rebuilt with

```text
familyIndex := the original familyIndex;
kernels     := the projected physical basis family.
```

The rebuilt closure has

* the same actual operator family;
* the same relative heat, zeta, spectral-cut and families-index data;
* sector-pure basis vectors at every parameter;
* the same action-generated H12 basis at `a = 0`;
* differentiable ambient basis vectors.

This is the direct bridge into the already implemented
`FiniteKernelBasisFamilyData` determinant/Fredholm architecture.  No parallel
family-index closure is introduced.

## 9. Two concrete global proof routes

`P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNoCrossingCriteria4D.lean`

### 9.1 Topological continuation

Because `Real` is connected, it is enough to prove that the already open and
nonempty set `U_Gram` is also closed:

```text
IsClosed U_Gram -> U_Gram = Real.
```

### 9.2 Quantitative continuation

A uniform positive determinant margin also closes the route:

```text
exists epsilon > 0,
  for every a,
    epsilon <= |det Gram(e~(a))|.
```

The file packages this as

```text
GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
```

and derives from it

```text
global projected physical basis;
projected physical named-kernel closure;
C1 regularity of that rebuilt closure.
```

## 10. Current irreducible proof

The local kernel problem is closed architecturally.  The outstanding global
content has been reduced to either of the equivalent/checkable tasks

```text
prove U_Gram is closed;
```

or

```text
prove a uniform positive lower bound for |det Gram(e~(a))|.
```

A more physical refinement may factor this estimate into the five orthogonal
sector blocks.  That sectorwise quantitative proof is the next natural step;
it is not claimed here.

## 11. Build target for this chain

The terminal module of the current continuation chain is

```text
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNoCrossingCriteria4D
```

Building that target imports all newly added projected-kernel continuation
layers in dependency order.
