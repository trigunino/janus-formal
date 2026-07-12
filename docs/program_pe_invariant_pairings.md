# Program P.D — Pointwise Invariant Pairings and Residual Coupling Shapes

> Globalization correction: [`program_pd_global_pairing_modules.md`](program_pd_global_pairing_modules.md)  
> Categorical jet setting: [`program_pe_categorical_jet_equivalence.md`](program_pe_categorical_jet_equivalence.md)

## Scope correction

This document classifies invariant pairing **shapes at a fixed representation
fiber or frozen structured jet**. Its low-rank Lean and SymPy calculations remain
valid in that scope.

It does not prove that a one-dimensional pointwise pairing space gives one
constant global natural coupling. Global pairing families form a module over the
algebra of invariant scalar functions on the structured-jet base; isotropy and
fiber dimensions can also change between strata. The separate globalization
document proves this correction and records the remaining theorem queue.

## Purpose

Programs P-A through P-C reduce the action-selection problem to the remaining
quadratic and lower-order couplings between natural field sectors. Program P.D
first turns the **fiberwise shapes** of those coefficients into a
representation-theory question:

```text
Which scalar bilinear maps at a fixed background jet

  E_i x E_j -> R or C

are invariant under tangent rotations, PT, gauge charge and the normal-root Z4?
```

At that fixed jet, the answer determines whether a pairing is forbidden, unique
up to a fiberwise scalar, or genuinely multi-parameter. Globalization then
requires the invariant scalar coefficient algebra and the equivariant pairing
module.

## Symmetry layers

The current local candidate has several logically distinct symmetry layers:

```text
Spin(3) or O(3) tangent-frame symmetry,
U(1) monopole/gauge charge,
normal-root Z4 holonomy,
PT conjugation/exchange,
Grassmann parity and BRST grading.
```

The precise global group may be a central product rather than a direct product,
because the square of the lifted normal generator can coincide with fermion
parity. Program P.D therefore applies the selection rules layer by layer and
does not silently identify the normal Z4 with gauge U(1) or tangent rotations.
For a varying background, these local symmetry groups must ultimately be
organized as isotropy groups of a structured jet groupoid.

## Discrete charge selection

A scalar bilinear between sectors with additive charges

```text
(pt_1,z4_1), (pt_2,z4_2)
```

requires

```text
pt_1 + pt_2 = 0 mod 2,
z4_1 + z4_2 = 0 mod 4.
```

For the two normal-root sectors:

```text
+i sector: z4 = 1,
-i sector: z4 = 3.
```

Therefore:

```text
1+1 = 2 mod 4  -> same-root quadratic term forbidden,
3+3 = 2 mod 4  -> same-root quadratic term forbidden,
1+3 = 0 mod 4  -> conjugate cross pairing allowed.
```

Lean:

```text
P0EFTJanusPEChargeSelection.lean
```

Exact pointwise result:

```text
conjugate (+i,-i) doublet: one quadratic shape up to a fiberwise scalar;
uncharged PT doublet: two fiberwise coefficients remain (diagonal and cross).
```

Thus the Z4 does real pointwise work: it removes multiplicity-space freedom in
the conjugate quarter sector. PT exchange alone does not. This does not fix the
allowed scalar as one background-independent constant.

## Tangent representation audit

The explicit Lean model uses signed coordinate permutations, a finite subgroup
of `O(3)`. The exact SymPy audit then adds generic rational rotations with
cosine `3/5` and sine `4/5`.

| Pairing | Signed-permutation dimension | Full tested `O(3)` dimension |
| --- | ---: | ---: |
| scalar x scalar | 1 | 1 |
| scalar x vector | 0 | 0 |
| scalar x traceless tensor | 0 | 0 |
| vector x vector | 1 | 1 |
| vector x traceless tensor | 0 | 0 |
| traceless tensor x traceless tensor | 2 | 1 |

Lean:

```text
P0EFTJanusPEInvariantPairings.lean
P0EFTJanusPETensorPairingFreedom.lean
```

Python/SymPy:

```text
python scripts/audit_janus_pe_invariant_pairings.py
pytest -q tests/test_janus_pe_invariant_pairings.py
```

## Vector theorem

Invariance under coordinate sign flips kills every off-diagonal coefficient of
a general `3 x 3` bilinear form. Coordinate swaps equate the three diagonal
coefficients. Hence

```text
B(v,w) = c * (v_x w_x + v_y w_y + v_z w_z).
```

At a fixed representation fiber, the tangent-vector pairing shape is unique up
to one scalar. The same reflection tests prove that scalar-vector and
scalar-traceless linear couplings vanish. Global inversion also forbids an odd
vector from pairing to an even tensor into a scalar.

## Why finite monodromy is insufficient for the rank-five tensor sector

Write a traceless symmetric tensor as

```text
[[a,  xy,      xz],
 [xy, b,       yz],
 [xz, yz, -a - b]].
```

Signed permutations leave two independent norms:

```text
diagonal traceless norm,
off-diagonal norm.
```

They are independent. Therefore PT, Z4 and a finite cubic subgroup do **not**
select a unique rank-five tensor kinetic shape.

A generic continuous rotation mixes the diagonal and off-diagonal subspaces and
forces their fiberwise coefficients to agree. The surviving pointwise pairing
shape is the Frobenius contraction, up to scale. In the coordinates above, a
convenient normalized matrix is

```text
[[1,   1/2, 0, 0, 0],
 [1/2, 1,   0, 0, 0],
 [0,   0,   1, 0, 0],
 [0,   0,   0, 1, 0],
 [0,   0,   0, 0, 1]].
```

This is one half of `tr(T U)` in the chosen coordinates.

## Interpretation in irreducible-representation language

For the standard low-rank `O(3)` sectors:

```text
scalar               l=0,
vector               l=1,
traceless Sym^2      l=2.
```

The audit realizes the expected pointwise multiplicity rule:

```text
Hom_G(E_i tensor E_j, scalar)
  has dimension 0 for inequivalent irreducibles,
  and dimension 1 for the displayed self-pairings.
```

Repeated copies of the same irreducible introduce a multiplicity space. Its
bilinear forms remain free unless PT, Z4, gauge charge or a microscopic law
reduces them. This is one location of residual couplings.

There is a second, independent location: even when the fiberwise invariant
space has rank one, its coefficient may be a nonconstant invariant function of
the background jet. Thus the global object is an equivariant module, not merely
one vector space over the constant scalars.

## Invariant-coefficient module theorem

The focused head now imports

```text
P0EFTJanusInvariantCoefficientModule.lean
```

which proves in an abstract action model:

```text
invariant scalar coefficient
  * invariant background-dependent pairing
  -> invariant background-dependent pairing.
```

It also gives a finite two-background counterexample with one fixed pointwise
pairing shape but no single constant proportionality factor. This formally
blocks the inference from pointwise multiplicity one to constant global
uniqueness.

## What P.D has proved and what it has not

### Proved/formalized

- Z4 and PT charge-neutrality rules;
- one-dimensional conjugate-quarter pointwise quadratic pairing shape;
- two-dimensional uncharged PT-doublet pointwise pairing space;
- uniqueness of the tangent metric pairing shape up to a fiberwise scalar;
- vanishing of scalar-vector and scalar-traceless pairings;
- existence of two independent cubic tensor pairings;
- equality of their fiberwise scales under a generic continuous rotation;
- exact symbolic dimensions in the low-rank `O(3)` audit;
- module closure under invariant scalar coefficients;
- a finite counterexample to one constant global scale.

### Still open

- construction of the exact structured local-symmetry groupoid;
- `Spin(3)=SU(2)` classification of all complex bilinear and Hermitian spinor
  pairings in the same global framework;
- gauge/ghost and BRST-graded invariant pairings;
- all multiplicity spaces arising from flavors, folds and bulk reductions;
- isotropy stratification and possible dimension jumps;
- globalization from pointwise representations to smooth equivariant bundle
  morphisms;
- the invariant scalar algebra on the admissible Janus jet space;
- finite generation of the equivariant pairing module in the declared
  polynomial/weighted subclass;
- normalization of each surviving generator;
- compatibility with the full Helmholtz, anomaly and Fredholm families.

## Sharp verdict

```text
P.D does not yet fix the action.

At a fixed structured jet it converts candidate couplings into:
  1. forbidden pairing shapes (dimension 0),
  2. one fiberwise shape per multiplicity-one invariant (dimension 1),
  3. explicit matrices on repeated-irrep multiplicity spaces (dimension >1).

Globally it must additionally compute:
  4. invariant scalar coefficient functions,
  5. the equivariant pairing module across isotropy strata.
```

The rank-five tensor sector is pointwise multiplicity one only under the full
continuous tangent rotation group. Finite monodromy, PT and Z4 are insufficient.
Conversely, the normal-root Z4 genuinely reduces the PT-conjugate quarter
doublet to one cross-pairing shape. Neither result fixes a background-dependent
coefficient or physical normalization.

## Next theorem queue

1. Construct the structured SpinC/PT/Z4/BRST jet groupoid.
2. Determine its isotropy stratification and the invariant scalar algebra.
3. Formalize the `Spin(3)` fundamental-spinor invariant epsilon tensor and
   Hermitian metric, each unique up to a fiberwise scalar.
4. Add `U(1)` charge neutrality and BRST/Grassmann grading to the full sector
   label.
5. Compute the multiplicity matrices for every repeated Janus sector.
6. Compute global pairing generators as a module over scalar invariants.
7. Prove extension across singular isotropy strata.
8. Insert a finite order/weight-restricted pairing basis into the coupled
   Helmholtz operator.
9. Use the parent bulk action, anomaly constraints and finite matching law to fix
   the surviving normalizations.
