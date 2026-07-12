# Program P.E — Invariant Pairings and Residual Coupling Space

## Purpose

Programs P-A through P-C reduce the action-selection problem to the remaining
quadratic and lower-order couplings between natural field sectors. Program P.E
turns those coefficients into a representation-theory question:

```text
Which scalar bilinear maps

  E_i x E_j -> R or C

are invariant under tangent rotations, PT, gauge charge and the normal-root Z4?
```

The answer determines whether a coupling is forbidden, unique up to one scale,
or genuinely multi-parameter.

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
parity. Program P.E therefore applies the selection rules layer by layer and
does not silently identify the normal Z4 with gauge U(1) or tangent rotations.

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

Exact result:

```text
conjugate (+i,-i) doublet: one quadratic coefficient up to scale;
uncharged PT doublet: two coefficients remain (diagonal and cross).
```

Thus the Z4 does real work: it removes multiplicity-space freedom in the
conjugate quarter sector. PT exchange alone does not.

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

The tangent-vector pairing is unique up to one normalization.

The same reflection tests prove that scalar-vector and scalar-traceless linear
couplings vanish. Global inversion also forbids an odd vector from pairing to
an even tensor into a scalar.

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
select a unique rank-five tensor kinetic term.

A generic continuous rotation mixes the diagonal and off-diagonal subspaces and
forces their coefficients to agree. The surviving pairing is the Frobenius
contraction, up to scale. In the coordinates above, a convenient normalized
matrix is

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

The audit realizes the expected multiplicity rule:

```text
Hom_G(E_i tensor E_j, scalar)
  has dimension 0 for inequivalent irreducibles,
  and dimension 1 for the displayed self-pairings.
```

However, repeated copies of the same irreducible introduce a multiplicity
space. Its bilinear forms remain free unless PT, Z4, gauge charge or a
microscopic law reduces them. This is the correct location of residual
couplings.

## What P.E has proved and what it has not

### Proved/formalized

- Z4 and PT charge-neutrality rules;
- one-dimensional conjugate-quarter quadratic pairing;
- two-dimensional uncharged PT-doublet pairing space;
- uniqueness of the tangent metric pairing up to scale;
- vanishing of scalar-vector and scalar-traceless pairings;
- existence of two independent cubic tensor pairings;
- equality of their scales under a generic continuous rotation;
- exact symbolic dimensions in the low-rank `O(3)` audit.

### Still open

- construction of the exact global local-symmetry group or groupoid;
- `Spin(3)=SU(2)` classification of complex bilinear and Hermitian spinor
  pairings in the same formal framework;
- gauge/ghost and BRST-graded invariant pairings;
- all multiplicity spaces arising from flavors, folds and bulk reductions;
- globalization from pointwise representations to bundle morphisms;
- normalization of each surviving one-dimensional invariant space;
- compatibility with the full Helmholtz, anomaly and Fredholm families.

## Sharp verdict

```text
P.E does not yet fix the action.

It converts arbitrary coupling coefficients into:
  1. forbidden pairings (dimension 0),
  2. one normalization per multiplicity-one invariant (dimension 1),
  3. explicit matrices on repeated-irrep multiplicity spaces (dimension >1).
```

The central new result is that the rank-five tensor sector is multiplicity one
only under the full continuous tangent rotation group. Finite monodromy, PT and
Z4 are insufficient. Conversely, the normal-root Z4 genuinely reduces the
PT-conjugate quarter doublet to one cross pairing.

## Next theorem queue

1. Formalize the `Spin(3)` fundamental-spinor invariant epsilon tensor and
   Hermitian metric, each unique up to scale.
2. Add `U(1)` charge neutrality and BRST/Grassmann grading to the full sector
   label.
3. Compute the multiplicity matrices for every repeated Janus sector.
4. Prove the pointwise invariant classifications globalize to natural bundle
   pairings.
5. Insert the resulting pairing basis into the coupled Helmholtz operator.
6. Use the parent bulk action, anomaly constraints and finite matching law to
   fix the surviving normalizations.
