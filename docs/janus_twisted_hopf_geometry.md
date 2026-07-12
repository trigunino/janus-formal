# Janus PT-Twisted Real Hopf Geometry

## Proposal

The resolved global Janus spacetime is modeled by the smooth quotient

```text
J(lambda,rho) = (R^4 minus {0}) / < x ~ lambda rho(x) >,
```

where

```text
0 < lambda < 1,
rho in O(4),
rho^2 = 1,
det(rho) = -1.
```

Choose `rho` as reflection across an equatorial `R^3`.  In logarithmic polar
coordinates

```text
x = exp(u) omega,
omega in S3,
```

the generator becomes

```text
(omega,u) -> (rho omega, u - T),
T = -log(lambda) > 0.
```

Thus `J(lambda,rho)` is the mapping torus of an orientation-reversing reflection
of `S3`.  It is the direct four-dimensional analogue of the Klein bottle.

## Why this is the correct dimensional lift

The Janus paper starts with a compact `S4` covering `P4`, identifies antipodal
Big-Bang/Big-Crunch regions, and proposes replacing the double singularity by a
tubular passage.  Its two-dimensional drawing says the resolved geometry has
the nature of a two-fold cover of a Klein bottle.

The proposed quotient realizes exactly that sequence:

```text
S4 with poles 0 and infinity
  -> remove both poles
R4 minus {0} ~= S3 x R
  -> identify logarithmic radius by reflection plus translation
PT-twisted mapping torus J(lambda,rho).
```

The singular points are not retained as orbifold fixed points.  They are
replaced by a compact logarithmic circle.

## Orientation double cover and the two folds

The generator `g` is orientation reversing.  Its square is

```text
g^2(omega,u) = (omega,u - 2T).
```

Therefore the orientation-preserving subgroup is `2Z`, and

```text
J_tilde = (S3 x R)/(u ~ u - 2T) ~= S3 x S1.
```

The quotient map

```text
S3 x S1 -> J(lambda,rho)
```

is a free two-fold orientation cover.  The deck group is `Z2`; the full tunnel
monodromy group is `Z`.

This distinction resolves an ambiguity in the older scaffold:

```text
orbifold/cover symmetry: Z2
tunnel monodromy: Z
fermionic Pin lift: possibly Z4
```

## Canonical throat

The reflection `rho` fixes an equatorial `S2` inside `S3`.  Its mapping torus is

```text
Sigma = S2 x S1.
```

This is the canonical Euclidean throat/world-volume.  It supplies:

- a compact `S2` carrying the auxiliary first Chern/flux class;
- a compact tunnel circle `S1`;
- a three-dimensional world-volume needed by the LL-brane;
- the missing circle for the relative-cohomology fiber integration
  `H^3(Sigma) -> H^2(S2)`.

The normal direction to the equator is reversed by `rho` after one tunnel
period.  Hence the normal line of `Sigma` is twisted once.  It becomes untwisted
on the orientation double cover after two periods.  This geometric normal
reversal is the natural carrier of the PT sign.

## Topological invariants

For the mapping torus of an orientation-reversing map of `S3`, the cellular top
boundary is multiplication by two.  The resulting ordinary integral homology is

```text
H0 = Z,
H1 = Z,
H2 = 0,
H3 = Z/2,
H4 = 0.
```

Because the manifold is nonorientable, the ordinary top class vanishes, while
the orientation-twisted top class is

```text
H4(J; Z_orientation) = Z.
```

The Euler characteristic is

```text
chi(J) = 0.
```

The orientation cover `S3 x S1` also has Euler characteristic zero.

## Locally conformally flat metric

The metric

```text
g0 = |x|^(-2) dx^2 = du^2 + g_S3
```

is invariant under both orthogonal reflection and radial dilation.  It therefore
descends to the quotient.  Multiplying by an overall squared radius gives

```text
g_R = R^2 (du^2 + g_S3).
```

The dimensionless tunnel period is `T`; the physical circle circumference is
proportional to `R T`.

This separates two roles cleanly:

```text
R : absolute geometric scale
T : dimensionless monodromy/RG hierarchy
```

## Geometry-RG identification

The quantum world-volume branch derives

```text
2 A = ell_UV exp(X).
```

The Hopf quotient gives

```text
lambda = exp(-T).
```

The unified identification is

```text
X = T,
2 A lambda = ell_UV.
```

Thus the exponentially large Janus radius and the exponentially small quotient
contraction are the same datum in inverse form.

For the diagnostic values

```text
A = 10^26 m,
ell_UV = ell_P,
```

one finds approximately

```text
T ~= 140,
lambda ~= 8.1e-62,
lambda^2 ~= 6.5e-123.
```

The familiar `10^-122` hierarchy appears as the contraction of the orientation-
preserving square monodromy, rather than as an inserted flux integer.

This numerical observation is not yet a prediction: the effective quantum
theory must derive `T`.

## Genuine Z4

The spacetime deck symmetry is only `Z2`.  A genuine `Z4` arises if the PT deck
transformation lifts to the Pin/fermionic bundle with

```text
G^2 = (-1)^F,
G^4 = 1.
```

Then

```text
1 -> Z2_F -> Z4 -> Z2_PT -> 1
```

is the correct central extension.  This supplies a precise possible meaning for
the older `Z4` sector while keeping the geometric cover two-to-one.

## Relation to the bimetric and LL programs

The proposed geometry supplies the missing common stage:

```text
orientation cover S3 x S1
  -> plus/minus hemispherical folds
canonical throat Sigma = S2 x S1
  -> LL auxiliary U(1) flux on S2
  -> compact transgression circle S1
normal-line twist
  -> PT reversal of boundary orientation/charge
Hopf period T
  -> world-volume RG exponent
```

The remaining physical theorems are now sharply stated:

1. construct the Lorentzian continuation and null throat metric;
2. derive the two-metric action on the two oriented folds;
3. prove that the normal twist makes the quasi-local bridge charge PT odd;
4. derive the relative Thom/boundary/fiber-integration map on `Sigma`;
5. match the full bulk and LL charge units;
6. derive the quantum effective action that fixes `T` and the overall scale.

## Formal files

```text
JanusFormal/Branches/JanusTwistedHopfGeometry.lean
JanusFormal/Branches/JanusTwistedHopfGeometry/Gates/
  P0EFTJanusTwistedHopfMonodromy.lean
  P0EFTJanusTwistedHopfTopologyInvariants.lean
  P0EFTJanusTwistedHopfScaleLaw.lean
  P0EFTJanusTwistedHopfThroatGeometry.lean
scripts/audit_janus_twisted_hopf_geometry.py
tests/test_janus_twisted_hopf_geometry.py
```

## Status

This is a proposed geometric completion, not a claim already present in the
Janus papers.  It is selected because it simultaneously realizes the projective
singularity resolution, the Klein-bottle analogy, the two-fold orientation
cover, a compact throat circle, PT normal reversal and the RG hierarchy
coordinate.
