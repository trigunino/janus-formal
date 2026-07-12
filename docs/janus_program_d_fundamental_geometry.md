# Program D — Fundamental Geometry as the Origin of Janus Physics

## Status

Active research branch:

```text
research/fundamental-geometry-d
```

Focused Lean head:

```text
lake build JanusFormal.Branches.FundamentalGeometryD
```

Program D asks a different question from the earlier alpha branches:

> Can the gauge field, world-volume quantum theory, PT/Pin data, bimetric bridge
> and the dimensionless alpha ratio all arise from one global geometry?

The starting candidate is the PT-twisted real Hopf mapping torus

```text
J(T,rho) = (S3 x R) / ((x,u) ~ (rho(x),u+T)),
```

where `rho` reverses the orientation of `S3`.  Equivalently it is the quotient
of `R4 \ {0}` by a contraction followed by `rho`.  Its orientation double cover
is expected to be `S3 x S1_(2T)`, and the fixed equator of the reflection gives
the canonical throat

```text
Sigma = S2 x S1_T.
```

The branch distinguishes proved algebra, geometric construction obligations and
physical emergence hypotheses.  No numerical alpha value is promoted.

## D0 — Evidence levels

Every claim belongs to one of four levels:

| Level | Meaning |
| --- | --- |
| **T** | theorem or exact algebra formalized in Lean |
| **G** | geometric construction target with standard mathematical support |
| **P** | physical emergence hypothesis requiring a new derivation |
| **N** | no-go or obstruction delimiting the candidate space |

This prevents a topological relation from being silently promoted to a quantum
prediction.

## D1 — Global geometry candidate

The inherited twisted-Hopf branch records the targets:

```text
compact nonorientable smooth four-manifold
fundamental group Z
orientation double cover S3 x S1
canonical throat S2 x S1
ordinary H3 torsion Z2
ordinary H4 = 0
twisted top class Z
Euler characteristic 0
```

The local conformal metric comes from

```text
|x|^-2 g_Euclidean = du^2 + g_S3,
```

which is invariant under radial dilation.  Multiplying the descended metric by
an overall `L^2` leaves one dimensionless modulus `T` and one absolute scale
`L`.

### Immediate consequence

Topology and the mapping-torus period may determine dimensionless ratios, but
an overall metric rescaling remains possible until dynamics selects `L`.

## D2 — First new no-go: ordinary Hopf descent fails

A naive proposal was to identify the LL auxiliary `U(1)` directly with the
standard Hopf bundle

```text
S1 -> S3 -> S2
```

and descend it through the orientation-reversing monodromy.

For a symmetry of the primitive Hopf bundle, Chern-class compatibility forces
the orientation action on the circle fiber to equal the orientation action on
the base.  The product orientation therefore changes by the product of two
equal signs and is preserved.

Hence:

```text
orientation-reversing S3 monodromy
  cannot preserve the ordinary primitive principal-U(1) Hopf bundle.
```

Lean theorem:

```text
P0EFTJanusHopfBundleOrientationNoGo.lean
```

This eliminates the simplest version of “the global Hopf connection is already
the LL gauge field.”

### Surviving exits

1. a monopole line bundle intrinsic to the `S2` throat;
2. a twisted `O(2) = U(1) semidirect Z2` gauge bundle;
3. a family of Hopf structures varying around the mapping-torus circle.

The first route is currently the cleanest.

## D3 — Emergent throat monopole

The throat

```text
Sigma = S2 x S1
```

has exactly the ingredients missing from the direct bulk descent:

- `S2` supports an integral monopole class;
- `S1` supplies the compact transgression circle;
- PT exchanges the signed classes `n <-> -n`.

The new Lean module proves:

```text
least nonzero |c1|  =>  |c1| = 1,
primitive boundary class x primitive circle winding
  => primitive throat monopole class.
```

Module:

```text
P0EFTJanusThroatMonopoleEmergence.lean
```

This fixes the integer sector but not the dimensionful gauge normalization.
The physical curvature still has the form

```text
F_physical = q_LL * F_integral,
```

and Program A or a spectral law must derive `q_LL`.

## D4 — Pin audit

The projective `RP4` candidate and the twisted-Hopf candidate need not have the
same Pin obstruction pattern.

The obstruction formulas are

```text
Pin+ : w2 = 0,
Pin- : w2 + w1^2 = 0.
```

The Lean audit proves two distinct patterns:

```text
w2=0, w1^2=1  => Pin+ only       (RP4 pattern)
w2=0, w1^2=0  => Pin+ and Pin-   (twisted-Hopf target pattern)
```

Module:

```text
P0EFTJanusPinObstructionAudit.lean
```

For the twisted-Hopf manifold, the intended geometric proof is:

1. realize it as the unit-sphere bundle of a rank-four bundle over `S1`;
2. use the stable tangent relation to show `w2=0`;
3. compute `H^2(-;Z2)=0` from the mapping-torus cellular model;
4. conclude `w1^2=0`.

If both Pin signs exist, topology alone does not choose the physical fermionic
lift.  The world-volume anomaly and time-reversal convention must select it.

## D5 — Spectral route to a dimensionless alpha ratio

Give the throat the product metric

```text
Sigma_(L,T) = S2_L x S1_(L*T).
```

The first nonconstant scalar modes are

```text
lambda_S2 = 2/L^2,
lambda_S1 = (2*pi/(L*T))^2.
```

A candidate spectral-isotropy law

```text
lambda_S2 = lambda_S1
```

fixes the dimensionless modulus:

```text
T^2 = 2*pi^2.
```

Suppose the renormalized LL charge is locked to the sphere gap:

```text
q_LL * L^2 = 2*c_q,
```

and primitive flux gives

```text
16*q_LL^2*A^4 = 1.
```

Then the branch proves the cleared ratio law

```text
64*c_q^2*A^4 = L^4.
```

For unit computed normalization `c_q=1`:

```text
8*A^2 = L^2,
```

or, for positive lengths,

```text
A/L = 1/(2*sqrt(2)).
```

Lean module:

```text
P0EFTJanusSpectralIsotropyAlphaRatio.lean
```

This is the first Program-D candidate that fixes an `alpha/geometric-length`
ratio without fixing the absolute length.

### What remains physical

The following statements are not yet derived:

- that the product throat metric is dynamically selected;
- that equality of the two first spectral modes is the correct vacuum law;
- that the first scalar mode sets the LL charge;
- that `c_q=1` in the convention matched to the bulk charge.

Each is kept as an explicit gate.

## D6 — Genuine Z4 interpretation

The spacetime fold exchange is geometric `Z2`.  A genuine physical `Z4` is a
fermionic central extension:

```text
g^2 = (-1)^F,
g^4 = 1,
g^2 != 1.
```

The inherited twisted-Hopf monodromy module implements this arithmetic in
`ZMod 4`.  A complete proof still requires a global Pin lift of the mapping
torus and an identification of its square with fermion parity.

Thus:

```text
Z2 geometry
  + selected Pin lift
  -> candidate Z4 action on fermions.
```

It is not a consequence of the twofold cover alone.

## D7 — Interfaces to the other programs

### D -> A: quantum world-volume

Program D should derive:

```text
compact throat gauge bundle
field content
spectral operator
allowed Chern-Simons level
UV boundary condition
```

Program A must then compute the renormalized effective action and stable vacuum.

### D -> B: nonlinear bimetric action

Program D should derive the common manifold comparison, throat embedding,
orientations and PT action on boundary states.  Program B must derive the full
variational action, constraints and null junction.

### D -> C: charge compatibility

The throat circle and primitive monopole class supply the degree-compatible
transgression route.  Program C must prove equality of large-gauge periods and
of the dimensionful bulk/boundary charge units.

## D8 — Milestone matrix

| Milestone | Deliverable | Current status |
| --- | --- | --- |
| **D1** | twisted-Hopf smooth quotient and invariants | scaffold plus cellular algebra |
| **D2** | direct Hopf `U(1)` descent test | **no-go proved** |
| **D3** | primitive throat monopole and circle transport | **integer algebra proved** |
| **D4** | Pin obstruction pattern | algebra proved; geometric classes open |
| **D5** | spectral modulus and alpha-ratio candidate | **conditional theorem proved** |
| **D6** | global Pin-lifted `Z4` | finite arithmetic proved; global lift open |
| **D7** | geometry-derived QFT | open research theorem |
| **D8** | geometry-derived bimetric junction | open research theorem |
| **D9** | absolute alpha | requires D7, D8 and charge normalization |

## D9 — Falsification criteria

Program D should be rejected or revised if any of the following is proved:

1. the proposed mapping torus cannot carry the required smooth/conformal
   Lorentzian continuation;
2. no physically acceptable Pin lift exists;
3. every compact throat gauge construction conflicts with PT or anomaly
   cancellation;
4. the spectral vacuum is unstable or gauge/scheme dependent;
5. the positive-kinetic bimetric completion cannot recover the Janus weak-field
   sign matrix;
6. the bulk/boundary charge periods cannot be matched.

## References anchoring the program

- Ornea and Verbitsky, *Non-linear Hopf manifolds are locally conformally
  Kahler*, arXiv:2202.12398 — Hopf quotients and locally conformal geometry.
- Dai and Freed, *Eta-Invariants and Determinant Lines*, arXiv:hep-th/9405012 —
  eta invariants, determinant lines, gluing and global anomalies.
- Jenquin, *Classical Chern-Simons on manifolds with spin structure*,
  arXiv:math/0504524 — spin Chern-Simons as an eta-invariant refinement.
- Witten, *Fermion Path Integrals And Topological Phases*, arXiv:1508.04715 —
  Pin structures, time reversal and fermionic anomalies.

## Honest conclusion

Program D has begun with one negative and two positive results:

```text
negative:
  the ordinary global Hopf U(1) does not descend through the orientation-
  reversing monodromy as initially imagined;

positive:
  the canonical S2 x S1 throat supports the correct primitive integer and
  compact-circle structure;

positive, conditional:
  a spectral lock can fix A/L even though topology cannot fix L absolutely.
```

The next theorem-level target is to construct the twisted-Hopf manifold and its
stable tangent bundle in Mathlib-level topology, then prove the proposed mod-two
cohomology and Pin statements without using opaque `Prop` fields.
