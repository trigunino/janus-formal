# Program D8 — Mapping-Torus, Orbifold and Representation Audit

## Purpose

Program D8 steps back from the spectral calculations and audits the object from
which they are supposed to arise.

The candidate used throughout Program D is

```text
J(T,rho) = (S3 x R) / ((x,u) ~ (rho(x),u+T)),
```

where `rho` is an orientation-reversing involution and `T != 0`.

The central questions are:

1. Is this quotient really an orbifold with a singular throat?
2. What is its fundamental group?
3. Does topology force a `Z4` monodromy?
4. Can that monodromy force a rank-five field multiplet?
5. What does the global two-to-one structure actually compare?

## Evidence levels

| Code | Meaning |
| --- | --- |
| **T** | exact theorem/algebra checked in Lean |
| **C** | standard topological consequence, pending full Mathlib construction |
| **G** | geometric construction target |
| **N** | no-go or correction |
| **P** | physical interpretation still requiring derivation |

## 1. The quotient action is free

The integer action has the form

```text
g^n(x,u) = (rho^n(x), u+n*T).
```

For `n != 0` and `T != 0`, equality `g^n(x,u)=(x,u)` would imply

```text
n*T = 0,
```

which is impossible.

Lean theorem:

```text
P0EFTJanusMappingTorusFreeActionAudit
  .nonzero_integer_step_has_no_fixed_point
```

### Consequence

The translation removes the fixed-point isotropy of `rho`.  The quotient is a
**smooth mapping-torus candidate**, not an orbifold whose equator is a singular
fixed locus.

The algebraic unit `S3` and equatorial `S2` are identified with Mathlib's
analytic spheres. Their covering-induced quotient atlases are now actual
analytic manifolds: the quotient projections are analytic local
diffeomorphisms and the descended throat inclusion is `C∞`. Time reversal is
an analytic involutive diffeomorphism on both quotients and still intertwines
the throat inclusion.

The word `orbifold` may still be used informally in the Janus literature, but it
must not be used as a mathematical claim of local finite isotropy for this
specific quotient.

## 2. The throat is embedded and one-sided

The reflection fixed set in the `S3` fiber is the equatorial `S2`.  On that set,
the mapping-torus generator acts only by

```text
u -> u+T,
```

so the embedded throat target is

```text
Sigma = S2 x S1_T.
```

However, the reflection reverses the normal coordinate.  Going once around the
throat circle sends a local normal vector `v` to `-v`.  A globally invariant
nonzero normal vector would satisfy `v=-v`, hence vanish.

Lean theorems:

```text
normal_transport_two_loops
invariant_normal_is_zero
exchange_side_has_no_fixed_point
exchange_side_twice
```

### Geometric interpretation

`Sigma` is an orientable three-manifold with a nontrivial normal line bundle.
It is therefore a **one-sided hypersurface** in the nonorientable mapping torus.

The two Janus worlds are globally separated only in the orientation double
cover.  In the quotient, the complement of the one-sided throat is expected to
be connected.

The actual set-level frontier is stronger than that heuristic alone. The
equatorial complement in the concrete `S3` is exactly the disjoint union of
two nonempty open sign sides. Reflection and one deck iterate exchange those
sides. After quotienting, the image of either side is the entire effective
throat complement, so the two quotient images coincide; PT preserves this
complement. Explicit normalized affine paths to the two poles prove that both
sign sides are path connected. The positive cover side is path connected and
its continuous quotient image is exactly the effective throat complement;
therefore that complement is path connected and connected. The two sign sides
are moreover identified exactly with the connected components of the positive
and negative poles in the sphere complement.

The fixed-throat normal local system now has an effective topological model:
the quotient by even windings maps to the original throat as a covering. The
half-period translation descends to a continuous, involutive, fixed-point-free
deck map; each fiber is equivalent to `ZMod 2`. Pulling the associated normal
line back to this cover yields an explicit homeomorphism with the product by
`R`. The quotient throat inclusion is additionally a closed topological
embedding, its manifold differential is injective at every point, and the
quotient of the ambient tangent space by its derivative range has real
dimension one. The exact local covering sections and their unique integer
transition cocycle now construct an actual real rank-one `VectorBundle` on the
effective throat. Its sign transitions are locally constant, hence analytic;
one deck circuit acts by `-id`. Every constructed fiber is noncanonically
linearly equivalent to the corresponding differential normal quotient.
The compact fundamental strips `S³ × [0,|T|]` and `S² × [0,|T|]`
project continuously and surjectively, proving compactness of both actual
effective quotients.

The remaining smooth-embedding frontier is explicit: Mathlib's
`IsSmoothEmbedding` instance is not proved, the pointwise normal equivalences
have not been assembled into a globally smooth equivalence with the
differential normal quotient, and the nonnull/null/joint strata remain open.

Lean theorems:

```text
orientationDoubleToThroat_isCoveringMap
orientationDouble_fiber_equiv_two
orientationDeck_involutive
orientationDeck_ne_self
orientationNormalTrivialization
orientationDouble_normal_pullback_closure
sphere_complement_eq_two_sides
sphereReflection_image_positive
one_vadd_mem_negative_iff
mappingTorusMk_preimage_effectiveThroat
image_positiveCoverSide_eq_effective_complement
image_negativeCoverSide_eq_effective_complement
quotient_images_of_sides_coincide
reflectedSpherePT_mem_effective_complement_iff
positiveSphereSide_isPathConnected
negativeSphereSide_isPathConnected
connectedComponentIn_throat_complement_positivePole
connectedComponentIn_throat_complement_negativePole
positiveCoverSide_isPathConnected
effectiveThroat_complement_isPathConnected
effectiveThroat_complement_isConnected
reflectedSpherePT_contMDiff
fixedThroatPT_contMDiff
reflectedSpherePTDiffeomorph
fixedThroatPTDiffeomorph
fixedThroatQuotientInclusion_isClosedEmbedding
mfderiv_fixedThroatQuotientInclusion_injective
mfderiv_fixedThroatQuotientInclusion_normal_finrank
fixedThroatNormalVectorBundleCore
fixedThroatNormalFiber_isVectorBundle
fixedThroatNormalVectorBundleCore_isContMDiff
fixedThroatNormalFiber_isContMDiffVectorBundle
fixedThroatNormalFiber_equiv_differentialNormal
localTransitionWinding_one_loop
one_loop_coordChange_eq_neg_id
```

## 3. What the two-to-one ratio means

Under a deck-invariant metric, the two sides upstairs have equal volume:

```text
Vol(A) = Vol(B).
```

The degree-two covering gives

```text
Vol(orientation cover) = 2 * Vol(quotient).
```

Lean theorems:

```text
deck_symmetry_gives_one_to_one_world_ratio
orientation_cover_is_twice_quotient_volume
```

### Correction

The topology produces a `2:1` ratio between **cover and quotient**, not between
world A and world B.  A physical `2:1` asymmetry between the two worlds would
require symmetry breaking, a weighted measure or additional dynamics.

## 4. Fundamental group frontier

Once the mapping torus is constructed as an `S3` bundle over `S1`, the long
exact homotopy sequence and `pi1(S3)=0` give

```text
pi1(J) = Z.
```

This is a standard topological consequence, but the repository still needs a
concrete Mathlib-level fibration/quotient construction before promoting it to a
native theorem.

## 5. Order-four holonomy is not an order-four fundamental group

For the cyclic loop label `n in Z`, the two candidate fourth-root holonomies are

```text
n ->  n mod 4,
n -> -n mod 4.
```

At the generator they give phases `1` and `3`.  Both square to the half-turn
`2`, and four loops map to zero phase.

But the loop `4 in Z` is not the null loop.  Therefore

```text
holonomy image has order four
```

does **not** imply

```text
pi1(J) = Z4.
```

Lean theorems:

```text
phase_doubles_to_half_turn_iff
orientation_generator_lifts_are_exactly_two
orientation_lift_squares_to_half_turn
orientation_lift_fourth_power_trivial
four_loops_are_not_null_in_the_cyclic_group
```

### Best current interpretation

The geometry has an orientation character

```text
w1 : Z -> Z2.
```

It admits two fourth-root lifts, exchanged by inversion/PT:

```text
Z -> Z4,
1 -> 1  or  1 -> 3.
```

This explains why quarter and three-quarter phases are natural.  It does not by
itself select a field representation or a bundle rank.

## 6. Cyclic topology does not select rank five

The same generator phase can be assigned to a flat sector of any externally
chosen rank.

Lean theorem:

```text
every_rank_supports_the_same_quarter_phase
```

In particular, rank one and rank five carry the identical quarter holonomy:

```text
same_quarter_holonomy_allows_rank_one_and_five
```

At the mathematical representation-theory level, finite-dimensional complex
irreducible representations of an abelian cyclic group are one-dimensional.
Thus a rank-five irreducible cannot be forced by `pi1(J)=Z` alone.

### Consequence for the number five

The number five must arise from additional data, for example:

- five flavors;
- an index theorem applied to a rank-five bundle;
- a bulk four-dimensional field reduced to the throat;
- a gauge/ghost supertrace;
- or a genuinely additional nonabelian internal symmetry.

It is not a consequence of the cyclic mapping-torus fundamental group.

## 7. Pin convention audit

In the standard Clifford convention:

```text
Pin+ reflection lift: u^2 = +1,
Pin- reflection lift: u^2 = -1.
```

The second pattern is the direct group-level order-four pattern because
`u^4=1` while `u^2=-1`.

Lean module:

```text
P0EFTJanusPinReflectionSquareConventionAudit
```

Physics papers may label Euclidean Pin structures using the square of an
antiunitary Lorentzian time-reversal operator.  Program D must therefore derive
and document the Euclidean/Lorentzian dictionary rather than infer a `Pin+` or
`Pin-` label from an unstated convention.

## 8. Revised candidate matrix

| Candidate | Verdict | Reason |
| --- | --- | --- |
| Smooth twisted mapping torus | **retained** | free action, natural one-sided throat and orientation cover |
| Throat as orbifold singular locus of the translated quotient | **rejected** | nonzero translation removes isotropy |
| Two worlds as globally separate components downstairs | **rejected** | they are exchanged around the one-sided throat |
| `2:1` as world-A/world-B volume ratio | **rejected from topology alone** | deck symmetry gives `1:1`; `2:1` is cover/quotient |
| `pi1 = Z4` | **rejected** | expected `pi1 = Z`; only a holonomy image can be `Z4` |
| Quarter holonomy as a fourth-root of orientation parity | **strong candidate** | exactly two lifts, phases `1` and `3` |
| Rank five forced by mapping-torus topology | **rejected** | cyclic holonomy supports arbitrary external rank |
| Additional rank-five/internal symmetry | **open** | must be derived separately |
| Genuine orbifold with finite isotropy | **alternative program** | requires changing the quotient construction |

## 9. Three honest continuation programs

### D8-A — Smooth mapping-torus completion

1. construct the proper free `Z` action;
2. form the smooth quotient;
3. prove the `S3 -> J -> S1` fibration;
4. calculate `pi1(J)=Z`;
5. construct the one-sided `S2 x S1` throat and its Möbius normal line;
6. promote the topological even-winding throat cover and trivial normal
   pullback to smooth differential bundles;
7. reuse the proved path-connected sides and connected quotient complement in
   the smooth throat embedding.

This is the preferred continuation of the current geometry.

### D8-B — True orbifold alternative

Define a different quotient with actual finite isotropy, then recompute:

- local models;
- orbifold fundamental group;
- singular strata;
- Pin/orbifold spin structures;
- index and eta invariants.

This would be a new geometry, not a reinterpretation of the existing free
mapping torus.

### D8-C — Additional internal bundle

Retain the smooth mapping torus and add a separately derived principal bundle or
group extension whose representations supply the field multiplet.  This route
must state why the internal group exists and why its rank/representation is
selected.

## 10. Terminal theorem queue

1. Promote the constructed topological quotient manifold atlas to `C∞`.
2. Prove the mapping-torus fibration and `pi1(J)=Z` in Lean.
3. Promote the constructed topological normal-line quotient and its trivial
   even-cover pullback to a smooth differential `VectorBundle`.
4. Reuse the identified connected components and connected quotient complement
   in the smooth throat embedding and boundary analysis.
5. Classify flat `Z4` lifts of the orientation local system globally.
6. Fix the Pin reflection convention and derive the physical PT square.
7. Formalize the theorem that complex irreducible cyclic representations are
   one-dimensional.
8. Derive any rank-five flavor/internal bundle from independent geometry or
   dynamics.
9. Rebuild the D7 determinant only after this field-content audit.

## Final conclusion

The step back changes the frontier substantially:

```text
The current quotient is best viewed as a smooth nonorientable mapping torus
with a one-sided throat, not as an orbifold singularity.
```

Its topology naturally explains:

- a two-sheeted orientation cover;
- side exchange after one circuit;
- a nontrivial orientation character;
- two quarter-phase `Z4` lifts.

It does **not** explain:

- a rank-five multiplet;
- a nonabelian internal representation;
- a `2:1` asymmetry between the two worlds;
- or an absolute physical scale.

Those are now cleanly separated research obligations rather than hidden
consequences of the word `orbifold`.
