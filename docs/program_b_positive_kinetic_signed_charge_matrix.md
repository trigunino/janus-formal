# Program B — positive kinetic / signed-charge Newtonian matrix

- Program: **B**
- Stable ID: `B-POSKIN-SIGNED-NEWTON`
- Evidence: **T** (Lean theorem)
- Dependencies: positive PT-flat spin-2 kinetic gate and signed matter-charge gate
- Lean target:
  `P0EFTJanusSignedMatterChargeNewtonianLimit.lean`

## Result

The reduced model admits simultaneously:

- two strictly positive spin-2 kinetic directions off the origin;
- attraction in the positive-positive sector;
- attraction in the negative-negative sector;
- repulsion in both mixed-sector orderings.

Thus the Janus Newtonian sign matrix does not algebraically require a negative
Einstein–Hilbert kinetic coefficient. The sign can be carried by a PT-odd
matter gravitational charge.

The same gate now supplies a common reduced action mechanism. A mediator with
positive quadratic coefficient and linear coupling to the total signed source
has stationary reduced energy

```text
-J^2/(2 k),  k > 0.
```

After subtracting source self-energies, its cross term is exactly

```text
-(q1 q2) m1 m2 / k,
```

so one common variational functional reproduces the complete sign table. This
closes reduced common-action integrability; it is not yet a covariant metric
or matter action.

## Remaining physical atom

This does not derive the signed charge from a covariant matter action. Closure
still requires positive matter Hamiltonians, compatible Bianchi/Noether
identities, an explicit equivalence-principle scope and nonlinear/radiative
stability.

## Equivalence-principle consequence

The gate also proves that PT-related signed charges with the same positive
inertial mass accelerate in opposite directions in one fixed mediator field.
Demanding charge-independent free fall across both sectors forces that field
to vanish. Therefore a viable covariant completion must choose explicitly:

- a sectorwise equivalence principle with separate PT-related metrics/fields;
- or a simultaneous PT transformation of the background field;
- or a different derived coupling that preserves universal free fall.

A single nonzero background field with universal cross-sector free fall is
incompatible with the reduced signed-charge ansatz.

The reduced gate now closes the natural PT-sectorwise alternative: if PT
reverses both the gravitational charge and the mediator field, then the
test-body acceleration and the source-field coupling are invariant. Thus a
future covariant action should implement a PT-odd field/connection map between
the two sectors, rather than compare both charges inside one unchanged field.
The positive reduced mediator action and its stationary solution are both
equivariant under this simultaneous PT transformation.

## Reduced Noether and integrability closure

A translation-invariant common pair potential has now been added. Its two
Euler sources are exactly opposite, giving the reduced diagonal Noether
exchange identity. Their mixed variations are reciprocal, so the interaction
passes the reduced common-action integrability test. This does not yet provide
the determinant-weighted covariant Bianchi identity for two metrics.

## Failure criterion

Reject the branch if no common covariant action produces the PT-odd source
coupling while preserving the bimetric constraint algebra and positive matter
energy.
