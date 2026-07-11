import Mathlib

namespace JanusFormal
namespace P0EFTJanusFixedThroatFluxDescentNoGo

set_option autoImplicit false

/--
Integer flux descent through a throat mapping torus.

`baseOrientationSign` records the action on the orientation of `S2`, while
`fiberChargeSign` records whether the `U(1)` charge is conjugated.  Each sign is
`+1` or `-1`.  Descent requires the flux integral to be invariant under their
product.
-/
structure FluxDescentData where
  fluxInteger : ℤ
  baseOrientationSign : ℤ
  fiberChargeSign : ℤ
  baseSignSquare : baseOrientationSign ^ 2 = 1
  fiberSignSquare : fiberChargeSign ^ 2 = 1
  descentLaw :
    fluxInteger =
      baseOrientationSign * fiberChargeSign * fluxInteger

/-- A pointwise-fixed `S2` and charge conjugation force zero flux. -/
theorem fixed_base_with_charge_conjugation_forces_zero_flux
    (s : FluxDescentData)
    (hBase : s.baseOrientationSign = 1)
    (hFiber : s.fiberChargeSign = -1) :
    s.fluxInteger = 0 := by
  rw [hBase, hFiber] at s.descentLaw
  norm_num at s.descentLaw
  omega

/-- Any nonzero descended flux requires the product of the two signs to be `+1`. -/
theorem nonzero_flux_requires_matching_orientation_actions
    (s : FluxDescentData)
    (hFlux : s.fluxInteger ≠ 0) :
    s.baseOrientationSign * s.fiberChargeSign = 1 := by
  have hFactor :
      (1 - s.baseOrientationSign * s.fiberChargeSign) *
        s.fluxInteger = 0 := by
    nlinarith [s.descentLaw]
  have hFirst :
      1 - s.baseOrientationSign * s.fiberChargeSign = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right hFlux
  linarith

/-- Charge conjugation with nonzero flux forces orientation reversal of `S2`. -/
theorem conjugate_nonzero_flux_forces_base_orientation_reversal
    (s : FluxDescentData)
    (hFlux : s.fluxInteger ≠ 0)
    (hFiber : s.fiberChargeSign = -1) :
    s.baseOrientationSign = -1 := by
  have hProduct :=
    nonzero_flux_requires_matching_orientation_actions s hFlux
  rw [hFiber] at hProduct
  nlinarith

/--
The canonical fixed throat `S2 x S1` therefore has three honest exits:

1. keep the monopole on the orientation double cover as a PT-paired `+n/-n`
   sector without descending one line bundle;
2. replace the pointwise-fixed `S2` monodromy by an orientation-reversing action;
3. let PT act outside the mapping-circle holonomy rather than as fiber charge
   conjugation along that circle.
-/
structure FixedThroatFluxExitStatus where
  pairedFluxesOnOrientationCoverConstructed : Prop
  orientationReversingS2MonodromyConstructed : Prop
  ptActionSeparatedFromCircleHolonomy : Prop
  atLeastOneNonzeroFluxExitDerived : Prop


def fixedThroatFluxNoGoExited
    (s : FixedThroatFluxExitStatus) : Prop :=
  (s.pairedFluxesOnOrientationCoverConstructed \/
    s.orientationReversingS2MonodromyConstructed \/
    s.ptActionSeparatedFromCircleHolonomy) /\
  s.atLeastOneNonzeroFluxExitDerived

end P0EFTJanusFixedThroatFluxDescentNoGo
end JanusFormal
