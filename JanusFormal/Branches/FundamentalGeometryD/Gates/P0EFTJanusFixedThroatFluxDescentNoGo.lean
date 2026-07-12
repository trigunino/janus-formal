import Mathlib

namespace JanusFormal
namespace P0EFTJanusFixedThroatFluxDescentNoGo

set_option autoImplicit false

structure FluxDescentData where
  fluxInteger : ℤ
  baseOrientationSign : ℤ
  fiberChargeSign : ℤ
  baseSignSquare : baseOrientationSign ^ 2 = 1
  fiberSignSquare : fiberChargeSign ^ 2 = 1
  descentLaw :
    fluxInteger =
      baseOrientationSign * fiberChargeSign * fluxInteger

theorem fixed_base_with_charge_conjugation_forces_zero_flux
    (s : FluxDescentData)
    (hBase : s.baseOrientationSign = 1)
    (hFiber : s.fiberChargeSign = -1) :
    s.fluxInteger = 0 := by
  have hDescent := s.descentLaw
  rw [hBase, hFiber] at hDescent
  norm_num at hDescent
  omega

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

theorem conjugate_nonzero_flux_forces_base_orientation_reversal
    (s : FluxDescentData)
    (hFlux : s.fluxInteger ≠ 0)
    (hFiber : s.fiberChargeSign = -1) :
    s.baseOrientationSign = -1 := by
  have hProduct :=
    nonzero_flux_requires_matching_orientation_actions s hFlux
  rw [hFiber] at hProduct
  nlinarith

structure FixedThroatFluxExitStatus where
  pairedFluxSectorsConstructed : Prop
  orientationReversingS2MonodromyConstructed : Prop
  ptActionSeparatedFromCircleHolonomy : Prop
  atLeastOneNonzeroFluxExitDerived : Prop


def fixedThroatFluxNoGoExited
    (s : FixedThroatFluxExitStatus) : Prop :=
  (s.pairedFluxSectorsConstructed \/
    s.orientationReversingS2MonodromyConstructed \/
    s.ptActionSeparatedFromCircleHolonomy) /\
  s.atLeastOneNonzeroFluxExitDerived

end P0EFTJanusFixedThroatFluxDescentNoGo
end JanusFormal
