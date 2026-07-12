import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedO2FluxDescent

set_option autoImplicit false

/--
Descent signs for a flux with a possibly twisted coefficient system.

The ordinary `U(1)` attempt has coefficient sign `+1`.  An `O(2)` or orientation-
local-system refinement can contribute an additional sign `-1`.
-/
structure TwistedFluxDescent where
  fluxInteger : ℤ
  baseOrientationSign : ℤ
  fiberChargeSign : ℤ
  coefficientTwistSign : ℤ
  descentLaw :
    fluxInteger =
      baseOrientationSign * fiberChargeSign *
        coefficientTwistSign * fluxInteger

/-- Pointwise-fixed base plus charge conjugation fails for ordinary coefficients. -/
theorem ordinary_coefficients_force_zero
    (s : TwistedFluxDescent)
    (hBase : s.baseOrientationSign = 1)
    (hFiber : s.fiberChargeSign = -1)
    (hCoefficient : s.coefficientTwistSign = 1) :
    s.fluxInteger = 0 := by
  have h := s.descentLaw
  rw [hBase, hFiber, hCoefficient] at h
  norm_num at h
  omega

/--
A second sign from a twisted coefficient system cancels charge conjugation, so
any integer flux satisfies the descent equation.
-/
theorem twisted_coefficients_restore_descent
    (n : ℤ) :
    n = (1 : ℤ) * (-1) * (-1) * n := by
  ring

/-- In particular a primitive nonzero flux descends algebraically. -/
theorem primitive_twisted_flux_descends :
    (1 : ℤ) = (1 : ℤ) * (-1) * (-1) * 1 := by
  norm_num

/-- The total sign of the fixed-base, conjugate-fiber, twisted-coefficient action is `+1`. -/
theorem o2_total_monodromy_sign_is_positive :
    (1 : ℤ) * (-1) * (-1) = 1 := by
  norm_num

/--
This algebra identifies the correct escape from the ordinary Hopf-line-bundle
no-go: the global gauge object must be an `O(2)` bundle, a real rank-two bundle,
or a `U(1)` connection valued in a sign local system.  Constructing that bundle
and its differential cohomology class remains a geometric theorem.
-/
structure TwistedO2GaugeStatus where
  signLocalSystemDerived : Prop
  o2PrincipalBundleConstructed : Prop
  twistedIntegralChernClassDefined : Prop
  nonzeroPrimitiveFluxDerived : Prop
  connectionAndCurvatureConstructed : Prop
  restrictionToThroatMatched : Prop
  ptActionMatched : Prop
  llAuxiliaryGaugeFieldDerived : Prop


def twistedO2GaugeClosed (s : TwistedO2GaugeStatus) : Prop :=
  s.signLocalSystemDerived /\
  s.o2PrincipalBundleConstructed /\
  s.twistedIntegralChernClassDefined /\
  s.nonzeroPrimitiveFluxDerived /\
  s.connectionAndCurvatureConstructed /\
  s.restrictionToThroatMatched /\
  s.ptActionMatched /\
  s.llAuxiliaryGaugeFieldDerived

end P0EFTJanusTwistedO2FluxDescent
end JanusFormal
