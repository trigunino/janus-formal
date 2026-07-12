import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusFiniteSphereBridgeMatching
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusLLBraneAuxiliaryFluxClosure

namespace JanusFormal
namespace P0EFTJanusConditionalAlphaSpectrumClosure

set_option autoImplicit false

open P0EFTJanusFiniteSphereBridgeMatching
open P0EFTJanusLLBraneAuxiliaryFluxClosure

/--
Compatibility data joining the finite FLRW boundary, the Schwarzschild PT
bridge and the LL-brane world-volume flux sector.
-/
structure ConditionalAlphaSpectrum where
  bridgeMatching : FiniteSphereBridgeMatching
  llMatching : LLTensionFluxMatching
  sameBridgeRadius :
    llMatching.throatRadius = bridgeMatching.bridgeRadius

/-- The exact-solution length is the LL-brane throat radius. -/
theorem alpha_squared_length_eq_ll_throat
    (s : ConditionalAlphaSpectrum) :
    s.bridgeMatching.alphaSquaredLength = s.llMatching.throatRadius := by
  calc
    s.bridgeMatching.alphaSquaredLength =
        s.bridgeMatching.bridgeRadius :=
      alpha_squared_length_eq_bridge_radius s.bridgeMatching
    _ = s.llMatching.throatRadius := s.sameBridgeRadius.symm

/-- Primitive LL flux gives the conditional `alpha^2` spectrum. -/
theorem primitive_charge_fixes_alpha_fourth_power
    (s : ConditionalAlphaSpectrum) :
    16 * s.llMatching.chargeUnit ^ 2 *
        s.bridgeMatching.alphaSquaredLength ^ 4 = 1 := by
  exact matched_alpha_charge_law
    s.llMatching.toSphericalAuxiliaryFlux
    s.bridgeMatching.alphaSquaredLength
    (alpha_squared_length_eq_ll_throat s)

/-- The LL-brane tension law transports to the cosmological exact-solution scale. -/
theorem tension_fixes_alpha_linearly
    (s : ConditionalAlphaSpectrum) :
    8 * s.llMatching.piConstant * s.llMatching.chiMagnitude *
        s.bridgeMatching.alphaSquaredLength = 1 := by
  rw [alpha_squared_length_eq_ll_throat s]
  exact s.llMatching.tensionRadiusLaw

/-- The flux unit and tension remain tied by the exact classical relation. -/
theorem charge_tension_relation_on_janus_scale
    (s : ConditionalAlphaSpectrum) :
    s.llMatching.chargeUnit ^ 2 =
      256 * s.llMatching.piConstant ^ 4 *
        s.llMatching.chiMagnitude ^ 4 :=
  charge_tension_relation s.llMatching

/-- The global mass constant is fixed relative to the bridge mass. -/
theorem global_mass_map_on_conditional_spectrum
    (s : ConditionalAlphaSpectrum) :
    4 * s.bridgeMatching.piConstant *
        s.bridgeMatching.globalMassConstant +
      3 * s.bridgeMatching.bridgeMass = 0 :=
  global_mass_to_bridge_mass_map s.bridgeMatching

/--
Everything dimensionless and relational is now fixed.  Absolute no-fit closure
requires one dimensionful normalization, chosen here as the LL auxiliary charge
unit; choosing the tension instead is equivalent by the charge-tension theorem.
-/
structure AbsoluteScaleInput where
  chargeUnitMagnitudeDerivedFromJanusAction : Prop
  chargeUnitIndependentOfObservedCosmology : Prop
  chargeUnitCompatibleWithBulkInflow : Prop
  signedBimetricJunctionDerived : Prop


def absoluteNoFitInputClosed (s : AbsoluteScaleInput) : Prop :=
  s.chargeUnitMagnitudeDerivedFromJanusAction /\
  s.chargeUnitIndependentOfObservedCosmology /\
  s.chargeUnitCompatibleWithBulkInflow /\
  s.signedBimetricJunctionDerived


theorem missing_charge_unit_is_the_terminal_scale_blocker
    (s : AbsoluteScaleInput)
    (hMissing : Not s.chargeUnitMagnitudeDerivedFromJanusAction) :
    Not (absoluteNoFitInputClosed s) := by
  intro h
  exact hMissing h.1

end P0EFTJanusConditionalAlphaSpectrumClosure
end JanusFormal
