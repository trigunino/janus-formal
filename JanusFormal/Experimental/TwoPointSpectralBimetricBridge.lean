import JanusFormal.Experimental.TwoPointSpectralJanus
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPositiveBimetricLinearSpectrum

/-!
# Experimental bridge from the two-point spectral seed to Programs A and B

This file is intentionally isolated from every supported program head.
It separates the exact quadratic compatibility with Program B from the
conditional scale identifications still required from Programs A and B.
-/

namespace JanusFormal
namespace ExperimentalTwoPointSpectralBimetricBridge

set_option autoImplicit false

open ExperimentalTwoPointSpectralJanus
open P0EFTJanusPositiveBimetricLinearSpectrum
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- The finite spectral action is exactly B's reduced relative-mode potential
when its mass coefficient is identified with the squared link. -/
theorem spectral_action_is_bimetric_relative_potential
    (link hPlus hMinus : ℝ) :
    spectralLinkAction link hPlus hMinus =
      relativeModePotential (link ^ 2) hPlus hMinus := by
  rw [spectralLinkAction_formula]
  rfl

/-- With unequal kinetic weights, the link induces B's physical massive pole. -/
theorem spectral_link_weighted_mass_formula
    (planckPlusSquared planckMinusSquared link : ℝ) :
    weightedRelativeEigenvalue
        planckPlusSquared planckMinusSquared (link ^ 2) =
      link ^ 2 *
        (1 / planckPlusSquared + 1 / planckMinusSquared) := by
  rfl

/-- Conditional normalization bridge to the PT-flat Fierz--Pauli coefficient. -/
theorem pt_mass_identification
    (link beta1 beta2 : ℝ)
    (hBridge : link ^ 2 =
      fpMassCombination (ptFlatCoefficients beta1 beta2)) :
    link ^ 2 = 2 * (beta1 + beta2) := by
  rw [hBridge, pt_flat_fp_mass_combination]

/-- The still-missing Program-A datum: a condensate-to-link normalization. -/
structure CondensateLinkBridge where
  condensate : ℝ
  normalization : ℝ
  link : ℝ
  link_from_condensate : link = normalization * condensate

/-- If Program A supplies the bridge, its condensate fixes the quadratic
relative-mode coefficient rather than merely its shape. -/
theorem condensate_fixes_relative_coefficient
    (bridge : CondensateLinkBridge) :
    bridge.link ^ 2 =
      bridge.normalization ^ 2 * bridge.condensate ^ 2 := by
  rw [bridge.link_from_condensate]
  ring

/-- Combined A-to-B target.  This theorem only propagates the two explicit
bridge assumptions; it does not claim that either has been derived. -/
theorem condensate_to_pt_mass_target
    (bridge : CondensateLinkBridge)
    (beta1 beta2 : ℝ)
    (hBimetric : bridge.link ^ 2 =
      fpMassCombination (ptFlatCoefficients beta1 beta2)) :
    bridge.normalization ^ 2 * bridge.condensate ^ 2 =
      2 * (beta1 + beta2) := by
  rw [← condensate_fixes_relative_coefficient bridge]
  exact pt_mass_identification bridge.link beta1 beta2 hBimetric

end ExperimentalTwoPointSpectralBimetricBridge
end JanusFormal
