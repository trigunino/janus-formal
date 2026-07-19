import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusEtaLargeGaugeAnomaly
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusHolonomySpectralFlow

/-!
# Circle eta/spectral-flow bridge

For the already constructed circle zero-mode model, this gate identifies the
unit large-gauge eta jump with minus twice the corresponding spectral-flow
integer.  It also identifies the residual mod-two class and proves cancellation
of the two PT-related jumps.

This is only the circle zero-mode representative.  It does not construct the
global Janus family index, an APS comparison theorem, or a bulk inflow class.
-/

namespace JanusFormal
namespace P0EFTJanusCircleEtaSpectralFlowBridge4D

set_option autoImplicit false

open P0EFTJanusCircleHolonomyEta
open P0EFTJanusEtaLargeGaugeAnomaly
open P0EFTJanusHolonomySpectralFlow

/-- The unit large-gauge eta jump is exactly minus twice the unit spectral
flow of the same circle zero-mode tower. -/
theorem zeroModeEta_unit_jump_eq_neg_two_spectralFlow
    (diracIndex : ℤ) (holonomy : ℝ) :
    zeroModeEta diracIndex (holonomy + 1) -
        zeroModeEta diracIndex holonomy =
      -2 * (spectralFlow diracIndex 1 : ℝ) := by
  rw [eta_unit_large_gauge_shift, unit_winding_spectral_flow]
  ring

/-- The same jump is the negative double of the induced doubled level shift
defined from spectral flow. -/
theorem zeroModeEta_unit_jump_eq_neg_two_doubledLevelShift
    (diracIndex : ℤ) (holonomy : ℝ) :
    zeroModeEta diracIndex (holonomy + 1) -
        zeroModeEta diracIndex holonomy =
      -2 * (doubledLevelShiftFromFlow diracIndex 1 : ℝ) := by
  simpa [doubledLevelShiftFromFlow] using
    zeroModeEta_unit_jump_eq_neg_two_spectralFlow diracIndex holonomy

/-- The mod-two large-gauge eta class is the unit spectral-flow integer reduced
modulo two. -/
theorem largeGaugeAnomalyParity_eq_spectralFlow_mod_two
    (diracIndex : ℤ) :
    largeGaugeAnomalyParity diracIndex =
      (spectralFlow diracIndex 1 : ZMod 2) := by
  simp [largeGaugeAnomalyParity]

/-- The eta jumps of the two PT-related circle towers cancel exactly. -/
theorem ptPaired_zeroModeEta_unit_jumps_cancel
    (diracIndex : ℤ) (holonomy : ℝ) :
    (zeroModeEta diracIndex (holonomy + 1) -
        zeroModeEta diracIndex holonomy) +
      (zeroModeEta (-diracIndex) (holonomy + 1) -
        zeroModeEta (-diracIndex) holonomy) = 0 := by
  rw [zeroModeEta_unit_jump_eq_neg_two_spectralFlow,
    zeroModeEta_unit_jump_eq_neg_two_spectralFlow]
  simp [spectralFlow]

end P0EFTJanusCircleEtaSpectralFlowBridge4D
end JanusFormal
