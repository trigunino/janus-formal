import JanusFormal.Experimental.TwoPointSpectralBimetricBridge

/-!
# Nonlinear audit of the minimal two-point spectral seed

This isolated experiment compares the quadratic two-point commutator action
with the full PT-flat proportional bimetric interaction.
-/

namespace JanusFormal
namespace ExperimentalTwoPointSpectralNonlinearBimetricAudit

set_option autoImplicit false

open ExperimentalTwoPointSpectralJanus
open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusReciprocalBimetricPotential

/-- Exact expansion of the PT-flat interaction around `c = 1 + x`. -/
theorem pt_interaction_expansion
    (beta1 beta2 x : ℝ) :
    proportionalInteractionEnergy beta1 beta2 (1 + x) =
      12 * (beta1 + beta2) * x ^ 2 +
      12 * (beta1 + beta2) * x ^ 3 +
      (4 * beta1 + 3 * beta2) * x ^ 4 := by
  unfold proportionalInteractionEnergy proportionalPotential
    ptFlatCoefficients
  ring

/-- Matching the spectral link to the Hessian fixes its quadratic coefficient,
while leaving an explicit cubic/quartic nonlinear residual. -/
theorem hessian_matched_spectral_residual
    (link beta1 beta2 x : ℝ)
    (hMatch : link ^ 2 = 12 * (beta1 + beta2)) :
    proportionalInteractionEnergy beta1 beta2 (1 + x) -
        spectralLinkAction link (1 + x) 1 =
      12 * (beta1 + beta2) * x ^ 3 +
      (4 * beta1 + 3 * beta2) * x ^ 4 := by
  rw [pt_interaction_expansion, spectralLinkAction_formula, hMatch]
  ring

/-- No nontrivial constant two-point link reproduces the complete PT-flat
proportional interaction for every `c`.  Exact global equality collapses both
bimetric coefficients and the link scale to zero. -/
theorem minimal_link_global_completion_no_go
    (link beta1 beta2 : ℝ)
    (hGlobal : ∀ c : ℝ,
      spectralLinkAction link c 1 =
        proportionalInteractionEnergy beta1 beta2 c) :
    link ^ 2 = 0 ∧ beta1 = 0 ∧ beta2 = 0 := by
  have h0 := hGlobal 0
  have h2 := hGlobal 2
  have h3 := hGlobal 3
  rw [spectralLinkAction_formula] at h0 h2 h3
  unfold proportionalInteractionEnergy proportionalPotential
    ptFlatCoefficients at h0 h2 h3
  norm_num at h0 h2 h3
  constructor
  · linarith
  constructor <;> linarith

end ExperimentalTwoPointSpectralNonlinearBimetricAudit
end JanusFormal
