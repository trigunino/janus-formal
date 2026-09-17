import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphModalRatioNoFloor4D

/-!
# The signed matter graph-to-L² ratio has a positive modal floor

For a mode of weight `w`, the bounded graph-to-L² multiplier has singular
ratio `|w| / sqrt (1 + w²)`.  The existing proper-spectrum gap bounds this
ratio away from zero outside the finite resonant kernel, even though the
graph Riesz coefficient `w / (1 + w²)` tends to zero at high frequency.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterGraphToL2ModalGap4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12MatterGraphModalRatioNoFloor4D

/-- An absolute weight gap yields an explicit graph-to-L² modal floor. -/
private theorem graph_to_l2_ratio_lower_bound
    {gap weight : Real} (hGap : 0 < gap) (hWeight : gap ≤ |weight|) :
    gap / (1 + gap) ≤ |weight| / Real.sqrt (1 + weight ^ 2) := by
  have hAbs : 0 ≤ |weight| := abs_nonneg _
  have hDen : 0 < 1 + weight ^ 2 := by positivity
  have hSqrt : 0 < Real.sqrt (1 + weight ^ 2) := Real.sqrt_pos.2 hDen
  have hSqrtSq : (Real.sqrt (1 + weight ^ 2)) ^ 2 = 1 + weight ^ 2 :=
    Real.sq_sqrt (le_of_lt hDen)
  have hSqrtLe : Real.sqrt (1 + weight ^ 2) ≤ 1 + |weight| := by
    nlinarith [sq_abs weight]
  have hGapDen : 0 < 1 + gap := by positivity
  have hAbsDen : 0 < 1 + |weight| := by positivity
  have hFirst : gap / (1 + gap) ≤ |weight| / (1 + |weight|) := by
    apply (div_le_div_iff₀ hGapDen hAbsDen).2
    nlinarith
  have hSecond : |weight| / (1 + |weight|) ≤
      |weight| / Real.sqrt (1 + weight ^ 2) := by
    apply (div_le_div_iff₀ hAbsDen hSqrt).2
    nlinarith
  exact hFirst.trans hSecond

variable (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)

/-- The genuine two-sector signed matter weight has an explicit positive
graph-to-L² singular ratio floor away from its possible mass-resonant kernel. -/
theorem matter_graph_to_l2_modal_gap :
    ∃ gap : Real, 0 < gap ∧
      ∀ mode : ProgramPPrimitiveSpinCMatterMode,
        programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared mode ≠ 0 →
        gap ≤
          |programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared mode| /
            Real.sqrt (1 +
              (programPPrimitiveSpinCMatterHessianWeight
                period hPeriod massSquared mode) ^ 2) := by
  let data := programPPrimitiveSpinCMatterHessianFiniteZeroGap
    period hPeriod massSquared
  refine ⟨data.gap / (1 + data.gap),
    div_pos data.gap_pos (by linarith [data.gap_pos]), ?_⟩
  intro mode hNonzero
  exact graph_to_l2_ratio_lower_bound data.gap_pos
    (data.gap_le mode hNonzero)

/-- The same nonresonant graph-to-L² modes have a positive modal floor,
while the actual graph Riesz coefficient has arbitrarily small values. -/
theorem matter_graph_to_l2_gap_with_riesz_decay :
    (∃ gap : Real, 0 < gap ∧
      ∀ mode : ProgramPPrimitiveSpinCMatterMode,
        programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared mode ≠ 0 →
        gap ≤
          |programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared mode| /
            Real.sqrt (1 +
              (programPPrimitiveSpinCMatterHessianWeight
                period hPeriod massSquared mode) ^ 2)) ∧
    (∀ epsilon : Real, 0 < epsilon →
      ∃ mode : PrimitiveSpinCGeometricSignedMode,
        |(primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode + massSquared) /
            (1 + (primitiveSpinCGeometricSignedKineticHessianWeight
              period hPeriod mode + massSquared) ^ 2)| < epsilon) := by
  exact ⟨matter_graph_to_l2_modal_gap period hPeriod massSquared,
    matter_graph_modal_ratio_arbitrarily_small period hPeriod massSquared⟩

end
end P0EFTJanusProgramPT12MatterGraphToL2ModalGap4D
end JanusFormal
