import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphModeRieszRatio4D

/-!
# No positive floor for the isolated matter graph's modal Riesz coefficients

Properness of the genuine signed SpinC spectrum and the infinite circle tower
force the exact matter graph Riesz multipliers `w / (1 + w²)` arbitrarily close
to zero.  This result concerns the diagonal matter graph alone.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterGraphModalRatioNoFloor4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusComplexDiagonalProperShiftFredholm4D
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)

private def zeroTowerSignedMode (n : Int) :
    PrimitiveSpinCGeometricSignedMode :=
  (.positiveQuarter,
    Sum.inl (⟨0, by simp [primitiveSphereModeDegeneracy]⟩, n))

private theorem zeroTowerSignedMode_injective :
    Function.Injective zeroTowerSignedMode := by
  intro first second h
  have hSum := congrArg
    (fun mode : PrimitiveSpinCGeometricSignedMode => mode.2) h
  have hPair := Sum.inl.inj hSum
  exact congrArg Prod.snd hPair

private instance signedModeInfinite :
    Infinite PrimitiveSpinCGeometricSignedMode :=
  Infinite.of_injective zeroTowerSignedMode zeroTowerSignedMode_injective

/-- A mass shift of the proper kinetic spectrum remains proper. -/
private theorem shiftedMatterWeight_proper :
    ComplexDiagonalProperWeight PrimitiveSpinCGeometricSignedMode
      (fun mode =>
        primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) := by
  refine ⟨?_⟩
  intro bound
  apply ((primitiveSpinCGeometricSignedKineticHessianWeight_proper
    period hPeriod).finite_sublevel (bound + |massSquared|)).subset
  intro mode hMode
  change |primitiveSpinCGeometricSignedKineticHessianWeight
    period hPeriod mode + massSquared| ≤ bound at hMode
  calc
    |primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode| =
      |(primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared) - massSquared| := by ring
    _ ≤ |primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared| + |massSquared| :=
      abs_sub _ _
    _ ≤ bound + |massSquared| := by
      simpa [add_comm] using add_le_add_right hMode |massSquared|

/-- Signed modes of the genuine mass-shifted SpinC Hessian have unbounded
absolute weight. -/
theorem exists_matter_weight_above (bound : Real) :
    ∃ mode : PrimitiveSpinCGeometricSignedMode,
      bound < |primitiveSpinCGeometricSignedKineticHessianWeight
        period hPeriod mode + massSquared| := by
  by_contra h
  push Not at h
  have hFinite : (Set.univ : Set PrimitiveSpinCGeometricSignedMode).Finite := by
    convert (shiftedMatterWeight_proper period hPeriod massSquared).finite_sublevel
      bound using 1
    ext mode
    simp [h mode]
  exact (show ¬Finite PrimitiveSpinCGeometricSignedMode from
    Infinite.not_finite) (Set.finite_univ_iff.mp hFinite)

/-- There is no positive lower floor for the isolated matter graph's exact
modal Riesz coefficients. -/
theorem matter_graph_modal_ratio_arbitrarily_small
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    ∃ mode : PrimitiveSpinCGeometricSignedMode,
      |(primitiveSpinCGeometricSignedKineticHessianWeight
          period hPeriod mode + massSquared) /
          (1 + (primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode + massSquared) ^ 2)| < epsilon := by
  obtain ⟨mode, hLarge⟩ := exists_matter_weight_above
    period hPeriod massSquared (1 / epsilon)
  let w := primitiveSpinCGeometricSignedKineticHessianWeight
    period hPeriod mode + massSquared
  have hAbs : 0 < |w| := lt_of_le_of_lt (by positivity) hLarge
  have hDen : 0 < 1 + w ^ 2 := by positivity
  have hRatio : |w / (1 + w ^ 2)| ≤ 1 / |w| := by
    rw [abs_div, abs_of_pos hDen]
    apply (div_le_div_iff₀ hDen hAbs).2
    nlinarith [sq_abs w]
  have hInv : 1 / |w| < epsilon := by
    apply (div_lt_iff₀ hAbs).2
    have h := (div_lt_iff₀ hEpsilon).1 hLarge
    nlinarith
  exact ⟨mode, lt_of_le_of_lt hRatio hInv⟩

/-- No strictly positive number bounds every genuine signed-matter modal
Riesz multiplier away from zero. -/
theorem no_positive_matter_graph_modal_ratio_floor :
    ¬ ∃ gap : Real, 0 < gap ∧
      ∀ mode : PrimitiveSpinCGeometricSignedMode,
        gap ≤ |(primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode + massSquared) /
            (1 + (primitiveSpinCGeometricSignedKineticHessianWeight
              period hPeriod mode + massSquared) ^ 2)| := by
  rintro ⟨gap, hGap, hFloor⟩
  obtain ⟨mode, hSmall⟩ := matter_graph_modal_ratio_arbitrarily_small
    period hPeriod massSquared gap hGap
  exact (not_lt_of_ge (hFloor mode)) hSmall

end
end P0EFTJanusProgramPT12MatterGraphModalRatioNoFloor4D
end JanusFormal
