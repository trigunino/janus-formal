import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurability of a pointwise parameter derivative

An almost-everywhere pointwise derivative is almost-everywhere strongly
measurable when the original family is locally so.  The proof realizes the
derivative as the almost-everywhere limit of forward difference quotients.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPParametricDerivativeAEStronglyMeasurable4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- A pointwise parameter derivative of a locally measurable real family is
almost-everywhere strongly measurable. -/
theorem derivative_aeStronglyMeasurable
    {Time : Type*} [MeasurableSpace Time]
    (measure : Measure Time)
    (family : Real → Time → Real)
    (familyDerivative : Time → Real)
    (parameter : Real)
    (family_aeStronglyMeasurable :
      ∀ᶠ current in nhds parameter,
        AEStronglyMeasurable (family current) measure)
    (pointwise_hasDerivAt :
      ∀ᵐ time ∂measure,
        HasDerivAt (fun current => family current time)
          (familyDerivative time) parameter) :
    AEStronglyMeasurable familyDerivative measure := by
  classical
  let step : Nat → Real := fun index => 1 / ((index : Real) + 1)
  have hStep : Tendsto step atTop (nhds (0 : Real)) := by
    simpa [step] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hStepPositive : ∀ index, 0 < step index := by
    intro index
    simp only [step]
    positivity
  have hStepRight :
      Tendsto step atTop (nhdsWithin (0 : Real) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2
      ⟨hStep, Eventually.of_forall hStepPositive⟩
  have hFamilyAtParameter :
      AEStronglyMeasurable (family parameter) measure :=
    family_aeStronglyMeasurable.self_of_nhds
  have hShiftedParameter :
      Tendsto (fun index => parameter + step index) atTop
        (nhds parameter) := by
    simpa using tendsto_const_nhds.add hStep
  have hFamilyAlongSequence :
      ∀ᶠ index in atTop,
        AEStronglyMeasurable
          (family (parameter + step index)) measure :=
    hShiftedParameter.eventually family_aeStronglyMeasurable
  let quotient : Nat → Time → Real := fun index time =>
    if AEStronglyMeasurable
        (family (parameter + step index)) measure then
      (step index)⁻¹ *
        (family (parameter + step index) time - family parameter time)
    else
      0
  have hQuotientMeasurable : ∀ index,
      AEStronglyMeasurable (quotient index) measure := by
    intro index
    by_cases hMeasurable :
        AEStronglyMeasurable
          (family (parameter + step index)) measure
    · simp only [quotient, hMeasurable, if_true]
      exact (hMeasurable.sub hFamilyAtParameter).const_mul
        (step index)⁻¹
    · simp only [quotient, hMeasurable, if_false]
      exact aestronglyMeasurable_const
  refine aestronglyMeasurable_of_tendsto_ae atTop
    hQuotientMeasurable ?_
  filter_upwards [pointwise_hasDerivAt] with time hDerivative
  have hSlope :
      Tendsto
        (fun index =>
          (step index)⁻¹ *
            (family (parameter + step index) time -
              family parameter time))
        atTop (nhds (familyDerivative time)) := by
    simpa [Function.comp_def, smul_eq_mul] using
      hDerivative.tendsto_slope_zero_right.comp hStepRight
  apply hSlope.congr'
  filter_upwards [hFamilyAlongSequence] with index hMeasurable
  simp only [quotient, hMeasurable, if_true]

/-- Public checkpoint for derivative-field measurability. -/
theorem parametric_derivative_aeStronglyMeasurable_gate
    {Time : Type*} [MeasurableSpace Time]
    (measure : Measure Time)
    (family : Real → Time → Real)
    (familyDerivative : Time → Real)
    (parameter : Real)
    (family_aeStronglyMeasurable :
      ∀ᶠ current in nhds parameter,
        AEStronglyMeasurable (family current) measure)
    (pointwise_hasDerivAt :
      ∀ᵐ time ∂measure,
        HasDerivAt (fun current => family current time)
          (familyDerivative time) parameter) :
    AEStronglyMeasurable familyDerivative measure :=
  derivative_aeStronglyMeasurable measure family familyDerivative parameter
    family_aeStronglyMeasurable pointwise_hasDerivAt

end
end P0EFTJanusProgramPParametricDerivativeAEStronglyMeasurable4D
end JanusFormal
