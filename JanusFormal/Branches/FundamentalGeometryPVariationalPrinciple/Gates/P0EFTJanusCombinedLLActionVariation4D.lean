import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonCompleteSectorD9Variation4D

/-!
# Differential LL action on the combined Program-P variation

The unchanged LL action reads only its LL field, auxiliary throat metric and
measure.  Hence the other components of the simultaneous variation are
ignored by this exact action, while its LL component follows the original
flux curve.
-/

namespace JanusFormal
namespace P0EFTJanusCombinedLLActionVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The LL data extracted from the simultaneous curve are exactly those of
the original LL-only flux curve. -/
theorem combinedIndependentVariation_llData
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (parameter : Real) :
    (independentFieldCurve period hPeriod fields
        (combinedIndependentVariation period hPeriod direction) parameter).llField =
      (differentialLLFluxCurve period hPeriod fields direction.ll parameter).llField ∧
    (independentFieldCurve period hPeriod fields
        (combinedIndependentVariation period hPeriod direction) parameter).llAuxMetric =
      (differentialLLFluxCurve period hPeriod fields direction.ll parameter).llAuxMetric ∧
    (independentFieldCurve period hPeriod fields
        (combinedIndependentVariation period hPeriod direction) parameter).llMeasure =
      (differentialLLFluxCurve period hPeriod fields direction.ll parameter).llMeasure := by
  simp [independentFieldCurve, combinedIndependentVariation,
    differentialLLFluxCurve]

theorem globalPTSymmetricDifferentialLLAction_congr_llData
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : IndependentFields period hPeriod)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    (hAuxMetric : first.llAuxMetric = second.llAuxMetric)
    (hMeasure : first.llMeasure = second.llMeasure)
    (hField : first.llField = second.llField) :
    globalPTSymmetricDifferentialLLAction period hPeriod frame first mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame second mu := by
  cases first
  cases second
  simp only at hAuxMetric hMeasure hField
  cases hAuxMetric
  cases hMeasure
  cases hField
  rfl

theorem globalPTSymmetricDifferentialLLFluxFirstVariation_congr_llData
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    (hAuxMetric : first.llAuxMetric = second.llAuxMetric)
    (hMeasure : first.llMeasure = second.llMeasure)
    (hField : first.llField = second.llField) :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        first direction mu =
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        second direction mu := by
  cases first
  cases second
  simp only at hAuxMetric hMeasure hField
  cases hAuxMetric
  cases hMeasure
  cases hField
  rfl

/-- The exact LL action cannot distinguish the simultaneous curve from its
LL-only extraction. -/
theorem globalPTSymmetricDifferentialLLAction_combined_curve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (parameter : Real)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod))) :
    globalPTSymmetricDifferentialLLAction period hPeriod frame
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) parameter) mu =
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction.ll parameter) mu := by
  obtain ⟨hField, hAuxMetric, hMeasure⟩ :=
    combinedIndependentVariation_llData period hPeriod fields direction parameter
  exact globalPTSymmetricDifferentialLLAction_congr_llData period hPeriod frame
    _ _ mu hAuxMetric hMeasure hField

/-- First derivative of the unchanged LL action along the full simultaneous
variation. -/
theorem globalPTSymmetricDifferentialLLAction_combined_curve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : CommonSectorDirections period hPeriod)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    [IsFiniteMeasure mu] :
    HasDerivAt
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (independentFieldCurve period hPeriod fields
            (combinedIndependentVariation period hPeriod direction) parameter) mu)
      (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        fields direction.ll mu) 0 := by
  rw [show (fun parameter : Real =>
      globalPTSymmetricDifferentialLLAction period hPeriod frame
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod direction) parameter) mu) =
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields direction.ll parameter) mu) from by
    funext parameter
    exact globalPTSymmetricDifferentialLLAction_combined_curve period hPeriod
      frame fields direction parameter mu]
  exact globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt period
    hPeriod frame fields direction.ll mu

/-- The mixed LL Hessian is transported along the same combined curve; the
second direction contributes through its LL component. -/
theorem globalPTSymmetricDifferentialLLFirstVariation_combined_curve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : CommonSectorDirections period hPeriod)
    (mu : Measure (MappingTorus (fixedEquatorData period hPeriod)))
    [IsFiniteMeasure mu] :
    HasDerivAt
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          (independentFieldCurve period hPeriod fields
            (combinedIndependentVariation period hPeriod first) parameter)
          second.ll mu)
      (globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame fields
        first.ll second.ll mu) 0 := by
  rw [show (fun parameter : Real =>
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        (independentFieldCurve period hPeriod fields
          (combinedIndependentVariation period hPeriod first) parameter)
        second.ll mu) =
      (fun parameter : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields first.ll parameter)
          second.ll mu) from by
    funext parameter
    obtain ⟨hField, hAuxMetric, hMeasure⟩ :=
      combinedIndependentVariation_llData period hPeriod fields first parameter
    exact globalPTSymmetricDifferentialLLFluxFirstVariation_congr_llData
      period hPeriod frame _ _ second.ll mu hAuxMetric hMeasure hField]
  exact globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
    period hPeriod frame fields first.ll second.ll mu

end

end P0EFTJanusCombinedLLActionVariation4D
end JanusFormal
