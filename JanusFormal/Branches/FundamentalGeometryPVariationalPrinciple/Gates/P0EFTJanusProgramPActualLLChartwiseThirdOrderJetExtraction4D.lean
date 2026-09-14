import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D

/-!
# Actual LL chartwise third-order jet extraction

The three smooth LL fields are differentiated once beyond their existing
second jets in the centered extended throat chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualLLChartwiseThirdOrderJetExtraction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D

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

universe u

/-- Smoothness of a throat field supplies the pointwise `C^3` chart
regularity required by the third-jet constructor. -/
theorem smoothThroatFieldChartRepresentative_contDiffAt_three
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    ContDiffAt Real 3
      (smoothThroatFieldChartRepresentative period hPeriod field point)
      (extChartAt throatCoverModelWithCorners point point) := by
  have hField : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, Fiber) 3 field.toFun point :=
    field.contMDiff_toFun.contMDiffAt.of_le (by
      change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have hSource := (contMDiffAt_iff_source).mp hField
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext coordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  exact hSource.contDiffAt

/-- Actual centered chartwise third jet of one smooth throat field. -/
def smoothThroatFieldThirdOrderJetAt
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    FramedThirdOrderJet ThroatCoverCoordinates Fiber :=
  chartwiseThirdOrderJetAt
    (smoothThroatFieldChartRepresentative period hPeriod field point)
    (extChartAt throatCoverModelWithCorners point point)
    (smoothThroatFieldChartRepresentative_contDiffAt_three
      period hPeriod field point)

@[simp]
theorem smoothThroatFieldThirdOrderJetAt_value
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    (smoothThroatFieldThirdOrderJetAt period hPeriod field point).value =
      field point := by
  rw [smoothThroatFieldThirdOrderJetAt, chartwiseThirdOrderJetAt_value,
    smoothThroatFieldChartRepresentative_center]

@[simp]
theorem smoothThroatFieldThirdOrderJetAt_firstDerivative
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    (smoothThroatFieldThirdOrderJetAt period hPeriod field point).firstDerivative =
      fderiv Real
        (smoothThroatFieldChartRepresentative period hPeriod field point)
        (extChartAt throatCoverModelWithCorners point point) :=
  rfl

@[simp]
theorem smoothThroatFieldThirdOrderJetAt_secondDerivative
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    (smoothThroatFieldThirdOrderJetAt period hPeriod field point).secondDerivative =
      fderiv Real
        (fderiv Real
          (smoothThroatFieldChartRepresentative period hPeriod field point))
        (extChartAt throatCoverModelWithCorners point point) :=
  rfl

@[simp]
theorem smoothThroatFieldThirdOrderJetAt_thirdDerivative
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    (smoothThroatFieldThirdOrderJetAt period hPeriod field point).thirdDerivative =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (smoothThroatFieldChartRepresentative period hPeriod field point)))
        (extChartAt throatCoverModelWithCorners point point) :=
  rfl

@[simp]
theorem smoothThroatFieldThirdOrderJetAt_toFramedSecondOrderJet
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    (smoothThroatFieldThirdOrderJetAt period hPeriod field point).toFramedSecondOrderJet =
      smoothThroatFieldSecondOrderJetAt period hPeriod field point := by
  apply FramedSecondOrderJet.ext_components
  · rfl
  · rfl
  · rfl

/-- The three centered LL third jets at one throat point. -/
structure GlobalLLChartwiseThirdOrderJets where
  llAuxMetric :
    FramedThirdOrderJet ThroatCoverCoordinates LLMetricFiber
  llMeasure : FramedThirdOrderJet ThroatCoverCoordinates Real
  llField : FramedThirdOrderJet ThroatCoverCoordinates LLFieldFiber

/-- LL third-jet extraction from a global Program-P configuration. -/
def globalFieldConfigurationLLChartwiseThirdOrderJetsAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    GlobalLLChartwiseThirdOrderJets where
  llAuxMetric :=
    smoothThroatFieldThirdOrderJetAt period hPeriod
      configuration.coefficientFields.llAuxMetric point
  llMeasure :=
    smoothThroatFieldThirdOrderJetAt period hPeriod
      configuration.coefficientFields.llMeasure point
  llField :=
    smoothThroatFieldThirdOrderJetAt period hPeriod
      configuration.coefficientFields.llField point

@[simp]
theorem globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llAuxMetric_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llAuxMetric.value =
      configuration.coefficientFields.llAuxMetric point :=
  smoothThroatFieldThirdOrderJetAt_value period hPeriod _ point

@[simp]
theorem globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llMeasure_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llMeasure.value =
      configuration.coefficientFields.llMeasure point :=
  smoothThroatFieldThirdOrderJetAt_value period hPeriod _ point

@[simp]
theorem globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llField_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llField.value =
      configuration.coefficientFields.llField point :=
  smoothThroatFieldThirdOrderJetAt_value period hPeriod _ point

@[simp]
theorem globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llAuxMetric_truncate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llAuxMetric.toFramedSecondOrderJet =
      (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration point).llAuxMetric :=
  smoothThroatFieldThirdOrderJetAt_toFramedSecondOrderJet
    period hPeriod _ point

@[simp]
theorem globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llMeasure_truncate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llMeasure.toFramedSecondOrderJet =
      (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration point).llMeasure :=
  smoothThroatFieldThirdOrderJetAt_toFramedSecondOrderJet
    period hPeriod _ point

@[simp]
theorem globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llField_truncate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llField.toFramedSecondOrderJet =
      (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration point).llField :=
  smoothThroatFieldThirdOrderJetAt_toFramedSecondOrderJet
    period hPeriod _ point

/-- The gauge-fixed wrapper uses the LL fields of its physical configuration. -/
def globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    GlobalLLChartwiseThirdOrderJets :=
  globalFieldConfigurationLLChartwiseThirdOrderJetsAt
    period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt_llAuxMetric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llAuxMetric.value =
      configuration.physical.coefficientFields.llAuxMetric point :=
  globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llAuxMetric_value
    period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt_llMeasure_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llMeasure.value =
      configuration.physical.coefficientFields.llMeasure point :=
  globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llMeasure_value
    period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt_llField_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llField.value =
      configuration.physical.coefficientFields.llField point :=
  globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llField_value
    period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt_llAuxMetric_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llAuxMetric.toFramedSecondOrderJet =
      (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration point).llAuxMetric :=
  globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llAuxMetric_truncate
    period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt_llMeasure_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llMeasure.toFramedSecondOrderJet =
      (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration point).llMeasure :=
  globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llMeasure_truncate
    period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt_llField_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseThirdOrderJetsAt
      period hPeriod configuration point).llField.toFramedSecondOrderJet =
      (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration point).llField :=
  globalFieldConfigurationLLChartwiseThirdOrderJetsAt_llField_truncate
    period hPeriod configuration.physical point

end
end P0EFTJanusProgramPActualLLChartwiseThirdOrderJetExtraction4D
end JanusFormal
