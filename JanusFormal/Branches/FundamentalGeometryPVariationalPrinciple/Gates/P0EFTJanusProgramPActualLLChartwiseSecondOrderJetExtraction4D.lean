import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D

/-!
# Actual LL chartwise second-order jet extraction

The three genuine smooth LL fields of a global Program-P configuration are
pulled back through the extended throat chart at one selected point.  Their
manifold smoothness supplies the `C^2` evidence required by the chartwise
second-order-jet constructor.

This is only a local extraction for the LL subsector.  It does not construct
the remaining throat carrier, a background jet, overlap data, or a global jet
bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D

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
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (ThroatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

universe u

/-- Coordinate representative of one genuine smooth throat field in the
extended chart centered at `point`. -/
def smoothThroatFieldChartRepresentative
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates → Fiber :=
  field.toFun ∘ (extChartAt throatCoverModelWithCorners point).symm

@[simp]
theorem smoothThroatFieldChartRepresentative_center
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatFieldChartRepresentative period hPeriod field point
        (extChartAt throatCoverModelWithCorners point point) =
      field point := by
  unfold smoothThroatFieldChartRepresentative
  change field.toFun
      ((extChartAt throatCoverModelWithCorners point).symm
        (extChartAt throatCoverModelWithCorners point point)) =
    field.toFun point
  rw [extChartAt_to_inv]

/-- Manifold smoothness of an actual throat field gives the pointwise `C^2`
hypothesis required by the chartwise jet constructor. -/
theorem smoothThroatFieldChartRepresentative_contDiffAt_two
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    ContDiffAt Real 2
      (smoothThroatFieldChartRepresentative period hPeriod field point)
      (extChartAt throatCoverModelWithCorners point point) := by
  have hField : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, Fiber) 2 field.toFun point :=
    field.contMDiff_toFun.contMDiffAt.of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have hSource := (contMDiffAt_iff_source).mp hField
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext coordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  exact hSource.contDiffAt

/-- Actual chartwise second jet of one smooth throat field. -/
def smoothThroatFieldSecondOrderJetAt
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    FramedSecondOrderJet ThroatCoverCoordinates Fiber :=
  chartwiseSecondOrderJetAt
    (smoothThroatFieldChartRepresentative period hPeriod field point)
    (extChartAt throatCoverModelWithCorners point point)
    (smoothThroatFieldChartRepresentative_contDiffAt_two
      period hPeriod field point)

@[simp]
theorem smoothThroatFieldSecondOrderJetAt_value
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    (smoothThroatFieldSecondOrderJetAt period hPeriod field point).value =
      field point := by
  rw [smoothThroatFieldSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value,
    smoothThroatFieldChartRepresentative_center]

/-- The three actual LL jets extracted at one throat point. -/
structure GlobalLLChartwiseSecondOrderJets where
  llAuxMetric :
    FramedSecondOrderJet ThroatCoverCoordinates LLMetricFiber
  llMeasure : FramedSecondOrderJet ThroatCoverCoordinates Real
  llField : FramedSecondOrderJet ThroatCoverCoordinates LLFieldFiber

/-- LL extraction from the genuine physical global configuration. -/
def globalFieldConfigurationLLChartwiseSecondOrderJetsAt
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    GlobalLLChartwiseSecondOrderJets where
  llAuxMetric :=
    smoothThroatFieldSecondOrderJetAt period hPeriod
      configuration.coefficientFields.llAuxMetric point
  llMeasure :=
    smoothThroatFieldSecondOrderJetAt period hPeriod
      configuration.coefficientFields.llMeasure point
  llField :=
    smoothThroatFieldSecondOrderJetAt period hPeriod
      configuration.coefficientFields.llField point

@[simp]
theorem globalFieldConfigurationLLChartwiseSecondOrderJetsAt_llAuxMetric_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration point).llAuxMetric.value =
      configuration.coefficientFields.llAuxMetric point := by
  exact smoothThroatFieldSecondOrderJetAt_value period hPeriod _ point

@[simp]
theorem globalFieldConfigurationLLChartwiseSecondOrderJetsAt_llMeasure_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration point).llMeasure.value =
      configuration.coefficientFields.llMeasure point := by
  exact smoothThroatFieldSecondOrderJetAt_value period hPeriod _ point

@[simp]
theorem globalFieldConfigurationLLChartwiseSecondOrderJetsAt_llField_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration point).llField.value =
      configuration.coefficientFields.llField point := by
  exact smoothThroatFieldSecondOrderJetAt_value period hPeriod _ point

/-- The gauge-fixed extension uses exactly the LL fields of its retained
physical configuration. -/
def globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    GlobalLLChartwiseSecondOrderJets :=
  globalFieldConfigurationLLChartwiseSecondOrderJetsAt
    period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt_llAuxMetric_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration point).llAuxMetric.value =
      configuration.physical.coefficientFields.llAuxMetric point := by
  exact
    globalFieldConfigurationLLChartwiseSecondOrderJetsAt_llAuxMetric_value
      period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt_llMeasure_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration point).llMeasure.value =
      configuration.physical.coefficientFields.llMeasure point := by
  exact
    globalFieldConfigurationLLChartwiseSecondOrderJetsAt_llMeasure_value
      period hPeriod configuration.physical point

@[simp]
theorem globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt_llField_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLChartwiseSecondOrderJetsAt
      period hPeriod configuration point).llField.value =
      configuration.physical.coefficientFields.llField point := by
  exact
    globalFieldConfigurationLLChartwiseSecondOrderJetsAt_llField_value
      period hPeriod configuration.physical point

end
end P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D
end JanusFormal
