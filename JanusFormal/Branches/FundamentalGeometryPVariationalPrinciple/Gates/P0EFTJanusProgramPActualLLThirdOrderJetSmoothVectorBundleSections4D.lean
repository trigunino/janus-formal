import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLChartwiseThirdOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSmoothFieldThirdOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLSecondOrderJetSmoothVectorBundleSections4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLThirdOrderJetProductVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

/-!
# Smooth LL third-jet vector-bundle sections

Compatible chartwise third jets of a smooth fixed-fiber throat field assemble
into a global smooth section.  The construction is applied to the three LL
fields and packaged in the existing LL product core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualLLThirdOrderJetSmoothVectorBundleSections4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set Bundle
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualLLChartwiseThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatSmoothFieldThirdOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetCoordChange4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualLLSecondOrderJetSmoothVectorBundleSections4D
open P0EFTJanusProgramPActualLLThirdOrderJetProductCoordChange4D
open P0EFTJanusProgramPActualLLThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

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

/-- Total space of the constant-fiber third-jet bundle. -/
abbrev ActualThroatConstantFiberThirdOrderJetBundleTotalSpace
    (Fiber : Type u)
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber] :=
  Bundle.TotalSpace
    (ActualThroatConstantFiberThirdOrderJet Fiber)
    (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := Fiber)).Fiber

section SmoothField

variable {Fiber : Type u}
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]

private abbrev JetCore :=
  actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
    period hPeriod (Fiber := Fiber)

/-- Fixed-fiber smooth third jets obey the coordinate changes of the core. -/
theorem throatSmoothFieldThirdOrderJetLocalRepresentative_compatible
    (field : SmoothThroatField period hPeriod Fiber)
    (first second current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberThirdOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberThirdOrderJetBundleBaseSet
          period hPeriod second) :
    (JetCore period hPeriod (Fiber := Fiber)).coordChange first second current
        (throatSmoothFieldThirdOrderJetLocalRepresentative
          period hPeriod field first current) =
      throatSmoothFieldThirdOrderJetLocalRepresentative
        period hPeriod field second current := by
  have hFirst : current ∈
      (extChartAt throatCoverModelWithCorners first).source := hCurrent.1
  have hSecond : current ∈
      (extChartAt throatCoverModelWithCorners second).source := hCurrent.2
  change actualThroatConstantFiberThirdOrderJetContinuousCoordChange
      period hPeriod (Fiber := Fiber) first second current
        (throatSmoothFieldThirdOrderJetLocalRepresentative
          period hPeriod field first current) = _
  rw [actualThroatConstantFiberThirdOrderJetContinuousCoordChange_apply]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  unfold throatSmoothFieldThirdOrderJetLocalRepresentative
  rw [dif_pos hFirst, dif_pos hSecond]
  simpa only [actualThroatConstantFiberThirdOrderJetBaseChangeAt] using
    (throatSmoothFieldThirdOrderJetInChartAt_transition
      period hPeriod field first second current hFirst hSecond).symm

/-- Coordinate data of the smooth third-jet section. -/
def actualThroatSmoothFieldThirdOrderJetSmoothCoreSectionCoordinates
    (field : SmoothThroatField period hPeriod Fiber) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (JetCore period hPeriod (Fiber := Fiber)) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (JetCore period hPeriod (Fiber := Fiber))
    (throatSmoothFieldThirdOrderJetLocalRepresentative
      period hPeriod field)
    (throatSmoothFieldThirdOrderJetLocalRepresentative_compatible
      period hPeriod field)
    (throatSmoothFieldThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod field)

/-- Global total-space section assembled from the local third jets. -/
def actualThroatSmoothFieldThirdOrderJetVectorBundleSection
    (field : SmoothThroatField period hPeriod Fiber) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberThirdOrderJetBundleTotalSpace
        period hPeriod Fiber :=
  fun current ↦ TotalSpace.mk'
    (ActualThroatConstantFiberThirdOrderJet Fiber) current
      (vectorBundleCoreSectionOfLocalRepresentatives
        (JetCore period hPeriod (Fiber := Fiber))
        (throatSmoothFieldThirdOrderJetLocalRepresentative
          period hPeriod field) current)

/-- The assembled third-jet section is globally smooth. -/
theorem actualThroatSmoothFieldThirdOrderJetVectorBundleSection_contMDiff
    (field : SmoothThroatField period hPeriod Fiber) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberThirdOrderJet Fiber))) ∞
      (actualThroatSmoothFieldThirdOrderJetVectorBundleSection
        period hPeriod field) := by
  letI : (JetCore period hPeriod (Fiber := Fiber)).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := Fiber)
  apply vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    throatCoverModelWithCorners (JetCore period hPeriod (Fiber := Fiber))
    (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod field)
  · intro first second current hCurrent
    exact throatSmoothFieldThirdOrderJetLocalRepresentative_compatible
      period hPeriod field first second current hCurrent
  · intro index
    exact throatSmoothFieldThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod field index

@[simp]
theorem actualThroatSmoothFieldThirdOrderJetVectorBundleSection_value
    (field : SmoothThroatField period hPeriod Fiber)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSmoothFieldThirdOrderJetVectorBundleSection
      period hPeriod field current).2.value = field current := by
  change
    (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod field
      current current).value = field current
  rw [throatSmoothFieldThirdOrderJetLocalRepresentative_eq_of_mem
    period hPeriod field current current (mem_extChartAt_source current)]
  exact throatSmoothFieldThirdOrderJetInChartAt_value
    period hPeriod field current current (mem_extChartAt_source current)

/-- Truncation recovers the existing smooth second-jet section. -/
@[simp]
theorem actualThroatSmoothFieldThirdOrderJetVectorBundleSection_truncate
    (field : SmoothThroatField period hPeriod Fiber)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSmoothFieldThirdOrderJetVectorBundleSection
      period hPeriod field current).2.toFramedSecondOrderJet =
      (actualThroatSmoothFieldSecondOrderJetVectorBundleSection
        period hPeriod field current).2 := by
  change
    (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod field
      current current).toFramedSecondOrderJet =
        throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod field
          current current
  exact throatSmoothFieldThirdOrderJetLocalRepresentative_truncate
    period hPeriod field current current

/-- At the centered chart, the descended jet is the centered extractor. -/
theorem actualThroatSmoothFieldThirdOrderJetVectorBundleSection_centeredJet
    (field : SmoothThroatField period hPeriod Fiber)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSmoothFieldThirdOrderJetVectorBundleSection
      period hPeriod field current).2 =
      smoothThroatFieldThirdOrderJetAt period hPeriod field current := by
  change
    throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod field
        current current =
      smoothThroatFieldThirdOrderJetAt period hPeriod field current
  rw [throatSmoothFieldThirdOrderJetLocalRepresentative_eq_of_mem
    period hPeriod field current current (mem_extChartAt_source current)]
  rfl

end SmoothField

/-! ## LL wrappers -/

def globalFieldConfigurationLLAuxMetricThirdOrderJetVectorBundleSection
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldThirdOrderJetVectorBundleSection period hPeriod
    configuration.coefficientFields.llAuxMetric

def globalFieldConfigurationLLMeasureThirdOrderJetVectorBundleSection
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldThirdOrderJetVectorBundleSection period hPeriod
    configuration.coefficientFields.llMeasure

def globalFieldConfigurationLLFieldThirdOrderJetVectorBundleSection
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldThirdOrderJetVectorBundleSection period hPeriod
    configuration.coefficientFields.llField

def globalFieldConfigurationLLAuxMetricThirdOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldThirdOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.coefficientFields.llAuxMetric

def globalFieldConfigurationLLMeasureThirdOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldThirdOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.coefficientFields.llMeasure

def globalFieldConfigurationLLFieldThirdOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldThirdOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.coefficientFields.llField

/-- Product coordinate data of the three LL third-jet sections. -/
def globalFieldConfigurationLLThirdOrderJetProductSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualLLThirdOrderJetProductVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
      (globalFieldConfigurationLLAuxMetricThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod configuration)
      (globalFieldConfigurationLLMeasureThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod configuration))
    (globalFieldConfigurationLLFieldThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod configuration)

/-! ## Gauge-fixed wrappers -/

def globalGaugeFixedFieldConfigurationLLAuxMetricThirdOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  globalFieldConfigurationLLAuxMetricThirdOrderJetVectorBundleSection
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLMeasureThirdOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  globalFieldConfigurationLLMeasureThirdOrderJetVectorBundleSection
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLFieldThirdOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  globalFieldConfigurationLLFieldThirdOrderJetVectorBundleSection
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLAuxMetricThirdOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  globalFieldConfigurationLLAuxMetricThirdOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLMeasureThirdOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  globalFieldConfigurationLLMeasureThirdOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLFieldThirdOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  globalFieldConfigurationLLFieldThirdOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.physical

/-- Gauge-fixed wrapper of the LL product coordinate data. -/
def globalGaugeFixedFieldConfigurationLLThirdOrderJetProductSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualLLThirdOrderJetProductVectorBundleCore period hPeriod) :=
  globalFieldConfigurationLLThirdOrderJetProductSmoothCoreSectionCoordinates
    period hPeriod configuration.physical

end
end P0EFTJanusProgramPActualLLThirdOrderJetSmoothVectorBundleSections4D
end JanusFormal
