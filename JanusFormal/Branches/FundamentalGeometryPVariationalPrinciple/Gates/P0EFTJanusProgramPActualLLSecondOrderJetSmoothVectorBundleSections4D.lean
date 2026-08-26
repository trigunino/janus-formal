import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

/-!
# Smooth LL second-jet vector-bundle sections

The compatible chartwise second jets of a smooth fixed-fiber throat field
assemble into a global smooth section.  This is applied to the three actual
LL fields of a Program-P configuration.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualLLSecondOrderJetSmoothVectorBundleSections4D

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
open P0EFTJanusProgramPActualLLChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

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

/-- Total space of the constant-fiber second-jet bundle. -/
abbrev ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
    (Fiber : Type u)
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber] :=
  Bundle.TotalSpace
    (ActualThroatConstantFiberSecondOrderJet Fiber)
    (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := Fiber)).Fiber

section SmoothField

variable {Fiber : Type u}
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
  [FiniteDimensional Real Fiber]

private abbrev JetCore :=
  actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
    period hPeriod (Fiber := Fiber)

/-- The raw smooth-field representatives obey the coordinate changes of the
constant-fiber second-jet core. -/
theorem throatSmoothFieldSecondOrderJetLocalRepresentative_compatible
    (field : SmoothThroatField period hPeriod Fiber)
    (first second current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod second) :
    (JetCore period hPeriod).coordChange first second current
        (throatSmoothFieldSecondOrderJetLocalRepresentative
          period hPeriod field first current) =
      throatSmoothFieldSecondOrderJetLocalRepresentative
        period hPeriod field second current := by
  have hFirst : current ∈
      (extChartAt throatCoverModelWithCorners first).source := by
    exact hCurrent.1
  have hSecond : current ∈
      (extChartAt throatCoverModelWithCorners second).source := by
    exact hCurrent.2
  change actualThroatConstantFiberSecondOrderJetCoordChange
      period hPeriod (Fiber := Fiber) first second current
        (throatSmoothFieldSecondOrderJetLocalRepresentative
          period hPeriod field first current) = _
  rw [actualThroatConstantFiberSecondOrderJetCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  unfold throatSmoothFieldSecondOrderJetLocalRepresentative
  rw [dif_pos hFirst, dif_pos hSecond]
  simpa only [actualThroatConstantFiberSecondOrderJetBaseChangeAt,
    throatSmoothFieldConstantFiberBaseChangeAt] using
    (throatSmoothFieldSecondOrderJetInChartAt_transition
      period hPeriod field first second current hFirst hSecond).symm

/-- The global total-space section selected from the compatible local second
jets of a smooth fixed-fiber throat field. -/
def actualThroatSmoothFieldSecondOrderJetVectorBundleSection
    (field : SmoothThroatField period hPeriod Fiber) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
        period hPeriod Fiber :=
  fun current ↦ TotalSpace.mk'
    (ActualThroatConstantFiberSecondOrderJet Fiber) current
      (vectorBundleCoreSectionOfLocalRepresentatives
        (JetCore period hPeriod)
        (throatSmoothFieldSecondOrderJetLocalRepresentative
          period hPeriod field) current)

/-- The assembled fixed-fiber second-jet section is globally `C∞`. -/
theorem actualThroatSmoothFieldSecondOrderJetVectorBundleSection_contMDiff
    (field : SmoothThroatField period hPeriod Fiber) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberSecondOrderJet Fiber))) ∞
      (actualThroatSmoothFieldSecondOrderJetVectorBundleSection
        period hPeriod field) := by
  letI : (JetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := Fiber)
  apply vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    throatCoverModelWithCorners (JetCore period hPeriod)
    (throatSmoothFieldSecondOrderJetLocalRepresentative
      period hPeriod field)
  · intro first second current hCurrent
    exact throatSmoothFieldSecondOrderJetLocalRepresentative_compatible
      period hPeriod field first second current hCurrent
  · intro index
    exact
      throatSmoothFieldSecondOrderJetLocalRepresentative_contMDiffOn
        period hPeriod field index

/-- The zero-order component of the assembled second jet is the original
smooth throat field. -/
@[simp]
theorem actualThroatSmoothFieldSecondOrderJetVectorBundleSection_value
    (field : SmoothThroatField period hPeriod Fiber)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSmoothFieldSecondOrderJetVectorBundleSection
      period hPeriod field current).2.value = field current := by
  change
    (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod field
      current current).value = field current
  unfold throatSmoothFieldSecondOrderJetLocalRepresentative
  split
  · rw [throatSmoothFieldSecondOrderJetInChartAt_value]
  · exact (by
      exfalso
      apply ‹current ∉
        (extChartAt throatCoverModelWithCorners current).source›
      exact mem_extChartAt_source current)

/-- At the preferred centered chart, the descended fiber is exactly the
previously defined chartwise second jet. -/
theorem actualThroatSmoothFieldSecondOrderJetVectorBundleSection_centeredJet
    (field : SmoothThroatField period hPeriod Fiber)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSmoothFieldSecondOrderJetVectorBundleSection
      period hPeriod field current).2 =
      smoothThroatFieldSecondOrderJetAt period hPeriod field current := by
  change
    throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod field
        current current =
      smoothThroatFieldSecondOrderJetAt period hPeriod field current
  rw [throatSmoothFieldSecondOrderJetLocalRepresentative,
    dif_pos (mem_extChartAt_source current)]
  rfl

end SmoothField

/-! ## The three actual LL sections -/

/-- Smooth second-jet section of the auxiliary LL metric. -/
def globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
    (configuration : GlobalFieldConfiguration period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
        period hPeriod LLMetricFiber :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection period hPeriod
    configuration.coefficientFields.llAuxMetric

/-- Smooth second-jet section of the real LL measure field. -/
def globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
    (configuration : GlobalFieldConfiguration period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
        period hPeriod Real :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection period hPeriod
    configuration.coefficientFields.llMeasure

/-- Smooth second-jet section of the LL vector field. -/
def globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
    (configuration : GlobalFieldConfiguration period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
        period hPeriod LLFieldFiber :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection period hPeriod
    configuration.coefficientFields.llField

/-- The three descended LL second-jet sections. -/
structure GlobalLLSecondOrderJetVectorBundleSections where
  llAuxMetric : EffectiveThroat period hPeriod →
    ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
      period hPeriod LLMetricFiber
  llMeasure : EffectiveThroat period hPeriod →
    ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
      period hPeriod Real
  llField : EffectiveThroat period hPeriod →
    ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
      period hPeriod LLFieldFiber

/-- LL section triplet of a genuine global Program-P configuration. -/
def globalFieldConfigurationLLSecondOrderJetVectorBundleSections
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalLLSecondOrderJetVectorBundleSections period hPeriod where
  llAuxMetric :=
    globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
      period hPeriod configuration
  llMeasure :=
    globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
      period hPeriod configuration
  llField :=
    globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
      period hPeriod configuration

theorem globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalFieldConfiguration period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberSecondOrderJet LLMetricFiber))) ∞
      (globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
        period hPeriod configuration) :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_contMDiff
    period hPeriod configuration.coefficientFields.llAuxMetric

theorem globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalFieldConfiguration period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberSecondOrderJet Real))) ∞
      (globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
        period hPeriod configuration) :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_contMDiff
    period hPeriod configuration.coefficientFields.llMeasure

theorem globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalFieldConfiguration period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberSecondOrderJet LLFieldFiber))) ∞
      (globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
        period hPeriod configuration) :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_contMDiff
    period hPeriod configuration.coefficientFields.llField

@[simp]
theorem globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2.value =
        configuration.coefficientFields.llAuxMetric current :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_value
    period hPeriod configuration.coefficientFields.llAuxMetric current

@[simp]
theorem globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2.value =
        configuration.coefficientFields.llMeasure current :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_value
    period hPeriod configuration.coefficientFields.llMeasure current

@[simp]
theorem globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection_value
    (configuration : GlobalFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2.value =
        configuration.coefficientFields.llField current :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_value
    period hPeriod configuration.coefficientFields.llField current

theorem globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection_jet
    (configuration : GlobalFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2 =
      (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration current).llAuxMetric :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_centeredJet
    period hPeriod configuration.coefficientFields.llAuxMetric current

theorem globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection_jet
    (configuration : GlobalFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2 =
      (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration current).llMeasure :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_centeredJet
    period hPeriod configuration.coefficientFields.llMeasure current

theorem globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection_jet
    (configuration : GlobalFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2 =
      (globalFieldConfigurationLLChartwiseSecondOrderJetsAt
        period hPeriod configuration current).llField :=
  actualThroatSmoothFieldSecondOrderJetVectorBundleSection_centeredJet
    period hPeriod configuration.coefficientFields.llField current

/-! ## Gauge-fixed wrappers -/

def globalGaugeFixedFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
        period hPeriod LLMetricFiber :=
  globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
        period hPeriod Real :=
  globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatConstantFiberSecondOrderJetBundleTotalSpace
        period hPeriod LLFieldFiber :=
  globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
    period hPeriod configuration.physical

def globalGaugeFixedFieldConfigurationLLSecondOrderJetVectorBundleSections
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalLLSecondOrderJetVectorBundleSections period hPeriod :=
  globalFieldConfigurationLLSecondOrderJetVectorBundleSections
    period hPeriod configuration.physical

theorem globalGaugeFixedFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberSecondOrderJet LLMetricFiber))) ∞
      (globalGaugeFixedFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
        period hPeriod configuration) :=
  globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection_contMDiff
    period hPeriod configuration.physical

theorem globalGaugeFixedFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberSecondOrderJet Real))) ∞
      (globalGaugeFixedFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
        period hPeriod configuration) :=
  globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection_contMDiff
    period hPeriod configuration.physical

theorem globalGaugeFixedFieldConfigurationLLFieldSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real
          (ActualThroatConstantFiberSecondOrderJet LLFieldFiber))) ∞
      (globalGaugeFixedFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
        period hPeriod configuration) :=
  globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection_contMDiff
    period hPeriod configuration.physical

@[simp]
theorem globalGaugeFixedFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2.value =
        configuration.physical.coefficientFields.llAuxMetric current :=
  globalFieldConfigurationLLAuxMetricSecondOrderJetVectorBundleSection_value
    period hPeriod configuration.physical current

@[simp]
theorem globalGaugeFixedFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2.value =
        configuration.physical.coefficientFields.llMeasure current :=
  globalFieldConfigurationLLMeasureSecondOrderJetVectorBundleSection_value
    period hPeriod configuration.physical current

@[simp]
theorem globalGaugeFixedFieldConfigurationLLFieldSecondOrderJetVectorBundleSection_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedFieldConfigurationLLFieldSecondOrderJetVectorBundleSection
      period hPeriod configuration current).2.value =
        configuration.physical.coefficientFields.llField current :=
  globalFieldConfigurationLLFieldSecondOrderJetVectorBundleSection_value
    period hPeriod configuration.physical current

end
end P0EFTJanusProgramPActualLLSecondOrderJetSmoothVectorBundleSections4D
end JanusFormal
