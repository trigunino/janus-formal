import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

/-!
# Smooth metric third-jet vector-bundle section

Compatible local metric third jets assemble into a global smooth section of
the actual throat metric third-jet bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleSection4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set Bundle
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

private abbrev MetricThirdJetCore :=
  throatMetricThirdOrderJetVectorBundleCore period hPeriod

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Total space of the actual throat metric third-jet bundle. -/
abbrev ActualThroatMetricThirdOrderJetBundleTotalSpace :=
  Bundle.TotalSpace MetricThirdJet (MetricThirdJetCore period hPeriod).Fiber

/-- Extracted metric third jets obey the coordinate changes of the metric
core. -/
theorem actualThroatMetricThirdOrderJetLocalRepresentative_compatible
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (MetricThirdJetCore period hPeriod).coordChange first second current
        (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
          tensor first current) =
      actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
        tensor second current := by
  change throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
    first second current
      (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
        tensor first current) = _
  rw [throatMetricThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatMetricThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  unfold actualThroatMetricThirdOrderJetLocalRepresentative
  rw [dif_pos hCurrent.1, dif_pos hCurrent.2]
  simpa only [throatMetricSecondOrderJetFrameChartAt_frameAnchor,
    throatMetricSecondOrderJetFrameChartAt_chartAnchor] using
    throatMetricThirdOrderJetSemidirectTransportAt_extracted period hPeriod
      tensor
      (throatMetricSecondOrderJetFrameChartAt period hPeriod first current
        hCurrent.1)
      (throatMetricSecondOrderJetFrameChartAt period hPeriod second current
        hCurrent.2)

/-- The global section selected from the compatible local metric third
jets. -/
def actualThroatMetricThirdOrderJetVectorBundleSection
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatMetricThirdOrderJetBundleTotalSpace period hPeriod :=
  fun current ↦ TotalSpace.mk' MetricThirdJet current
    (vectorBundleCoreSectionOfLocalRepresentatives
      (MetricThirdJetCore period hPeriod)
      (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
        tensor) current)

/-- In every valid core chart, the global section has the prescribed local
representative as fiber coordinate. -/
theorem actualThroatMetricThirdOrderJetVectorBundleSection_localRepresentative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    (((MetricThirdJetCore period hPeriod).localTriv index)
      (actualThroatMetricThirdOrderJetVectorBundleSection period hPeriod
        tensor current)).2 =
      actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
        tensor index current := by
  exact vectorBundleCoreSectionOfLocalRepresentatives_localCoordinate
    (MetricThirdJetCore period hPeriod)
    (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod tensor)
    (actualThroatMetricThirdOrderJetLocalRepresentative_compatible
      period hPeriod tensor) index current hCurrent

/-- Equivalently, every valid local coordinate is the arbitrary frame/chart
metric third-jet extraction. -/
theorem actualThroatMetricThirdOrderJetVectorBundleSection_localCoordinate
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    (((MetricThirdJetCore period hPeriod).localTriv index)
      (actualThroatMetricThirdOrderJetVectorBundleSection period hPeriod
        tensor current)).2 =
      throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
        index.1 index.2 current hCurrent.1 hCurrent.2 := by
  rw [actualThroatMetricThirdOrderJetVectorBundleSection_localRepresentative
    period hPeriod tensor index current hCurrent]
  exact actualThroatMetricThirdOrderJetLocalRepresentative_eq_of_mem
    period hPeriod tensor index current hCurrent

private theorem metricThirdJetCore_isContMDiff :
    (MetricThirdJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  convert throatMetricThirdOrderJetVectorBundleCore_isContMDiff
    period hPeriod using 1

/-- Compatible smooth local metric third jets assemble into a global `C∞`
section. -/
theorem actualThroatMetricThirdOrderJetVectorBundleSection_contMDiff
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real MetricThirdJet)) ∞
      (actualThroatMetricThirdOrderJetVectorBundleSection
        period hPeriod tensor) := by
  letI : (MetricThirdJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    metricThirdJetCore_isContMDiff period hPeriod
  apply vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    throatCoverModelWithCorners (MetricThirdJetCore period hPeriod)
    (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod tensor)
  · intro first second current hCurrent
    exact actualThroatMetricThirdOrderJetLocalRepresentative_compatible
      period hPeriod tensor first second current hCurrent
  · intro index
    exact actualThroatMetricThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod tensor index

/-- The global third-jet section truncates exactly to the existing global
second-jet section. -/
@[simp]
theorem actualThroatMetricThirdOrderJetVectorBundleSection_truncate
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatMetricThirdOrderJetVectorBundleSection period hPeriod
      tensor current).2.toFramedSecondOrderJet =
      (actualThroatMetricSecondOrderJetVectorBundleSection period hPeriod
        tensor current).2 := by
  change
    (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod tensor
      (throatMetricSecondOrderJetBundleIndexAt period hPeriod current)
        current).toFramedSecondOrderJet =
      actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod tensor
        (throatMetricSecondOrderJetBundleIndexAt period hPeriod current) current
  exact actualThroatMetricThirdOrderJetLocalRepresentative_truncate
    period hPeriod tensor
      (throatMetricSecondOrderJetBundleIndexAt period hPeriod current) current

/-- At the preferred centered index, the section fiber is the corresponding
arbitrary-frame/chart metric third jet. -/
theorem actualThroatMetricThirdOrderJetVectorBundleSection_centeredJet
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatMetricThirdOrderJetVectorBundleSection period hPeriod
      tensor current).2 =
      throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
        current current current
        (FiberBundle.mem_baseSet_trivializationAt' current)
        (mem_extChartAt_source current) := by
  change actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
      tensor (throatMetricSecondOrderJetBundleIndexAt period hPeriod current)
        current = _
  rw [actualThroatMetricThirdOrderJetLocalRepresentative,
    dif_pos (mem_throatMetricSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

/-! ## Actual induced metric sections -/

/-- Smooth metric third-jet section of one actual induced sector metric. -/
def globalGaugeFixedInducedMetricThirdOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    EffectiveThroat period hPeriod →
      ActualThroatMetricThirdOrderJetBundleTotalSpace period hPeriod :=
  actualThroatMetricThirdOrderJetVectorBundleSection period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)

theorem globalGaugeFixedInducedMetricThirdOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real MetricThirdJet)) ∞
      (globalGaugeFixedInducedMetricThirdOrderJetVectorBundleSection
        period hPeriod configuration sector) :=
  actualThroatMetricThirdOrderJetVectorBundleSection_contMDiff period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)

/-- The physical third-jet section truncates to the existing physical
second-jet section. -/
@[simp]
theorem globalGaugeFixedInducedMetricThirdOrderJetVectorBundleSection_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedInducedMetricThirdOrderJetVectorBundleSection period
      hPeriod configuration sector current).2.toFramedSecondOrderJet =
      (globalGaugeFixedInducedMetricSecondOrderJetVectorBundleSection period
        hPeriod configuration sector current).2 :=
  actualThroatMetricThirdOrderJetVectorBundleSection_truncate period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)
    current

/-- At the preferred centered index, the physical section is the centered
arbitrary-frame/chart metric third-jet extraction. -/
theorem globalGaugeFixedInducedMetricThirdOrderJetVectorBundleSection_centeredJet
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedInducedMetricThirdOrderJetVectorBundleSection period
      hPeriod configuration sector current).2 =
      globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt period hPeriod
        configuration sector current current current
        (FiberBundle.mem_baseSet_trivializationAt' current)
        (mem_extChartAt_source current) := by
  change actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
      (globalGaugeFixedInducedMetricBySector period hPeriod configuration
        sector)
      (throatMetricSecondOrderJetBundleIndexAt period hPeriod current)
      current = _
  rw [actualThroatMetricThirdOrderJetLocalRepresentative,
    dif_pos (mem_throatMetricSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleSection4D
end JanusFormal
