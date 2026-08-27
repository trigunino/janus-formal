import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

/-!
# Smooth metric second-jet vector-bundle section

Compatible local metric second jets assemble into a global smooth section of
the actual throat metric second-jet bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleSection4D

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
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricJet :=
  FramedSecondOrderJet ThroatCoverCoordinates TensorModel

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

private abbrev MetricJetCore :=
  throatMetricSecondOrderJetVectorBundleCore period hPeriod

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

/-- Total space of the actual throat metric second-jet bundle. -/
abbrev ActualThroatMetricSecondOrderJetBundleTotalSpace :=
  Bundle.TotalSpace MetricJet (MetricJetCore period hPeriod).Fiber

/-- Extracted metric jets obey the coordinate changes of the metric core. -/
theorem actualThroatMetricSecondOrderJetLocalRepresentative_compatible
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (MetricJetCore period hPeriod).coordChange first second current
        (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
          tensor first current) =
      actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        tensor second current := by
  change throatMetricSecondOrderJetBundleCoordChange period hPeriod
    first second current
      (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        tensor first current) = _
  rw [throatMetricSecondOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  unfold actualThroatMetricSecondOrderJetLocalRepresentative
  rw [dif_pos hCurrent.1, dif_pos hCurrent.2]
  simpa only [throatMetricSecondOrderJetFrameChartAt_frameAnchor,
    throatMetricSecondOrderJetFrameChartAt_chartAnchor] using
    throatMetricSecondOrderJetSemidirectTransportAt_extracted period hPeriod
      tensor
      (throatMetricSecondOrderJetFrameChartAt period hPeriod first current
        hCurrent.1)
      (throatMetricSecondOrderJetFrameChartAt period hPeriod second current
        hCurrent.2)

/-- The global section selected from the compatible local metric jets. -/
def actualThroatMetricSecondOrderJetVectorBundleSection
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    EffectiveThroat period hPeriod →
      ActualThroatMetricSecondOrderJetBundleTotalSpace period hPeriod :=
  fun current ↦ TotalSpace.mk' MetricJet current
    (vectorBundleCoreSectionOfLocalRepresentatives
      (MetricJetCore period hPeriod)
      (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        tensor) current)

/-- In every valid core chart, the global section has the prescribed
extracted metric jet as local coordinate. -/
theorem actualThroatMetricSecondOrderJetVectorBundleSection_localCoordinate
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    (((MetricJetCore period hPeriod).localTriv index)
      (actualThroatMetricSecondOrderJetVectorBundleSection period hPeriod
        tensor current)).2 =
      throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        index.1 index.2 current hCurrent.1 hCurrent.2 := by
  have hLocal :=
    vectorBundleCoreSectionOfLocalRepresentatives_localCoordinate
      (MetricJetCore period hPeriod)
      (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        tensor)
      (actualThroatMetricSecondOrderJetLocalRepresentative_compatible
        period hPeriod tensor) index current hCurrent
  simpa only [actualThroatMetricSecondOrderJetVectorBundleSection,
    actualThroatMetricSecondOrderJetLocalRepresentative,
    dif_pos hCurrent] using hLocal

private theorem metricJetCore_isContMDiff :
    (MetricJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  convert throatMetricSecondOrderJetVectorBundleCore_isContMDiff
    period hPeriod using 1

/-- Compatible smooth local metric jets assemble into a global `C∞`
section. -/
theorem actualThroatMetricSecondOrderJetVectorBundleSection_contMDiff
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real MetricJet)) ∞
      (actualThroatMetricSecondOrderJetVectorBundleSection
        period hPeriod tensor) := by
  letI : (MetricJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    metricJetCore_isContMDiff period hPeriod
  apply vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    throatCoverModelWithCorners (MetricJetCore period hPeriod)
    (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
      tensor)
  · intro first second current hCurrent
    exact actualThroatMetricSecondOrderJetLocalRepresentative_compatible
      period hPeriod tensor first second current hCurrent
  · intro index
    exact actualThroatMetricSecondOrderJetLocalRepresentative_contMDiffOn
      period hPeriod tensor index

/-- At the preferred diagonal index, the section fiber is the centered
extracted metric jet. -/
theorem actualThroatMetricSecondOrderJetVectorBundleSection_centeredJet
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatMetricSecondOrderJetVectorBundleSection period hPeriod
      tensor current).2 =
      throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        current current current
        (FiberBundle.mem_baseSet_trivializationAt' current)
        (mem_extChartAt_source current) := by
  change actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
      tensor (throatMetricSecondOrderJetBundleIndexAt period hPeriod current)
        current = _
  rw [actualThroatMetricSecondOrderJetLocalRepresentative,
    dif_pos (mem_throatMetricSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

/-! ## Actual induced metric sections -/

/-- Smooth metric second-jet section of one actual induced sector metric. -/
def globalGaugeFixedInducedMetricSecondOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    EffectiveThroat period hPeriod →
      ActualThroatMetricSecondOrderJetBundleTotalSpace period hPeriod :=
  actualThroatMetricSecondOrderJetVectorBundleSection period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)

theorem globalGaugeFixedInducedMetricSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real MetricJet)) ∞
      (globalGaugeFixedInducedMetricSecondOrderJetVectorBundleSection
        period hPeriod configuration sector) :=
  actualThroatMetricSecondOrderJetVectorBundleSection_contMDiff period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)

/-- At the diagonal center, the induced-metric section is exactly the
previous centered actual throat metric second jet. -/
theorem globalGaugeFixedInducedMetricSecondOrderJetVectorBundleSection_centeredJet
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedInducedMetricSecondOrderJetVectorBundleSection
      period hPeriod configuration sector current).2 =
      globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod
        configuration sector current := by
  rw [globalGaugeFixedInducedMetricSecondOrderJetVectorBundleSection,
    actualThroatMetricSecondOrderJetVectorBundleSection_centeredJet]
  rfl

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleSection4D
end JanusFormal
