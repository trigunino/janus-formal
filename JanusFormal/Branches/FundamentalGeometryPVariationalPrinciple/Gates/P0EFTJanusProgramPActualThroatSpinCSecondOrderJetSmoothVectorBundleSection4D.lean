import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

/-!
# Smooth SpinC second-jet vector-bundle section

Compatible local SpinC second jets assemble into a global smooth section of
the actual throat SpinC second-jet bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleSection4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

private abbrev SpinCJetCore (choice : NormalRootChoice) :=
  throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Total space of the actual throat SpinC second-jet bundle. -/
abbrev ActualThroatSpinCSecondOrderJetBundleTotalSpace
    (choice : NormalRootChoice) :=
  Bundle.TotalSpace SpinCJet (SpinCJetCore period hPeriod choice).Fiber

/-- Extracted SpinC jets obey the coordinate changes of the SpinC core. -/
theorem actualThroatSpinCSecondOrderJetLocalRepresentative_compatible
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (SpinCJetCore period hPeriod choice).coordChange first second current
        (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
          choice state first current) =
      actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
        choice state second current := by
  change throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
    first second current
      (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
        choice state first current) = _
  rw [throatSpinCSecondOrderJetBundleCoordChange_apply_of_mem
    period hPeriod choice first second current hCurrent]
  unfold actualThroatSpinCSecondOrderJetLocalRepresentative
  rw [dif_pos hCurrent.1, dif_pos hCurrent.2]
  simpa only [
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
    throatSpinCSecondOrderJetSemidirectTransportAt_extracted period hPeriod
      choice state
      (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod
        first current hCurrent.1)
      (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod
        second current hCurrent.2)

/-- The global section selected from the compatible local SpinC jets. -/
def actualThroatSpinCSecondOrderJetVectorBundleSection
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    EffectiveThroat period hPeriod →
      ActualThroatSpinCSecondOrderJetBundleTotalSpace period hPeriod choice :=
  fun current ↦ TotalSpace.mk' SpinCJet current
    (vectorBundleCoreSectionOfLocalRepresentatives
      (SpinCJetCore period hPeriod choice)
      (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
        choice state) current)

/-- In every valid core chart, the global section has the prescribed local
representative as fiber coordinate. -/
theorem actualThroatSpinCSecondOrderJetVectorBundleSection_localRepresentative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (((SpinCJetCore period hPeriod choice).localTriv index)
      (actualThroatSpinCSecondOrderJetVectorBundleSection period hPeriod
        choice state current)).2 =
      actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
        choice state index current := by
  exact vectorBundleCoreSectionOfLocalRepresentatives_localCoordinate
    (SpinCJetCore period hPeriod choice)
    (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
      choice state)
    (actualThroatSpinCSecondOrderJetLocalRepresentative_compatible
      period hPeriod choice state) index current hCurrent

/-- Equivalently, every valid local coordinate is the arbitrary
trivialization/chart SpinC second-jet extraction. -/
theorem actualThroatSpinCSecondOrderJetVectorBundleSection_localCoordinate
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (((SpinCJetCore period hPeriod choice).localTriv index)
      (actualThroatSpinCSecondOrderJetVectorBundleSection period hPeriod
        choice state current)).2 =
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
        choice state index.1 index.2 current hCurrent.1 hCurrent.2 := by
  rw [actualThroatSpinCSecondOrderJetVectorBundleSection_localRepresentative
    period hPeriod choice state index current hCurrent]
  exact actualThroatSpinCSecondOrderJetLocalRepresentative_eq_of_mem
    period hPeriod choice state index current hCurrent

private theorem spinCJetCore_isContMDiff
    (choice : NormalRootChoice) :
    (SpinCJetCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  convert throatSpinCSecondOrderJetVectorBundleCore_isContMDiff
    period hPeriod choice using 1

/-- Compatible smooth local SpinC jets assemble into a global `C∞`
section. -/
theorem actualThroatSpinCSecondOrderJetVectorBundleSection_contMDiff
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real SpinCJet)) ∞
      (actualThroatSpinCSecondOrderJetVectorBundleSection
        period hPeriod choice state) := by
  letI : (SpinCJetCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    spinCJetCore_isContMDiff period hPeriod choice
  apply vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    throatCoverModelWithCorners (SpinCJetCore period hPeriod choice)
    (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
      choice state)
  · intro first second current hCurrent
    exact actualThroatSpinCSecondOrderJetLocalRepresentative_compatible
      period hPeriod choice state first second current hCurrent
  · intro index
    exact actualThroatSpinCSecondOrderJetLocalRepresentative_contMDiffOn
      period hPeriod choice state index

/-- At the preferred centered index, the section fiber is the corresponding
arbitrary-trivialization SpinC second jet. -/
theorem actualThroatSpinCSecondOrderJetVectorBundleSection_centeredJet
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSpinCSecondOrderJetVectorBundleSection period hPeriod
      choice state current).2 =
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
        choice state
          (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current).1
          current current
          (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
            period hPeriod current).1
          (mem_extChartAt_source current) := by
  change actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
      choice state
        (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current)
        current = _
  rw [actualThroatSpinCSecondOrderJetLocalRepresentative,
    dif_pos (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

/-! ## Actual gauge-fixed SpinC matter sections -/

/-- Smooth SpinC matter second-jet section of one physical sector. -/
def globalGaugeFixedSpinCMatterSecondOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    EffectiveThroat period hPeriod →
      ActualThroatSpinCSecondOrderJetBundleTotalSpace period hPeriod
        .positiveQuarter :=
  actualThroatSpinCSecondOrderJetVectorBundleSection period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector)

theorem globalGaugeFixedSpinCMatterSecondOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real SpinCJet)) ∞
      (globalGaugeFixedSpinCMatterSecondOrderJetVectorBundleSection
        period hPeriod configuration sector) :=
  actualThroatSpinCSecondOrderJetVectorBundleSection_contMDiff period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector)

/-- At the preferred centered index, the physical section is exactly the
previous SpinC matter second-jet extraction. -/
theorem globalGaugeFixedSpinCMatterSecondOrderJetVectorBundleSection_centeredJet
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedSpinCMatterSecondOrderJetVectorBundleSection
      period hPeriod configuration sector current).2 =
      globalGaugeFixedSpinCMatterSecondOrderJetsAt period hPeriod configuration
        (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current).1
        current
        (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
          period hPeriod current).1 sector := by
  change actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
      .positiveQuarter (configuration.physical.spinCMatter sector)
        (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current)
        current = _
  rw [actualThroatSpinCSecondOrderJetLocalRepresentative,
    dif_pos (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  simpa only [throatSpinCSecondOrderJetBundleIndexAt,
    globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt] using
    globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt_diagonal
      period hPeriod configuration sector
      (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current).1 current
      (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
        period hPeriod current).1

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleSection4D
end JanusFormal
