import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

/-!
# Smooth SpinC third-jet vector-bundle section

Compatible local SpinC third jets assemble into a global smooth section of
the actual throat SpinC third-jet bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleSection4D

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
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

private abbrev SpinCThirdJetCore (choice : NormalRootChoice) :=
  throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Total space of the actual throat SpinC third-jet bundle. -/
abbrev ActualThroatSpinCThirdOrderJetBundleTotalSpace
    (choice : NormalRootChoice) :=
  Bundle.TotalSpace SpinCThirdJet
    (SpinCThirdJetCore period hPeriod choice).Fiber

/-- Extracted SpinC third jets obey the coordinate changes of the SpinC
core. -/
theorem actualThroatSpinCThirdOrderJetLocalRepresentative_compatible
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (SpinCThirdJetCore period hPeriod choice).coordChange first second current
        (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
          choice state first current) =
      actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
        choice state second current := by
  change throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod
    choice first second current
      (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
        choice state first current) = _
  rw [throatSpinCThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatSpinCThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod choice first second current hCurrent]
  unfold actualThroatSpinCThirdOrderJetLocalRepresentative
  rw [dif_pos hCurrent.1, dif_pos hCurrent.2]
  simpa only [
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor] using
    throatSpinCThirdOrderJetSemidirectTransportAt_extracted period hPeriod
      choice state
      (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod
        first current hCurrent.1)
      (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod
        second current hCurrent.2)

/-- The global section selected from the compatible local SpinC third jets. -/
def actualThroatSpinCThirdOrderJetVectorBundleSection
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    EffectiveThroat period hPeriod →
      ActualThroatSpinCThirdOrderJetBundleTotalSpace period hPeriod choice :=
  fun current ↦ TotalSpace.mk' SpinCThirdJet current
    (vectorBundleCoreSectionOfLocalRepresentatives
      (SpinCThirdJetCore period hPeriod choice)
      (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
        choice state) current)

/-- In every valid core chart, the global section has the prescribed local
representative as fiber coordinate. -/
theorem actualThroatSpinCThirdOrderJetVectorBundleSection_localRepresentative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (((SpinCThirdJetCore period hPeriod choice).localTriv index)
      (actualThroatSpinCThirdOrderJetVectorBundleSection period hPeriod
        choice state current)).2 =
      actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
        choice state index current := by
  exact vectorBundleCoreSectionOfLocalRepresentatives_localCoordinate
    (SpinCThirdJetCore period hPeriod choice)
    (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
      choice state)
    (actualThroatSpinCThirdOrderJetLocalRepresentative_compatible
      period hPeriod choice state) index current hCurrent

/-- Equivalently, every valid local coordinate is the arbitrary
trivialization/chart SpinC third-jet extraction. -/
theorem actualThroatSpinCThirdOrderJetVectorBundleSection_localCoordinate
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (((SpinCThirdJetCore period hPeriod choice).localTriv index)
      (actualThroatSpinCThirdOrderJetVectorBundleSection period hPeriod
        choice state current)).2 =
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
        choice state index.1 index.2 current hCurrent.1 hCurrent.2 := by
  rw [actualThroatSpinCThirdOrderJetVectorBundleSection_localRepresentative
    period hPeriod choice state index current hCurrent]
  exact actualThroatSpinCThirdOrderJetLocalRepresentative_eq_of_mem
    period hPeriod choice state index current hCurrent

private theorem spinCThirdJetCore_isContMDiff
    (choice : NormalRootChoice) :
    (SpinCThirdJetCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  convert throatSpinCThirdOrderJetVectorBundleCore_isContMDiff
    period hPeriod choice using 1

/-- Compatible smooth local SpinC third jets assemble into a global `C∞`
section. -/
theorem actualThroatSpinCThirdOrderJetVectorBundleSection_contMDiff
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real SpinCThirdJet)) ∞
      (actualThroatSpinCThirdOrderJetVectorBundleSection
        period hPeriod choice state) := by
  letI : (SpinCThirdJetCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    spinCThirdJetCore_isContMDiff period hPeriod choice
  apply vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    throatCoverModelWithCorners (SpinCThirdJetCore period hPeriod choice)
    (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
      choice state)
  · intro first second current hCurrent
    exact actualThroatSpinCThirdOrderJetLocalRepresentative_compatible
      period hPeriod choice state first second current hCurrent
  · intro index
    exact actualThroatSpinCThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod choice state index

/-- The global third-jet section truncates exactly to the existing global
second-jet section. -/
@[simp]
theorem actualThroatSpinCThirdOrderJetVectorBundleSection_truncate
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSpinCThirdOrderJetVectorBundleSection period hPeriod
      choice state current).2.toFramedSecondOrderJet =
      (actualThroatSpinCSecondOrderJetVectorBundleSection period hPeriod
        choice state current).2 := by
  change
    (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod choice
      state (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current)
        current).toFramedSecondOrderJet =
      actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod choice
        state (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current)
          current
  exact actualThroatSpinCThirdOrderJetLocalRepresentative_truncate
    period hPeriod choice state
      (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current) current

/-- At the preferred centered index, the section fiber is the corresponding
arbitrary-trivialization SpinC third jet. -/
theorem actualThroatSpinCThirdOrderJetVectorBundleSection_centeredJet
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatSpinCThirdOrderJetVectorBundleSection period hPeriod
      choice state current).2 =
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
        choice state
          (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current).1
          current current
          (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
            period hPeriod current).1
          (mem_extChartAt_source current) := by
  change actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
      choice state
        (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current)
        current = _
  rw [actualThroatSpinCThirdOrderJetLocalRepresentative,
    dif_pos (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

/-! ## Actual gauge-fixed SpinC matter sections -/

/-- Smooth SpinC matter third-jet section of one physical sector. -/
def globalGaugeFixedSpinCMatterThirdOrderJetVectorBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    EffectiveThroat period hPeriod →
      ActualThroatSpinCThirdOrderJetBundleTotalSpace period hPeriod
        .positiveQuarter :=
  actualThroatSpinCThirdOrderJetVectorBundleSection period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector)

theorem globalGaugeFixedSpinCMatterThirdOrderJetVectorBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real SpinCThirdJet)) ∞
      (globalGaugeFixedSpinCMatterThirdOrderJetVectorBundleSection
        period hPeriod configuration sector) :=
  actualThroatSpinCThirdOrderJetVectorBundleSection_contMDiff period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector)

/-- The physical third-jet section truncates to the existing physical
second-jet section. -/
@[simp]
theorem globalGaugeFixedSpinCMatterThirdOrderJetVectorBundleSection_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedSpinCMatterThirdOrderJetVectorBundleSection period hPeriod
      configuration sector current).2.toFramedSecondOrderJet =
      (globalGaugeFixedSpinCMatterSecondOrderJetVectorBundleSection period
        hPeriod configuration sector current).2 :=
  actualThroatSpinCThirdOrderJetVectorBundleSection_truncate period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) current

/-- At the preferred centered index, the physical section is the centered
arbitrary-trivialization SpinC matter third-jet extraction. -/
theorem globalGaugeFixedSpinCMatterThirdOrderJetVectorBundleSection_centeredJet
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedSpinCMatterThirdOrderJetVectorBundleSection
      period hPeriod configuration sector current).2 =
      globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt
        period hPeriod configuration sector
          (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current).1
          current current
          (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
            period hPeriod current).1
          (mem_extChartAt_source current) := by
  change actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
      .positiveQuarter (configuration.physical.spinCMatter sector)
        (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current)
        current = _
  rw [actualThroatSpinCThirdOrderJetLocalRepresentative,
    dif_pos (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleSection4D
end JanusFormal
