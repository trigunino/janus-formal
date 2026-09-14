import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

/-!
# Smooth gauge third-jet vector-bundle section

Compatible local gauge third jets assemble into a global smooth section of
the actual throat gauge third-jet bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleSection4D

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
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescentLocalTrivialization4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPVectorBundleCoreCompatibleLocalSection4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

private abbrev GaugeThirdJetCore :=
  throatGaugeThirdOrderJetVectorBundleCore period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Total space of the actual throat gauge third-jet bundle. -/
abbrev ActualThroatGaugeThirdOrderJetBundleTotalSpace :=
  Bundle.TotalSpace GaugeThirdJet (GaugeThirdJetCore period hPeriod).Fiber

/-- Extracted gauge third jets obey the coordinate changes of the gauge
core. -/
theorem actualThroatGaugeThirdOrderJetLocalRepresentative_compatible
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    (GaugeThirdJetCore period hPeriod).coordChange first second current
        (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
          potential component first current) =
      actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
        potential component second current := by
  change throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
    first second current
      (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
        potential component first current) = _
  rw [throatGaugeThirdOrderJetBundleContinuousCoordChange_apply]
  rw [throatGaugeThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  unfold actualThroatGaugeThirdOrderJetLocalRepresentative
  rw [dif_pos hCurrent.1, dif_pos hCurrent.2]
  simpa only [zeroThroatGaugeSecondOrderJetPresentationAt] using
    throatGaugeThirdOrderJetSemidirectTransportAt_extracted period hPeriod
      potential component
      (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
        current hCurrent.1)
      (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
        current hCurrent.2)

/-- The global section selected from the compatible local gauge third jets. -/
def actualThroatGaugeThirdOrderJetVectorBundleSection
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    EffectiveThroat period hPeriod →
      ActualThroatGaugeThirdOrderJetBundleTotalSpace period hPeriod :=
  fun current ↦ TotalSpace.mk' GaugeThirdJet current
    (vectorBundleCoreSectionOfLocalRepresentatives
      (GaugeThirdJetCore period hPeriod)
      (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
        potential component) current)

/-- In every valid core chart, the global section has the prescribed local
representative as fiber coordinate. -/
theorem actualThroatGaugeThirdOrderJetVectorBundleSection_localRepresentative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    (((GaugeThirdJetCore period hPeriod).localTriv index)
      (actualThroatGaugeThirdOrderJetVectorBundleSection period hPeriod
        potential component current)).2 =
      actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
        potential component index current := by
  exact vectorBundleCoreSectionOfLocalRepresentatives_localCoordinate
    (GaugeThirdJetCore period hPeriod)
    (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
      potential component)
    (actualThroatGaugeThirdOrderJetLocalRepresentative_compatible
      period hPeriod potential component) index current hCurrent

/-- Every valid local coordinate is the arbitrary frame/base-chart gauge
third-jet extraction. -/
theorem actualThroatGaugeThirdOrderJetVectorBundleSection_localCoordinate
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    (((GaugeThirdJetCore period hPeriod).localTriv index)
      (actualThroatGaugeThirdOrderJetVectorBundleSection period hPeriod
        potential component current)).2 =
      throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
        component index.1 index.2 current hCurrent.1 hCurrent.2 := by
  rw [actualThroatGaugeThirdOrderJetVectorBundleSection_localRepresentative
    period hPeriod potential component index current hCurrent]
  exact actualThroatGaugeThirdOrderJetLocalRepresentative_eq_of_mem
    period hPeriod potential component index current hCurrent

private theorem gaugeThirdJetCore_isContMDiff :
    (GaugeThirdJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  convert throatGaugeThirdOrderJetVectorBundleCore_isContMDiff
    period hPeriod using 1

/-- Compatible smooth local gauge third jets assemble into a global `C∞`
section. -/
theorem actualThroatGaugeThirdOrderJetVectorBundleSection_contMDiff
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real GaugeThirdJet)) ∞
      (actualThroatGaugeThirdOrderJetVectorBundleSection
        period hPeriod potential component) := by
  letI : (GaugeThirdJetCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ :=
    gaugeThirdJetCore_isContMDiff period hPeriod
  apply vectorBundleCoreSectionOfLocalRepresentatives_contMDiff
    throatCoverModelWithCorners (GaugeThirdJetCore period hPeriod)
    (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
      potential component)
  · intro first second current hCurrent
    exact actualThroatGaugeThirdOrderJetLocalRepresentative_compatible
      period hPeriod potential component first second current hCurrent
  · intro index
    exact actualThroatGaugeThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod potential component index

/-- The global third-jet section truncates to the existing descended gauge
second-jet section. -/
@[simp]
theorem actualThroatGaugeThirdOrderJetVectorBundleSection_truncate
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatGaugeThirdOrderJetVectorBundleSection period hPeriod
      potential component current).2.toFramedSecondOrderJet =
      (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
        potential component current).2 := by
  let index := throatGaugeSecondOrderJetBundleIndexAt period hPeriod current
  have hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index :=
    mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt period hPeriod current
  change
    (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod potential
      component index current).toFramedSecondOrderJet = _
  rw [actualThroatGaugeThirdOrderJetLocalRepresentative_truncate]
  have hCoordinate :=
    actualThroatGaugeSecondOrderJetVectorBundleSection_localTriv_snd
      period hPeriod potential component index current hCurrent
  have hSection :
      (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
        potential component current).2 =
        throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
          component index.1 index.2 current hCurrent.1 hCurrent.2 := by
    calc
      (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
          potential component current).2 =
          (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).coordChange
            index index current
            (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
              potential component current).2 := by
        symm
        exact
          (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).coordChange_self
            index current hCurrent _
      _ = (((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
            index)
          (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
            potential component current)).2 := by
        rw [(throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv_apply]
        rfl
      _ = _ := hCoordinate
  unfold actualThroatGaugeSecondOrderJetLocalRepresentative
  rw [dif_pos hCurrent]
  exact hSection.symm

/-- At the preferred centered index, the section fiber is the corresponding
arbitrary-frame/base-chart gauge third jet. -/
theorem actualThroatGaugeThirdOrderJetVectorBundleSection_centeredJet
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatGaugeThirdOrderJetVectorBundleSection period hPeriod
      potential component current).2 =
      throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
        component current current current
        (FiberBundle.mem_baseSet_trivializationAt' current)
        (mem_extChartAt_source current) := by
  change actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
      potential component
        (throatGaugeSecondOrderJetBundleIndexAt period hPeriod current)
        current = _
  rw [actualThroatGaugeThirdOrderJetLocalRepresentative,
    dif_pos (mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

/-! ## Actual Candidate-A gauge sections -/

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Smooth Candidate-A gauge third-jet section of one sector and component. -/
def globalCandidateAThroatGaugeThirdOrderJetVectorBundleSection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2) :
    EffectiveThroat period hPeriod →
      ActualThroatGaugeThirdOrderJetBundleTotalSpace period hPeriod :=
  actualThroatGaugeThirdOrderJetVectorBundleSection period hPeriod
    (globalCandidateAThroatPotentialBySector period hPeriod data sector)
    component

theorem globalCandidateAThroatGaugeThirdOrderJetVectorBundleSection_contMDiff
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real GaugeThirdJet)) ∞
      (globalCandidateAThroatGaugeThirdOrderJetVectorBundleSection
        period hPeriod data sector component) :=
  actualThroatGaugeThirdOrderJetVectorBundleSection_contMDiff period hPeriod
    (globalCandidateAThroatPotentialBySector period hPeriod data sector)
    component

/-- The physical third-jet section truncates to the existing descended gauge
second-jet section. -/
@[simp]
theorem globalCandidateAThroatGaugeThirdOrderJetVectorBundleSection_truncate
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    (globalCandidateAThroatGaugeThirdOrderJetVectorBundleSection period hPeriod
      data sector component current).2.toFramedSecondOrderJet =
      (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data sector)
        component current).2 :=
  actualThroatGaugeThirdOrderJetVectorBundleSection_truncate period hPeriod
    (globalCandidateAThroatPotentialBySector period hPeriod data sector)
    component current

/-- At the preferred centered index, the physical section is the centered
Candidate-A gauge third-jet extraction. -/
theorem globalCandidateAThroatGaugeThirdOrderJetVectorBundleSection_centeredJet
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (current : EffectiveThroat period hPeriod) :
    (globalCandidateAThroatGaugeThirdOrderJetVectorBundleSection period hPeriod
      data sector component current).2 =
      globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt period hPeriod data
        sector component current current current
        (FiberBundle.mem_baseSet_trivializationAt' current)
        (mem_extChartAt_source current) := by
  change actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
      (globalCandidateAThroatPotentialBySector period hPeriod data sector)
      component (throatGaugeSecondOrderJetBundleIndexAt period hPeriod current)
      current = _
  rw [actualThroatGaugeThirdOrderJetLocalRepresentative,
    dif_pos (mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current)]
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleSection4D
end JanusFormal
