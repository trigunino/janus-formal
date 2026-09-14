import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartThirdOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

/-!
# Smooth local representatives of actual throat SpinC third jets

For a fixed SpinC trivialization/chart index, the existing smooth second-jet
representative and the genuine third derivative assemble into a smooth framed
third jet on the corresponding atlas patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetLocalSectionSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Function Module Set
open scoped Manifold ContDiff Topology
open Bundle
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
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCSecondJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

private abbrev SpinCFirstDerivative :=
  ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber

local instance spinCFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCFirstDerivativeNormedSpace :
    NormedSpace Real SpinCFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance spinCFirstDerivativeFiniteDimensional :
    FiniteDimensional Real SpinCFirstDerivative :=
  ContinuousLinearMap.finiteDimensional

private abbrev SpinCSecondDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCFirstDerivative

local instance spinCSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCSecondDerivativeNormedSpace :
    NormedSpace Real SpinCSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance spinCSecondDerivativeFiniteDimensional :
    FiniteDimensional Real SpinCSecondDerivative :=
  ContinuousLinearMap.finiteDimensional

private abbrev SpinCThirdDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCSecondDerivative

local instance spinCThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCThirdDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCThirdDerivativeNormedSpace :
    NormedSpace Real SpinCThirdDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The third derivative of a fixed-trivialization SpinC representative is
smooth on its atlas patch. -/
theorem d9PrimitiveSpinCLocalThirdDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCThirdDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (fderiv Real
            (fderiv Real
              (d9PrimitiveSpinCSectionTrivializationChartRepresentative
                period hPeriod choice state index.1 index.2)))
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state index.1 index.2 current
        hCurrent.1 hCurrent.2
  have hThirdDerivative :=
    ((hGerm.fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners index.2) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent.2
  exact (hThirdDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-- Totalized SpinC third-jet representative in one fixed atlas patch. -/
def actualThroatSpinCThirdOrderJetLocalRepresentative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod) : SpinCThirdJet := by
  classical
  exact if hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index then
    d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
      choice state index.1 index.2 current hCurrent.1 hCurrent.2
  else 0

/-- On its atlas patch, the totalized representative is the arbitrary
trivialization/chart extraction. -/
theorem actualThroatSpinCThirdOrderJetLocalRepresentative_eq_of_mem
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod choice
        state index current =
      d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
        choice state index.1 index.2 current hCurrent.1 hCurrent.2 := by
  simp only [actualThroatSpinCThirdOrderJetLocalRepresentative,
    dif_pos hCurrent]

/-- The third-jet representative truncates exactly to the existing local
second-jet representative. -/
@[simp]
theorem actualThroatSpinCThirdOrderJetLocalRepresentative_truncate
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod) :
    (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod choice
      state index current).toFramedSecondOrderJet =
      actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod choice
        state index current := by
  classical
  unfold actualThroatSpinCThirdOrderJetLocalRepresentative
    actualThroatSpinCSecondOrderJetLocalRepresentative
  split <;> rfl

private theorem actualThroatSpinCThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCThirdDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
          choice state index current).thirdDerivative)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (d9PrimitiveSpinCLocalThirdDerivative_contMDiffOn period hPeriod
    choice state index).congr
  intro current hCurrent
  unfold actualThroatSpinCThirdOrderJetLocalRepresentative
  split
  · rw [d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_thirdDerivative]
  · contradiction

/-- The value and first three derivatives of a smooth primitive SpinC section
form a smooth raw framed third jet on every fixed atlas patch. -/
theorem actualThroatSpinCThirdOrderJetLocalRepresentative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCThirdJet) ∞
      (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
        choice state index)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  have hLower : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCSecondJet) ∞
      (fun current =>
        (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
          choice state index current).toFramedSecondOrderJet)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
    apply
      (actualThroatSpinCSecondOrderJetLocalRepresentative_contMDiffOn
        period hPeriod choice state index).congr
    intro current _
    exact actualThroatSpinCThirdOrderJetLocalRepresentative_truncate
      period hPeriod choice state index current
  exact contMDiffOn_framedThirdOrderJet_of_truncate_and_thirdDerivative
    (actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
      choice state index) hLower
    (actualThroatSpinCThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
      period hPeriod choice state index)

/-! ## Global gauge-fixed wrapper -/

/-- Local SpinC third-jet representative of one physical sector. -/
def globalGaugeFixedSpinCMatterThirdOrderJetLocalRepresentative
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod) :
    ThroatBase period hPeriod → SpinCThirdJet :=
  actualThroatSpinCThirdOrderJetLocalRepresentative period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index

theorem globalGaugeFixedSpinCMatterThirdOrderJetLocalRepresentative_eq_of_mem
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    globalGaugeFixedSpinCMatterThirdOrderJetLocalRepresentative period hPeriod
        configuration sector index current =
      globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt
        period hPeriod configuration sector index.1 index.2 current
          hCurrent.1 hCurrent.2 :=
  actualThroatSpinCThirdOrderJetLocalRepresentative_eq_of_mem period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index current
      hCurrent

/-- Physical local third jets truncate to the existing physical local second
jets. -/
@[simp]
theorem globalGaugeFixedSpinCMatterThirdOrderJetLocalRepresentative_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod) :
    (globalGaugeFixedSpinCMatterThirdOrderJetLocalRepresentative period hPeriod
      configuration sector index current).toFramedSecondOrderJet =
      globalGaugeFixedSpinCMatterSecondOrderJetLocalRepresentative period hPeriod
        configuration sector index current :=
  actualThroatSpinCThirdOrderJetLocalRepresentative_truncate period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index current

/-- Every gauge-fixed physical SpinC sector has a smooth local third-jet
representative on each atlas patch. -/
theorem globalGaugeFixedSpinCMatterThirdOrderJetLocalRepresentative_contMDiffOn
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCThirdJet) ∞
      (globalGaugeFixedSpinCMatterThirdOrderJetLocalRepresentative period
        hPeriod configuration sector index)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :=
  actualThroatSpinCThirdOrderJetLocalRepresentative_contMDiffOn period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetLocalSectionSmoothness4D
end JanusFormal
