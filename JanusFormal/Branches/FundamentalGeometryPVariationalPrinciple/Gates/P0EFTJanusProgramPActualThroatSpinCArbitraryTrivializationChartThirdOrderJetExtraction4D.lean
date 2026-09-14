import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D

/-!
# Actual throat SpinC third jets in arbitrary trivializations and charts

The existing arbitrary-trivialization/chart second jet of a genuine smooth
primitive SpinC section is extended by its genuine third Frechet derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartThirdOrderJetExtraction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The genuine third jet of a smooth SpinC section in arbitrary valid fiber
and base trivializations. -/
def d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber :=
  fixedTrivializationSpinCMatterThirdOrderJetAt
    (d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state index chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    ((d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state index chartAnchor current hTrivialization
        hChart).of_le (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top))

/-- Forgetting the third derivative recovers the existing SpinC second-jet
extraction definitionally. -/
@[simp]
theorem d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_truncate
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
      choice state index chartAnchor current hTrivialization
        hChart).toFramedSecondOrderJet =
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
        choice state index chartAnchor current hTrivialization hChart :=
  rfl

@[simp]
theorem d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_value
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
      choice state index chartAnchor current hTrivialization hChart).value =
      d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice state index
        current :=
  d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value period
    hPeriod choice state index chartAnchor current hTrivialization hChart

@[simp]
theorem d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_firstDerivative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
      choice state index chartAnchor current hTrivialization
        hChart).firstDerivative =
      fderiv Real
        (d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
          choice state index chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_secondDerivative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
      choice state index chartAnchor current hTrivialization
        hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCSectionTrivializationChartRepresentative period
            hPeriod choice state index chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt_thirdDerivative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
      choice state index chartAnchor current hTrivialization
        hChart).thirdDerivative =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCSectionTrivializationChartRepresentative period
              hPeriod choice state index chartAnchor)))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

/-- Physical SpinC matter third jet in arbitrary valid bundle and base
trivializations. -/
def globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber :=
  d9PrimitiveSpinCSectionThirdOrderJetInTrivializationChartAt period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index
      chartAnchor current hTrivialization hChart

/-- Physical third-jet extraction truncates to the existing physical
second-jet extraction. -/
@[simp]
theorem globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt period
      hPeriod configuration sector index chartAnchor current hTrivialization
        hChart).toFramedSecondOrderJet =
      globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt period
        hPeriod configuration sector index chartAnchor current hTrivialization
          hChart :=
  rfl

/-- At a centered base chart, physical third-jet truncation recovers the
previous centered physical SpinC second jet. -/
@[simp]
theorem globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt_diagonal_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    (globalGaugeFixedSpinCMatterThirdOrderJetInTrivializationChartAt period
      hPeriod configuration sector index current current hTrivialization
        (mem_extChartAt_source current)).toFramedSecondOrderJet =
      globalGaugeFixedSpinCMatterSecondOrderJetsAt period hPeriod configuration
        index current hTrivialization sector :=
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartThirdOrderJetExtraction4D
end JanusFormal
