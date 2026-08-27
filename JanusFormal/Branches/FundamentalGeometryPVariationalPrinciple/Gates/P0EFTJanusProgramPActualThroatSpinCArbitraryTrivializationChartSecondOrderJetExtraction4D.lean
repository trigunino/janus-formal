import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D

/-!
# Actual throat SpinC second jets in arbitrary trivializations and charts

A genuine smooth primitive SpinC section is read in an independently selected
bundle trivialization and extended base chart.  This supplies its second jet at
every point where both choices are valid.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D

set_option autoImplicit false
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
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Local coordinates of a smooth SpinC section in independently selected
fiber and base trivializations. -/
def d9PrimitiveSpinCSectionTrivializationChartRepresentative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor : ThroatBase period hPeriod) :
    ThroatCoverCoordinates → D9DoubledMatterFiber :=
  d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice state index ∘
    (extChartAt throatCoverModelWithCorners chartAnchor).symm

/-- The arbitrary-trivialization/chart representative is `C∞` at every
represented point. -/
theorem d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
        choice state index chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  have hLocal : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (d9PrimitiveSpinCSmoothSectionLocalValue
        period hPeriod choice state index) current :=
    ((d9PrimitiveSpinCSmoothSectionLocalValue_contMDiffOn period hPeriod
      choice state index) current hTrivialization).contMDiffAt
        ((d9PrimitiveSpinCBaseSet_isOpen period hPeriod index).mem_nhds
          hTrivialization)
  have hTarget : extChartAt throatCoverModelWithCorners chartAnchor current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).target :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hInverse : ContMDiffAt
      (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
      (extChartAt throatCoverModelWithCorners chartAnchor).symm
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) chartAnchor).contMDiffAt
        (extChartAt_target_mem_nhds' hTarget)
  have hComposition := hLocal.comp_of_eq hInverse
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)
  exact hComposition.contDiffAt

/-- The genuine second jet of a smooth SpinC section in arbitrary valid
fiber and base trivializations. -/
def d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber :=
  fixedTrivializationSpinCMatterJetAt
    (d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state index chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    ((d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state index chartAnchor current
        hTrivialization hChart).of_le
      (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))

@[simp]
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
      period hPeriod choice state index chartAnchor current
        hTrivialization hChart).value =
      d9PrimitiveSpinCSmoothSectionLocalValue
        period hPeriod choice state index current := by
  change
    d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod choice state index
        ((extChartAt throatCoverModelWithCorners chartAnchor).symm
          (extChartAt throatCoverModelWithCorners chartAnchor current)) = _
  rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]

@[simp]
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
      period hPeriod choice state index chartAnchor current
        hTrivialization hChart).firstDerivative =
      fderiv Real
        (d9PrimitiveSpinCSectionTrivializationChartRepresentative
          period hPeriod choice state index chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
      period hPeriod choice state index chartAnchor current
        hTrivialization hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCSectionTrivializationChartRepresentative
            period hPeriod choice state index chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

/-- The physical SpinC matter jet in arbitrary valid bundle and base
trivializations. -/
def globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber :=
  d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
    period hPeriod .positiveQuarter
      (configuration.physical.spinCMatter sector) index chartAnchor current
        hTrivialization hChart

/-- With the base chart centered at the represented point, the arbitrary
extraction is exactly the previous chartwise SpinC matter jet. -/
@[simp]
theorem globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt_diagonal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hTrivialization :
      current ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt
        period hPeriod configuration sector index current current
          hTrivialization (mem_extChartAt_source current) =
      globalGaugeFixedSpinCMatterSecondOrderJetsAt period hPeriod configuration
        index current hTrivialization sector := by
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
end JanusFormal
