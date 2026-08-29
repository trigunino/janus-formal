import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

/-!
# Second-order same-chart SpinC trivialization overlap

The SpinC fiber transition and both local representatives are read in one
fixed arbitrary throat chart.  Their exact germ yields the value, first-order,
and full four-term second-order Leibniz laws.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance primitiveSpinCCoreIsContMDiff (choice : NormalRootChoice) :
    (d9PrimitiveSpinCVectorBundleCore
      period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ :=
  d9PrimitiveSpinCVectorBundleCore_isContMDiff period hPeriod choice

/-! ## Centered transition and exact local germ -/

/-- The varying SpinC fiber transition read in one fixed arbitrary extended
throat chart. -/
def d9PrimitiveSpinCTransitionCenteredChart
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor : ThroatBase period hPeriod) :
    ThroatCoverCoordinates → SpinCEnd :=
  fun coordinate =>
    d9PrimitiveSpinCCoordChange period hPeriod choice first second
      ((extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate)

/-- The centered SpinC transition is `C∞` at every point where both
trivializations and the selected base chart are valid. -/
theorem d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
    (choice : NormalRootChoice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        first second chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  let coordinate := extChartAt throatCoverModelWithCorners chartAnchor current
  have hTarget : coordinate ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).target :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hInverse :
      ContMDiffAt (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) chartAnchor).contMDiffAt
        (extChartAt_target_mem_nhds' hTarget)
  have hTransitionOn :
      ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCEnd) ∞
        (d9PrimitiveSpinCCoordChange period hPeriod choice first second)
        (d9PrimitiveSpinCBaseSet period hPeriod first ∩
          d9PrimitiveSpinCBaseSet period hPeriod second) :=
    ((d9PrimitiveSpinCVectorBundleCore period hPeriod choice)
      |>.contMDiffOn_coordChange throatCoverModelWithCorners first second)
  have hTransition := hTransitionOn.contMDiffAt
    (((d9PrimitiveSpinCBaseSet_isOpen period hPeriod first).inter
      (d9PrimitiveSpinCBaseSet_isOpen period hPeriod second)).mem_nhds hCurrent)
  have hComposition := hTransition.comp_of_eq hInverse
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)
  change ContDiffAt Real ∞
    ((d9PrimitiveSpinCCoordChange period hPeriod choice first second) ∘
      (extChartAt throatCoverModelWithCorners chartAnchor).symm) coordinate
  exact hComposition.contDiffAt

/-- On a common trivialization overlap, the centered transition applied to
the first local representative is exactly the second local representative as
a germ in the common base chart. -/
theorem d9PrimitiveSpinCSectionTrivializationChartRepresentative_transition_eventuallyEq
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (fun coordinate =>
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          first second chartAnchor coordinate
        (d9PrimitiveSpinCSectionTrivializationChartRepresentative period
          hPeriod choice state first chartAnchor coordinate)) =ᶠ[𝓝
            (extChartAt throatCoverModelWithCorners chartAnchor current)]
      d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
        choice state second chartAnchor := by
  have hOverlapOpen : IsOpen
      (d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second) :=
    (d9PrimitiveSpinCBaseSet_isOpen period hPeriod first).inter
      (d9PrimitiveSpinCBaseSet_isOpen period hPeriod second)
  have hOverlapNhds :
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second ∈ 𝓝 current :=
    hOverlapOpen.mem_nhds hCurrent
  have hChartInverse : ContinuousAt
      (extChartAt throatCoverModelWithCorners chartAnchor).symm
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    continuousAt_extChartAt_symm' hChart
  have hInverseEventually :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm ⁻¹'
          (d9PrimitiveSpinCBaseSet period hPeriod first ∩
            d9PrimitiveSpinCBaseSet period hPeriod second) ∈
        𝓝 (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    hChartInverse.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]
      exact hOverlapNhds)
  filter_upwards [hInverseEventually] with coordinate hCoordinate
  simpa only [d9PrimitiveSpinCTransitionCenteredChart,
    d9PrimitiveSpinCSectionTrivializationChartRepresentative,
    Function.comp_apply] using
    d9PrimitiveSpinCSmoothSectionLocalValue_coordChange period hPeriod choice
      state first second
      ((extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate)
      hCoordinate

/-! ## Exact value and differentiated transition laws -/

/-- Zero-order component of the same-chart SpinC jet transition law. -/
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value_transition
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
      hPeriod choice state second chartAnchor current hCurrent.2 hChart).value =
      d9PrimitiveSpinCCoordChange period hPeriod choice first second current
        (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state first chartAnchor current hCurrent.1 hChart).value := by
  rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value]
  exact (d9PrimitiveSpinCSmoothSectionLocalValue_coordChange period hPeriod
    choice state first second current hCurrent).symm

/-- First-order varying-trivialization Leibniz law for a SpinC section in one
arbitrary fixed base chart. -/
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative_transition
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
      hPeriod choice state second chartAnchor current hCurrent.2 hChart).firstDerivative =
      (d9PrimitiveSpinCCoordChange period hPeriod choice first second current).comp
        (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state first chartAnchor current hCurrent.1 hChart).firstDerivative +
      (fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          first second chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current)).flip
          (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
            hPeriod choice state first chartAnchor current hCurrent.1 hChart).value := by
  let transition := d9PrimitiveSpinCTransitionCenteredChart period hPeriod
    choice first second chartAnchor
  let firstRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state first chartAnchor
  let secondRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state second chartAnchor
  let coordinate := extChartAt throatCoverModelWithCorners chartAnchor current
  have hTransition : ContDiffAt Real 2 transition coordinate :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
      choice first second chartAnchor current hCurrent hChart).of_le (by
        show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hFirst : ContDiffAt Real 2 firstRepresentative coordinate :=
    (d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state first chartAnchor current hCurrent.1 hChart).of_le
        (by
          show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hGerm :
      (fun point => transition point (firstRepresentative point)) =ᶠ[𝓝 coordinate]
        secondRepresentative := by
    simpa only [transition, firstRepresentative, secondRepresentative,
      coordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_transition_eventuallyEq
        period hPeriod choice state first second chartAnchor current hCurrent hChart
  have hProduct := fderiv_clm_apply
    (hTransition.differentiableAt (by norm_num))
    (hFirst.differentiableAt (by norm_num))
  have hCoordinateInverse :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate =
        current := by
    simpa only [coordinate] using
      (extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart
  simp only [transition, firstRepresentative,
    d9PrimitiveSpinCTransitionCenteredChart,
    d9PrimitiveSpinCSectionTrivializationChartRepresentative,
    Function.comp_apply] at hProduct
  rw [hCoordinateInverse] at hProduct
  rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value]
  rw [show fderiv Real secondRepresentative coordinate =
      fderiv Real (fun point => transition point (firstRepresentative point))
        coordinate by exact hGerm.fderiv_eq.symm]
  simpa only [transition, firstRepresentative, coordinate,
    d9PrimitiveSpinCTransitionCenteredChart,
    d9PrimitiveSpinCSectionTrivializationChartRepresentative,
    Function.comp_apply] using hProduct

/-- Full four-term second-order varying-trivialization law for a SpinC
section in one arbitrary fixed base chart. -/
theorem d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative_transition_apply
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (first second : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod first ∩
        d9PrimitiveSpinCBaseSet period hPeriod second)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (firstDirection secondDirection : ThroatCoverCoordinates) :
    (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
      hPeriod choice state second chartAnchor current hCurrent.2 hChart).secondDerivative
        firstDirection secondDirection =
      d9PrimitiveSpinCCoordChange period hPeriod choice first second current
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state first chartAnchor current hCurrent.1 hChart).secondDerivative
            firstDirection secondDirection) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            first second chartAnchor)
          (extChartAt throatCoverModelWithCorners chartAnchor current)
          firstDirection
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state first chartAnchor current hCurrent.1 hChart).firstDerivative
            secondDirection) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            first second chartAnchor)
          (extChartAt throatCoverModelWithCorners chartAnchor current)
          secondDirection
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state first chartAnchor current hCurrent.1 hChart).firstDerivative
            firstDirection) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
                first second chartAnchor) coordinate secondDirection)
          (extChartAt throatCoverModelWithCorners chartAnchor current)
          firstDirection
        ((d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period
          hPeriod choice state first chartAnchor current hCurrent.1 hChart).value) := by
  let transition := d9PrimitiveSpinCTransitionCenteredChart period hPeriod
    choice first second chartAnchor
  let firstRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state first chartAnchor
  let secondRepresentative :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative period hPeriod
      choice state second chartAnchor
  let coordinate := extChartAt throatCoverModelWithCorners chartAnchor current
  have hTransition : ContDiffAt Real 2 transition coordinate :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
      choice first second chartAnchor current hCurrent hChart).of_le (by
        show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hFirst : ContDiffAt Real 2 firstRepresentative coordinate :=
    (d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state first chartAnchor current hCurrent.1 hChart).of_le
        (by
          show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hGerm :
      (fun point => transition point (firstRepresentative point)) =ᶠ[𝓝 coordinate]
        secondRepresentative := by
    simpa only [transition, firstRepresentative, secondRepresentative,
      coordinate] using
      d9PrimitiveSpinCSectionTrivializationChartRepresentative_transition_eventuallyEq
        period hPeriod choice state first second chartAnchor current hCurrent hChart
  have hSecondDerivative :
      fderiv Real (fderiv Real
          (fun point => transition point (firstRepresentative point))) coordinate =
        fderiv Real (fderiv Real secondRepresentative) coordinate :=
    (hGerm.fderiv).fderiv_eq
  have hLeibniz := second_fderiv_clm_apply_apply transition
    firstRepresentative coordinate firstDirection secondDirection hTransition hFirst
  have hCoordinateInverse :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate =
        current := by
    simpa only [coordinate] using
      (extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart
  simp only [transition, firstRepresentative,
    d9PrimitiveSpinCTransitionCenteredChart,
    d9PrimitiveSpinCSectionTrivializationChartRepresentative,
    Function.comp_apply] at hLeibniz
  rw [hCoordinateInverse] at hLeibniz
  rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative,
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value]
  rw [show fderiv Real (fderiv Real secondRepresentative) coordinate
      firstDirection secondDirection =
    fderiv Real (fderiv Real
      (fun point => transition point (firstRepresentative point))) coordinate
        firstDirection secondDirection by
    exact congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber =>
        derivative firstDirection secondDirection) hSecondDerivative.symm]
  simpa only [transition, firstRepresentative, coordinate,
    d9PrimitiveSpinCTransitionCenteredChart,
    d9PrimitiveSpinCSectionTrivializationChartRepresentative,
    Function.comp_apply] using hLeibniz

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
end JanusFormal
