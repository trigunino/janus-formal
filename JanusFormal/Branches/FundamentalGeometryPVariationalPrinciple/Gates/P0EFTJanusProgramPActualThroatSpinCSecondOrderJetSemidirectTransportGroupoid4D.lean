import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D

/-!
# Groupoid laws for SpinC second-jet semidirect transport

The concrete reverse-base/forward-SpinC-fiber transport satisfies identity,
composition and inverse laws on every raw framed second jet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportGroupoid4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 800000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

local instance spinCEndNormedAddCommGroup :
    NormedAddCommGroup SpinCEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCEndNormedSpace : NormedSpace Real SpinCEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCEnd

local instance spinCTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionFirstDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev SpinCTrivializationChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatSpinCSecondOrderJetTrivializationChartAt period hPeriod current

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem fderiv_clm_apply_const_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (field : X → Y →L[Real] Z) (point direction : X) (value : Y)
    (hField : DifferentiableAt Real field point) :
    fderiv Real (fun current ↦ field current value) point direction =
      fderiv Real field point direction value := by
  have hDerivative :=
    fderiv_clm_apply hField (differentiableAt_const (c := value))
  have hApplied := congrArg
    (fun derivative : X →L[Real] Z ↦ derivative direction) hDerivative
  simpa using hApplied

private theorem transition_fderiv_differentiableAt
    (choice : NormalRootChoice)
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod secondIndex)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    DifferentiableAt Real
      (fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex chartAnchor))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  have hSmooth : ((1 : ℕ∞ω) + 1) ≤ (∞ : ℕ∞ω) := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    ((d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
      choice firstIndex secondIndex chartAnchor current hIndices hChart)
      |>.fderiv_right (m := 1) hSmooth).differentiableAt (by norm_num)

private theorem transition_secondDerivative_partial_eq
    (choice : NormalRootChoice)
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod secondIndex)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (first second : ThroatCoverCoordinates) :
    fderiv Real
        (fun coordinate ↦ fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex chartAnchor) coordinate second)
        (extChartAt throatCoverModelWithCorners chartAnchor current) first =
      fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current)
          first second := by
  exact fderiv_clm_apply_const_apply
    (fderiv Real
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex secondIndex chartAnchor))
    (extChartAt throatCoverModelWithCorners chartAnchor current) first second
    (transition_fderiv_differentiableAt period hPeriod choice firstIndex
      secondIndex chartAnchor current hIndices hChart)

private theorem transition_baseChart_eventuallyEq
    (choice : NormalRootChoice)
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex secondIndex firstCenter =ᶠ[
          nhds (extChartAt throatCoverModelWithCorners firstCenter current)]
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  have hFirstTarget :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hInverseContinuous := continuousAt_extChartAt_symm'' hFirstTarget
  have hSecondPreimage :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          (extChartAt throatCoverModelWithCorners secondCenter).source ∈
        nhds (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact extChartAt_source_mem_nhds' hSecond)
  filter_upwards [hSecondPreimage] with coordinate hCoordinate
  simp only [d9PrimitiveSpinCTransitionCenteredChart,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hCoordinate]

private theorem transition_firstDerivative_baseChart
    (choice : NormalRootChoice)
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod secondIndex)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (direction : ThroatCoverCoordinates) :
    fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current) direction =
      fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
          direction) := by
  let inner := throatGaugeBaseChartTransition period hPeriod
    firstCenter secondCenter
  let outer := d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
    firstIndex secondIndex secondCenter
  let point := extChartAt throatCoverModelWithCorners firstCenter current
  have hInner := throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
    firstCenter secondCenter current hFirst hSecond
  have hOuter : ContDiffAt Real 2 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
      choice firstIndex secondIndex secondCenter current hIndices hSecond).of_le
        (by
          show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        firstCenter secondCenter current hFirst
  have hOuterAt : DifferentiableAt Real outer (inner point) := by
    simpa only [hAt] using hOuter.differentiableAt (by norm_num)
  have hChain :
      fderiv Real (outer ∘ inner) point =
        (fderiv Real outer (inner point)).comp
          (fderiv Real inner point) :=
    fderiv_comp point hOuterAt (hInner.differentiableAt (by norm_num))
  have hGerm := transition_baseChart_eventuallyEq period hPeriod choice
    firstIndex secondIndex firstCenter secondCenter current hFirst hSecond
  have hEq := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] SpinCEnd ↦
      derivative direction) hGerm.fderiv_eq
  rw [hChain] at hEq
  simpa only [inner, outer, point, hAt,
    ContinuousLinearMap.comp_apply] using hEq

private theorem transition_secondDerivative_baseChart
    (choice : NormalRootChoice)
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod secondIndex)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex firstCenter))
        (extChartAt throatCoverModelWithCorners firstCenter current)
          first second =
      fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex secondIndex secondCenter))
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) second) +
        fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first second) := by
  let inner := throatGaugeBaseChartTransition period hPeriod
    firstCenter secondCenter
  let outer := d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
    firstIndex secondIndex secondCenter
  let point := extChartAt throatCoverModelWithCorners firstCenter current
  have hInner := throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
    firstCenter secondCenter current hFirst hSecond
  have hOuter : ContDiffAt Real 2 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
      choice firstIndex secondIndex secondCenter current hIndices hSecond).of_le
        (by
          show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        firstCenter secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 2 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod choice
    firstIndex secondIndex firstCenter secondCenter current hFirst hSecond
  have hSecondEq := (hGerm.fderiv (𝕜 := Real)).fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] SpinCEnd ↦ derivative first second)
    hSecondEq
  rw [second_fderiv_comp_apply
    (E := ThroatCoverCoordinates) (F := ThroatCoverCoordinates)
    (G := SpinCEnd) inner outer point hInner hOuterAt, hAt] at hApplied
  simpa only [inner, outer, point] using hApplied

private theorem change_baseFirst_comp
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).baseFirst direction =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source middle).baseFirst
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).baseFirst direction) := by
  have hCocycle :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
      period hPeriod target.chartAnchor middle.chartAnchor
        source.chartAnchor current target.chart_mem middle.chart_mem
          source.chart_mem
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates ↦ derivative direction) hCocycle
  simpa only [throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    ContinuousLinearMap.comp_apply] using hApplied

private theorem change_baseSecond_comp
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).baseSecond first second =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseSecond
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first)
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) +
        (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseSecond first second) := by
  simpa only [throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseSecond,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
      period hPeriod target.chartAnchor middle.chartAnchor
        source.chartAnchor current target.chart_mem middle.chart_mem
          source.chart_mem first second

private theorem change_fiberValue_comp
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (value : D9DoubledMatterFiber) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberValue value =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value) := by
  have hCocycle := d9PrimitiveSpinCCoordChange_comp period hPeriod choice
    source.trivializationIndex middle.trivializationIndex
      target.trivializationIndex current
      ⟨⟨source.trivialization_mem, middle.trivialization_mem⟩,
        target.trivialization_mem⟩
  have hApplied := congrArg (fun transition : SpinCEnd ↦ transition value)
    hCocycle
  simpa only [throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    ContinuousLinearMap.comp_apply] using hApplied.symm

private theorem change_fiberFirst_comp
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) (value : D9DoubledMatterFiber) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberFirst direction value =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst direction) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst direction
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value) := by
  have hReparam := transition_firstDerivative_baseChart period hPeriod choice
    source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current
      ⟨source.trivialization_mem, middle.trivialization_mem⟩
        target.chart_mem middle.chart_mem direction
  have hBaseSelf :
      fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative]
      using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod target.chartAnchor current target.chart_mem
  have hCocycle :=
    throatSpinCTrivializationBaseChartTransition_firstDerivative_cocycle
      period hPeriod choice source.trivializationIndex
        middle.trivializationIndex target.trivializationIndex
        target.chartAnchor target.chartAnchor current
        ⟨source.trivialization_mem, middle.trivialization_mem,
          target.trivialization_mem⟩
        target.chart_mem target.chart_mem direction
  have hApplied := congrArg (fun derivative : SpinCEnd ↦ derivative value)
    hCocycle
  rw [hReparam, hBaseSelf, ContinuousLinearMap.id_apply] at hApplied
  simpa only [throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst,
    d9PrimitiveSpinCTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
      target.chart_mem,
    (extChartAt throatCoverModelWithCorners middle.chartAnchor).left_inv
      middle.chart_mem,
    add_apply, ContinuousLinearMap.comp_apply] using hApplied

private theorem change_fiberSecond_comp
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) (value : D9DoubledMatterFiber) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberSecond first second value =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberSecond
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first)
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseSecond first second) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst first
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst second
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberSecond first second
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value) := by
  have hReparamFirst := transition_firstDerivative_baseChart period hPeriod
    choice source.trivializationIndex middle.trivializationIndex
      target.chartAnchor middle.chartAnchor current
      ⟨source.trivialization_mem, middle.trivialization_mem⟩
        target.chart_mem middle.chart_mem first
  have hReparamSecondDirection := transition_firstDerivative_baseChart
    period hPeriod choice source.trivializationIndex
      middle.trivializationIndex target.chartAnchor middle.chartAnchor current
      ⟨source.trivialization_mem, middle.trivialization_mem⟩
        target.chart_mem middle.chart_mem second
  have hReparamSecond := transition_secondDerivative_baseChart period hPeriod
    choice source.trivializationIndex middle.trivializationIndex
      target.chartAnchor middle.chartAnchor current
      ⟨source.trivialization_mem, middle.trivialization_mem⟩
        target.chart_mem middle.chart_mem first second
  have hBaseSelf :
      fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative]
      using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod target.chartAnchor current target.chart_mem
  have hBaseFieldDifferentiable : DifferentiableAt Real
      (fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor target.chartAnchor))
      (extChartAt throatCoverModelWithCorners target.chartAnchor current) := by
    exact ((throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      target.chartAnchor target.chartAnchor current target.chart_mem
        target.chart_mem).fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)
  have hBasePartialEq := fderiv_clm_apply_const_apply
    (fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        target.chartAnchor target.chartAnchor))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
      first second hBaseFieldDifferentiable
  have hBaseIteratedZero :
      fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor target.chartAnchor))
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first second = 0 := by
    have hSelf :=
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod target.chartAnchor current target.chart_mem
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates ↦
        derivative first second) hSelf
    simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative,
      zero_apply] using hApplied
  have hBasePartialZero :
      fderiv Real
          (fun coordinate ↦ fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor target.chartAnchor) coordinate second)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first = 0 := by
    rw [hBasePartialEq, hBaseIteratedZero]
  have hDirectPartial := transition_secondDerivative_partial_eq period hPeriod
    choice source.trivializationIndex target.trivializationIndex
      target.chartAnchor current
      ⟨source.trivialization_mem, target.trivialization_mem⟩
        target.chart_mem first second
  have hSourceMiddlePartial := transition_secondDerivative_partial_eq
    period hPeriod choice source.trivializationIndex
      middle.trivializationIndex target.chartAnchor current
      ⟨source.trivialization_mem, middle.trivialization_mem⟩
        target.chart_mem first second
  have hMiddleTargetPartial := transition_secondDerivative_partial_eq
    period hPeriod choice middle.trivializationIndex
      target.trivializationIndex target.chartAnchor current
      ⟨middle.trivialization_mem, target.trivialization_mem⟩
        target.chart_mem first second
  have hCocycle :=
    throatSpinCTrivializationBaseChartTransition_secondDerivative_cocycle_apply
      period hPeriod choice source.trivializationIndex
        middle.trivializationIndex target.trivializationIndex
        target.chartAnchor target.chartAnchor current
        ⟨source.trivialization_mem, middle.trivialization_mem,
          target.trivialization_mem⟩
        target.chart_mem target.chart_mem first second value
  rw [hBaseSelf] at hCocycle
  simp only [ContinuousLinearMap.id_apply] at hCocycle
  rw [hBasePartialZero] at hCocycle
  simp only [map_zero, zero_apply, add_zero] at hCocycle
  rw [hDirectPartial, hSourceMiddlePartial, hMiddleTargetPartial,
    hReparamFirst, hReparamSecondDirection, hReparamSecond] at hCocycle
  simpa only [throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseSecond,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberSecond,
    throatSpinCTargetTrivializationTransitionSecondDerivativeAt,
    d9PrimitiveSpinCTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
      target.chart_mem,
    (extChartAt throatCoverModelWithCorners middle.chartAnchor).left_inv
      middle.chart_mem,
    add_apply, map_add, ContinuousLinearMap.comp_apply, add_zero] using hCocycle

private theorem transition_self_eventuallyEq
    (choice : NormalRootChoice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hIndex : current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        index index chartAnchor =ᶠ[
          nhds (extChartAt throatCoverModelWithCorners chartAnchor current)]
      fun _ ↦ ContinuousLinearMap.id Real D9DoubledMatterFiber := by
  have hBaseNhds : d9PrimitiveSpinCBaseSet period hPeriod index ∈
      nhds current :=
    (d9PrimitiveSpinCBaseSet_isOpen period hPeriod index).mem_nhds hIndex
  have hTarget :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hInverseContinuous := continuousAt_extChartAt_symm'' hTarget
  have hPreimage :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm ⁻¹'
          d9PrimitiveSpinCBaseSet period hPeriod index ∈
        nhds (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]
      exact hBaseNhds)
  filter_upwards [hPreimage] with coordinate hCoordinate
  exact d9PrimitiveSpinCCoordChange_self period hPeriod choice index
    ((extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate)
      hCoordinate

private theorem transition_self_firstDerivative
    (choice : NormalRootChoice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hIndex : current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          index index chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) = 0 := by
  have hGerm := transition_self_eventuallyEq period hPeriod choice index
    chartAnchor current hIndex hChart
  simpa only [fderiv_const_apply] using hGerm.fderiv_eq

private theorem transition_self_secondDerivative
    (choice : NormalRootChoice)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hIndex : current ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            index index chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) = 0 := by
  have hGerm := transition_self_eventuallyEq period hPeriod choice index
    chartAnchor current hIndex hChart
  have hConstFirst :
      fderiv Real
          (fun _ : ThroatCoverCoordinates ↦
            ContinuousLinearMap.id Real D9DoubledMatterFiber) =
        (0 : ThroatCoverCoordinates →
          ThroatCoverCoordinates →L[Real] SpinCEnd) :=
    fderiv_const _
  have hEq := (hGerm.fderiv (𝕜 := Real)).fderiv_eq (𝕜 := Real)
  rw [hConstFirst] at hEq
  have hZeroSecond :
      fderiv Real
          (0 : ThroatCoverCoordinates →
            ThroatCoverCoordinates →L[Real] SpinCEnd) =
        (0 : ThroatCoverCoordinates →
          ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real] SpinCEnd) :=
    fderiv_zero
  rw [hZeroSecond] at hEq
  simpa only [Pi.zero_apply] using hEq

/-! ## Identity -/

/-- Transport from a SpinC trivialization/chart pair to itself fixes every
raw jet. -/
@[simp]
theorem throatSpinCSecondOrderJetSemidirectTransportAt_self_apply
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCJet) :
    throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
      presentation presentation jet = jet := by
  let change := throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod
    choice presentation presentation
  have hBaseFirst : change.baseFirst =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [change,
      throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod presentation.chartAnchor current presentation.chart_mem
  have hBaseSecond : change.baseSecond = 0 := by
    simpa only [change,
      throatSpinCSecondOrderJetSemidirectChangeAt_baseSecond,
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod presentation.chartAnchor current presentation.chart_mem
  have hFiberValue : change.fiberValue =
      ContinuousLinearMap.id Real D9DoubledMatterFiber := by
    simpa only [change,
      throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue] using
      d9PrimitiveSpinCCoordChange_self period hPeriod choice
        presentation.trivializationIndex current presentation.trivialization_mem
  have hFiberFirst : change.fiberFirst = 0 := by
    simpa only [change,
      throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst] using
      transition_self_firstDerivative period hPeriod choice
        presentation.trivializationIndex presentation.chartAnchor current
          presentation.trivialization_mem presentation.chart_mem
  have hFiberSecond : change.fiberSecond = 0 := by
    simpa only [change,
      throatSpinCSecondOrderJetSemidirectChangeAt_fiberSecond,
      throatSpinCTargetTrivializationTransitionSecondDerivativeAt] using
      transition_self_secondDerivative period hPeriod choice
        presentation.trivializationIndex presentation.chartAnchor current
          presentation.trivialization_mem presentation.chart_mem
  change change.toContinuousLinearMap jet = jet
  exact framedSecondOrderJetSemidirectTransport_self_of_coefficients change
    (fun direction ↦ by rw [hBaseFirst]; rfl)
    (fun first second ↦ by rw [hBaseSecond]; rfl)
    (fun value ↦ by rw [hFiberValue]; rfl)
    (fun direction value ↦ by rw [hFiberFirst]; rfl)
    (fun first second value ↦ by rw [hFiberSecond]; rfl) jet

/-- Self-transport is the identity continuous linear map. -/
@[simp]
theorem throatSpinCSecondOrderJetSemidirectTransportAt_self
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current) :
    throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        presentation presentation =
      ContinuousLinearMap.id Real SpinCJet := by
  apply ContinuousLinearMap.ext
  intro jet
  exact throatSpinCSecondOrderJetSemidirectTransportAt_self_apply
    period hPeriod choice presentation jet

/-! ## Composition and inverses -/

/-- Transport through an intermediate SpinC trivialization/chart pair equals
direct transport on every raw jet. -/
theorem throatSpinCSecondOrderJetSemidirectTransportAt_comp_apply
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCJet) :
    throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        source target jet =
      throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        middle target
        (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
          source middle jet) := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).toContinuousLinearMap jet =
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      middle target).toContinuousLinearMap
      ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source middle).toContinuousLinearMap jet)
  exact framedSecondOrderJetSemidirectTransport_comp_of_coefficients
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source middle)
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      middle target)
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target)
    (change_baseFirst_comp period hPeriod choice source middle target)
    (change_baseSecond_comp period hPeriod choice source middle target)
    (change_fiberValue_comp period hPeriod choice source middle target)
    (change_fiberFirst_comp period hPeriod choice source middle target)
    (change_fiberSecond_comp period hPeriod choice source middle target) jet

/-- SpinC semidirect transport composes exactly through any intermediate
trivialization/chart pair. -/
theorem throatSpinCSecondOrderJetSemidirectTransportAt_comp
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current) :
    throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        source target =
      (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        middle target).comp
        (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
          source middle) := by
  apply ContinuousLinearMap.ext
  intro jet
  exact throatSpinCSecondOrderJetSemidirectTransportAt_comp_apply
    period hPeriod choice source middle target jet

/-- Reverse SpinC transport is a left inverse. -/
theorem throatSpinCSecondOrderJetSemidirectTransportAt_inverse_comp
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        target source).comp
        (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
          source target) =
      ContinuousLinearMap.id Real SpinCJet := by
  rw [← throatSpinCSecondOrderJetSemidirectTransportAt_comp
    period hPeriod choice source target source]
  exact throatSpinCSecondOrderJetSemidirectTransportAt_self
    period hPeriod choice source

/-- Reverse SpinC transport is a right inverse. -/
theorem throatSpinCSecondOrderJetSemidirectTransportAt_comp_inverse
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        source target).comp
        (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
          target source) =
      ContinuousLinearMap.id Real SpinCJet := by
  exact throatSpinCSecondOrderJetSemidirectTransportAt_inverse_comp
    period hPeriod choice target source

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportGroupoid4D
end JanusFormal
