import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricCombinedFrameBaseChartSecondOrderGroupoid4D

/-!
# Groupoid laws for metric second-jet semidirect transport

The concrete reverse-base/forward-frame transport satisfies identity,
composition and inverse laws on every raw framed metric second jet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportGroupoid4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 800000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatMetricCombinedFrameBaseChartSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

attribute [local instance]
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedAddCommGroup
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedSpace

private abbrev TensorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] TensorEnd

local instance tensorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev MetricJet :=
  FramedSecondOrderJet ThroatCoverCoordinates ThroatCovariantTwoTensorModel

private abbrev MetricFrameChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatMetricSecondOrderJetFrameChartAt period hPeriod current

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem semidirect_transport_comp_of_coefficients
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]
    [FiniteDimensional Real X] [FiniteDimensional Real V]
    (firstMiddle middleLast firstLast :
      FramedSecondOrderJetSemidirectChange X V)
    (hBaseFirst : ∀ direction,
      firstLast.baseFirst direction =
        firstMiddle.baseFirst (middleLast.baseFirst direction))
    (hBaseSecond : ∀ first second,
      firstLast.baseSecond first second =
        firstMiddle.baseSecond
            (middleLast.baseFirst first) (middleLast.baseFirst second) +
          firstMiddle.baseFirst (middleLast.baseSecond first second))
    (hFiberValue : ∀ value,
      firstLast.fiberValue value =
        middleLast.fiberValue (firstMiddle.fiberValue value))
    (hFiberFirst : ∀ direction value,
      firstLast.fiberFirst direction value =
        middleLast.fiberValue
            (firstMiddle.fiberFirst (middleLast.baseFirst direction) value) +
          middleLast.fiberFirst direction (firstMiddle.fiberValue value))
    (hFiberSecond : ∀ first second value,
      firstLast.fiberSecond first second value =
        middleLast.fiberValue
            (firstMiddle.fiberSecond
              (middleLast.baseFirst first) (middleLast.baseFirst second) value) +
          middleLast.fiberValue
            (firstMiddle.fiberFirst
              (middleLast.baseSecond first second) value) +
          middleLast.fiberFirst first
            (firstMiddle.fiberFirst (middleLast.baseFirst second) value) +
          middleLast.fiberFirst second
            (firstMiddle.fiberFirst (middleLast.baseFirst first) value) +
          middleLast.fiberSecond first second
            (firstMiddle.fiberValue value))
    (jet : FramedSecondOrderJet X V) :
    firstLast.toContinuousLinearMap jet =
      middleLast.toContinuousLinearMap
        (firstMiddle.toContinuousLinearMap jet) := by
  apply FramedSecondOrderJet.ext_components
  · simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_value, hFiberValue]
  · ext direction
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_firstDerivative_apply,
      hBaseFirst, hFiberValue, hFiberFirst, map_add]
    abel
  · ext first second
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_secondDerivative_apply,
      hBaseFirst, hBaseSecond, hFiberValue, hFiberFirst, hFiberSecond,
      map_add]
    simp only [FramedSecondOrderJetSemidirectChange.transport_firstDerivative_apply,
      FramedSecondOrderJetSemidirectChange.transport_value, map_add]
    abel

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
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hFrames : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    DifferentiableAt Real
      (fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor chartAnchor))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  have hSmooth : ((1 : ℕ∞ω) + 1) ≤ (∞ : ℕ∞ω) := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact
    ((throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor chartAnchor current hFrames
        hChart).fderiv_right (m := 1) hSmooth).differentiableAt (by norm_num)

private theorem transition_secondDerivative_partial_eq
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hFrames : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (first second : ThroatCoverCoordinates) :
    fderiv Real
        (fun coordinate ↦ fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor) coordinate second)
        (extChartAt throatCoverModelWithCorners chartAnchor current) first =
      fderiv Real
        (fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current)
          first second := by
  exact fderiv_clm_apply_const_apply
    (fderiv Real
      (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor chartAnchor))
    (extChartAt throatCoverModelWithCorners chartAnchor current) first second
    (transition_fderiv_differentiableAt period hPeriod firstAnchor
      secondAnchor chartAnchor current hFrames hChart)

/-- The same frame transition in two base charts is related by the genuine
base-chart transition germ. -/
private theorem transition_baseChart_eventuallyEq
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor firstCenter =ᶠ[
          𝓝 (extChartAt throatCoverModelWithCorners firstCenter current)]
      (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  have hFirstTarget :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hInverseContinuous :=
    continuousAt_extChartAt_symm'' hFirstTarget
  have hSecondPreimage :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          (extChartAt throatCoverModelWithCorners secondCenter).source ∈
        𝓝 (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact extChartAt_source_mem_nhds' hSecond)
  filter_upwards [hSecondPreimage] with coordinate hCoordinate
  simp only [throatCovariantTwoTensorTransitionCenteredChart,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hCoordinate]

private theorem transition_firstDerivative_baseChart
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFrames : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (direction : ThroatCoverCoordinates) :
    fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current) direction =
      fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
          direction) := by
  let inner := throatGaugeBaseChartTransition period hPeriod
    firstCenter secondCenter
  let outer := throatCovariantTwoTensorTransitionCenteredChart period hPeriod
    firstAnchor secondAnchor secondCenter
  let point := extChartAt throatCoverModelWithCorners firstCenter current
  have hInner := throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
    firstCenter secondCenter current hFirst hSecond
  have hOuter : ContDiffAt Real 2 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor secondCenter current hFrames
        hSecond).of_le (by
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
  have hGerm := transition_baseChart_eventuallyEq period hPeriod firstAnchor
    secondAnchor firstCenter secondCenter current hFirst hSecond
  have hEq := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] TensorEnd ↦
      derivative direction) hGerm.fderiv_eq
  rw [hChain] at hEq
  simpa only [inner, outer, point, hAt,
    ContinuousLinearMap.comp_apply] using hEq

private theorem transition_secondDerivative_baseChart
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFrames : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    fderiv Real
        (fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter))
        (extChartAt throatCoverModelWithCorners firstCenter current)
          first second =
      fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor secondCenter))
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
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first second) := by
  let inner := throatGaugeBaseChartTransition period hPeriod
    firstCenter secondCenter
  let outer := throatCovariantTwoTensorTransitionCenteredChart period hPeriod
    firstAnchor secondAnchor secondCenter
  let point := extChartAt throatCoverModelWithCorners firstCenter current
  have hInner := throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
    firstCenter secondCenter current hFirst hSecond
  have hOuter : ContDiffAt Real 2 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor secondCenter current hFrames
        hSecond).of_le (by
          show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        firstCenter secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 2 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod firstAnchor
    secondAnchor firstCenter secondCenter current hFirst hSecond
  have hSecondEq := (hGerm.fderiv (𝕜 := Real)).fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] TensorEnd ↦ derivative first second)
    hSecondEq
  rw [second_fderiv_comp_apply
    (E := ThroatCoverCoordinates) (F := ThroatCoverCoordinates)
    (G := TensorEnd) inner outer point hInner hOuterAt, hAt] at hApplied
  simpa only [inner, outer, point] using hApplied

private theorem change_baseFirst_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source target).baseFirst direction =
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source middle).baseFirst
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).baseFirst direction) := by
  have hCocycle :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
      period hPeriod target.chartAnchor middle.chartAnchor
        source.chartAnchor current target.chart_mem middle.chart_mem
          source.chart_mem
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates ↦ derivative direction) hCocycle
  simpa only [throatMetricSecondOrderJetSemidirectChangeAt_baseFirst,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    ContinuousLinearMap.comp_apply] using hApplied

private theorem change_baseSecond_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source target).baseSecond first second =
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          source middle).baseSecond
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first)
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second) +
        (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          source middle).baseFirst
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseSecond first second) := by
  simpa only [throatMetricSecondOrderJetSemidirectChangeAt_baseFirst,
    throatMetricSecondOrderJetSemidirectChangeAt_baseSecond,
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
      period hPeriod target.chartAnchor middle.chartAnchor
        source.chartAnchor current target.chart_mem middle.chart_mem
          source.chart_mem first second

private theorem change_fiberValue_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (value : TensorModel) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source target).fiberValue value =
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        middle target).fiberValue
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          source middle).fiberValue value) := by
  have hCocycle :=
    P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.throatCovariantTwoTensorTrivializationTransitionAt_cocycle
      period hPeriod source.frameAnchor middle.frameAnchor target.frameAnchor
        current ⟨source.frame_mem, middle.frame_mem, target.frame_mem⟩
  have hApplied := congrArg (fun transition ↦ transition value) hCocycle
  change throatCovariantTwoTensorFrameTransitionAt period hPeriod
      source.frameAnchor target.frameAnchor current value =
    throatCovariantTwoTensorFrameTransitionAt period hPeriod
      middle.frameAnchor target.frameAnchor current
        (throatCovariantTwoTensorFrameTransitionAt period hPeriod
          source.frameAnchor middle.frameAnchor current value)
  rw [throatCovariantTwoTensorFrameTransitionAt_eq_zeroOrder_apply,
    throatCovariantTwoTensorFrameTransitionAt_eq_zeroOrder_apply,
    throatCovariantTwoTensorFrameTransitionAt_eq_zeroOrder_apply]
  exact hApplied.symm

private theorem change_fiberFirst_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) (value : TensorModel) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source target).fiberFirst direction value =
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberValue
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst direction) value) +
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberFirst direction
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          source middle).fiberValue value) := by
  have hReparam := transition_firstDerivative_baseChart period hPeriod
    source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
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
    throatMetricFrameBaseChartTransition_firstDerivative_cocycle period hPeriod
      source.frameAnchor middle.frameAnchor target.frameAnchor
        target.chartAnchor target.chartAnchor current
        ⟨source.frame_mem, middle.frame_mem, target.frame_mem⟩
        target.chart_mem target.chart_mem direction
  have hApplied := congrArg (fun derivative : TensorEnd ↦ derivative value)
    hCocycle
  rw [hReparam, hBaseSelf, ContinuousLinearMap.id_apply] at hApplied
  simpa only [throatMetricSecondOrderJetSemidirectChangeAt_baseFirst,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberValue,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberFirst,
    throatCovariantTwoTensorTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
      target.chart_mem,
    (extChartAt throatCoverModelWithCorners middle.chartAnchor).left_inv
      middle.chart_mem,
    add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe] using
      hApplied

private theorem change_fiberSecond_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) (value : TensorModel) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source target).fiberSecond first second value =
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberValue
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberSecond
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first)
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second) value) +
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberValue
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseSecond first second) value) +
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberFirst first
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second) value) +
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberFirst second
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first) value) +
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberSecond first second
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          source middle).fiberValue value) := by
  have hReparamFirst := transition_firstDerivative_baseChart period hPeriod
    source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
        target.chart_mem middle.chart_mem first
  have hReparamSecondDirection :=
    transition_firstDerivative_baseChart period hPeriod source.frameAnchor
      middle.frameAnchor target.chartAnchor middle.chartAnchor current
      ⟨source.frame_mem, middle.frame_mem⟩ target.chart_mem middle.chart_mem
        second
  have hReparamSecond := transition_secondDerivative_baseChart period hPeriod
    source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
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
    source.frameAnchor target.frameAnchor target.chartAnchor current
      ⟨source.frame_mem, target.frame_mem⟩ target.chart_mem first second
  have hSourceMiddlePartial := transition_secondDerivative_partial_eq
    period hPeriod source.frameAnchor middle.frameAnchor target.chartAnchor
      current ⟨source.frame_mem, middle.frame_mem⟩ target.chart_mem first second
  have hMiddleTargetPartial := transition_secondDerivative_partial_eq
    period hPeriod middle.frameAnchor target.frameAnchor target.chartAnchor
      current ⟨middle.frame_mem, target.frame_mem⟩ target.chart_mem first second
  have hCocycle :=
    throatMetricFrameBaseChartTransition_secondDerivative_cocycle_apply
      period hPeriod source.frameAnchor middle.frameAnchor target.frameAnchor
        target.chartAnchor target.chartAnchor current
        ⟨source.frame_mem, middle.frame_mem, target.frame_mem⟩
        target.chart_mem target.chart_mem first second value
  rw [hBaseSelf] at hCocycle
  simp only [ContinuousLinearMap.id_apply] at hCocycle
  rw [hBasePartialZero] at hCocycle
  simp only [map_zero, zero_apply, add_zero] at hCocycle
  rw [hDirectPartial, hSourceMiddlePartial, hMiddleTargetPartial,
    hReparamFirst, hReparamSecondDirection, hReparamSecond] at hCocycle
  simpa only [throatMetricSecondOrderJetSemidirectChangeAt_baseFirst,
    throatMetricSecondOrderJetSemidirectChangeAt_baseSecond,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberValue,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberFirst,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberSecond,
    throatMetricTargetFrameTransitionSecondDerivativeAt,
    throatCovariantTwoTensorTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
      target.chart_mem,
    (extChartAt throatCoverModelWithCorners middle.chartAnchor).left_inv
      middle.chart_mem,
    add_apply, map_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, add_zero] using hCocycle

/-! ## Identity -/

/-- Transport from a frame/chart pair to itself fixes every raw metric jet. -/
@[simp]
theorem throatMetricSecondOrderJetSemidirectTransportAt_self_apply
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (jet : MetricJet) :
    throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
      presentation presentation jet = jet := by
  let change := throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
    presentation presentation
  have hBaseFirst : change.baseFirst =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [change,
      throatMetricSecondOrderJetSemidirectChangeAt_baseFirst,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod presentation.chartAnchor current
          presentation.chart_mem
  have hBaseSecond : change.baseSecond = 0 := by
    simpa only [change,
      throatMetricSecondOrderJetSemidirectChangeAt_baseSecond,
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod presentation.chartAnchor current
          presentation.chart_mem
  have hFiberValue : change.fiberValue =
      ContinuousLinearMap.id Real TensorModel := by
    simpa only [change,
      throatMetricSecondOrderJetSemidirectChangeAt_fiberValue,
      throatCovariantTwoTensorTransitionCenteredChart,
      (extChartAt throatCoverModelWithCorners
        presentation.chartAnchor).left_inv presentation.chart_mem,
      ContinuousLinearEquiv.coe_coe] using
      throatCovariantTwoTensorTransitionCenteredChart_self period hPeriod
        presentation.frameAnchor presentation.chartAnchor current
          presentation.frame_mem presentation.chart_mem
  have hFiberFirst : change.fiberFirst = 0 := by
    simpa only [change,
      throatMetricSecondOrderJetSemidirectChangeAt_fiberFirst] using
      throatCovariantTwoTensorTransitionCenteredChart_self_firstDerivative
        period hPeriod presentation.frameAnchor presentation.chartAnchor
          current presentation.frame_mem presentation.chart_mem
  have hFiberSecond : change.fiberSecond = 0 := by
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [change,
      throatMetricSecondOrderJetSemidirectChangeAt_fiberSecond]
    rw [throatMetricTargetFrameTransitionSecondDerivativeAt]
    rw [← transition_secondDerivative_partial_eq period hPeriod
      presentation.frameAnchor presentation.frameAnchor
      presentation.chartAnchor current
      ⟨presentation.frame_mem, presentation.frame_mem⟩
      presentation.chart_mem first second]
    rw [throatCovariantTwoTensorTransitionCenteredChart_self_secondDerivative
      period hPeriod presentation.frameAnchor presentation.chartAnchor current
      presentation.frame_mem presentation.chart_mem second]
    rfl
  change change.toContinuousLinearMap jet = jet
  apply FramedSecondOrderJet.ext_components
  · simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_value, hFiberValue,
      ContinuousLinearMap.id_apply]
  · apply ContinuousLinearMap.ext
    intro direction
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_firstDerivative_apply,
      hBaseFirst, hFiberValue, hFiberFirst, ContinuousLinearMap.id_apply,
      zero_apply, add_zero]
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [FramedSecondOrderJetSemidirectChange.toContinuousLinearMap_apply,
      FramedSecondOrderJetSemidirectChange.transport_secondDerivative_apply,
      hBaseFirst, hBaseSecond, hFiberValue, hFiberFirst, hFiberSecond,
      ContinuousLinearMap.id_apply, zero_apply, map_zero, add_zero]

/-- Self-transport is the identity continuous linear map. -/
@[simp]
theorem throatMetricSecondOrderJetSemidirectTransportAt_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current) :
    throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        presentation presentation =
      ContinuousLinearMap.id Real MetricJet := by
  apply ContinuousLinearMap.ext
  intro jet
  exact throatMetricSecondOrderJetSemidirectTransportAt_self_apply
    period hPeriod presentation jet

/-! ## Composition and inverses -/

/-- Transport through an intermediate frame/chart pair equals direct
transport on every raw metric jet. -/
theorem throatMetricSecondOrderJetSemidirectTransportAt_comp_apply
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (jet : MetricJet) :
    throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        source target jet =
      throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        middle target
        (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
          source middle jet) := by
  change
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).toContinuousLinearMap jet =
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      middle target).toContinuousLinearMap
      ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source middle).toContinuousLinearMap jet)
  exact semidirect_transport_comp_of_coefficients
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source middle)
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      middle target)
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target)
    (change_baseFirst_comp period hPeriod source middle target)
    (change_baseSecond_comp period hPeriod source middle target)
    (change_fiberValue_comp period hPeriod source middle target)
    (change_fiberFirst_comp period hPeriod source middle target)
    (change_fiberSecond_comp period hPeriod source middle target) jet

/-- Metric semidirect transport composes exactly through any intermediate
frame/chart pair. -/
theorem throatMetricSecondOrderJetSemidirectTransportAt_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current) :
    throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        source target =
      (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        middle target).comp
        (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
          source middle) := by
  apply ContinuousLinearMap.ext
  intro jet
  exact throatMetricSecondOrderJetSemidirectTransportAt_comp_apply
    period hPeriod source middle target jet

/-- Reverse metric transport is a left inverse. -/
theorem throatMetricSecondOrderJetSemidirectTransportAt_inverse_comp
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        target source).comp
        (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
          source target) =
      ContinuousLinearMap.id Real MetricJet := by
  rw [← throatMetricSecondOrderJetSemidirectTransportAt_comp
    period hPeriod source target source]
  exact throatMetricSecondOrderJetSemidirectTransportAt_self
    period hPeriod source

/-- Reverse metric transport is a right inverse. -/
theorem throatMetricSecondOrderJetSemidirectTransportAt_comp_inverse
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        source target).comp
        (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
          target source) =
      ContinuousLinearMap.id Real MetricJet := by
  exact throatMetricSecondOrderJetSemidirectTransportAt_inverse_comp
    period hPeriod target source

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportGroupoid4D
end JanusFormal
