import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricCombinedFrameBaseChartSecondOrderGroupoid4D

/-!
# Third derivative of the actual throat metric frame transition

The centered covariant rank-two frame transition is smooth at every valid
frame/chart pair.  This gate exposes its genuine third Frechet derivative in
the target base chart and proves the two adjacent symmetries of that
coefficient.

This is only the third-order fiber-transition coefficient.  No third-jet
transport, cocycle, physical atlas, or current descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatMetricCombinedFrameBaseChartSecondOrderGroupoid4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev MetricFrameChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatMetricSecondOrderJetFrameChartAt period hPeriod current

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedSpace

private abbrev TensorEnd :=
  TensorModel →L[Real] TensorModel

local instance tensorEndNormedAddCommGroup :
    NormedAddCommGroup TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorEndNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorEndNormedSpace

private abbrev TensorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] TensorEnd

local instance tensorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real TensorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev TensorTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] TensorTransitionFirstDerivative

local instance tensorTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionSecondDerivativeNormedSpace :
    NormedSpace Real TensorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  have hApply := congrArg
    (fun derivative : E →L[Real] G => derivative direction) hDerivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hApply

private theorem thirdFDeriv_swap_second_third
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (function : E → F) (point first second third : E)
    (hFunction : ContDiffAt Real 3 function point) :
    fderiv Real (fderiv Real (fderiv Real function)) point first second third =
      fderiv Real (fderiv Real (fderiv Real function)) point first third second := by
  have hHessian :
      DifferentiableAt Real (fderiv Real (fderiv Real function)) point :=
    ((hFunction.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hHessianAtSecond :
      DifferentiableAt Real
        (fun nearby => fderiv Real (fderiv Real function) nearby second) point :=
    hHessian.clm_apply (differentiableAt_const (c := second))
  have hHessianAtThird :
      DifferentiableAt Real
        (fun nearby => fderiv Real (fderiv Real function) nearby third) point :=
    hHessian.clm_apply (differentiableAt_const (c := third))
  have hNearbySymmetry :
      Filter.EventuallyEq (𝓝 point)
        (fun nearby => fderiv Real (fderiv Real function) nearby second third)
        (fun nearby => fderiv Real (fderiv Real function) nearby third second) := by
    filter_upwards [hFunction.eventually (by norm_num)] with nearby hNearby
    exact (hNearby.isSymmSndFDerivAt (𝕜 := Real) (by norm_num)).eq second third
  have hDerivativeEquality := hNearbySymmetry.fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : E →L[Real] F => derivative first) hDerivativeEquality
  have hOuterSecond :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby second)
          point first =
        fderiv Real (fderiv Real (fderiv Real function)) point first second :=
    fderiv_continuousLinearMap_apply_const _ point first second hHessian
  have hOuterThird :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby third)
          point first =
        fderiv Real (fderiv Real (fderiv Real function)) point first third :=
    fderiv_continuousLinearMap_apply_const _ point first third hHessian
  have hSecondThird :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby second third)
          point first =
        fderiv Real (fderiv Real (fderiv Real function))
          point first second third := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby second)
          point first third :=
        fderiv_continuousLinearMap_apply_const _ point first third
          hHessianAtSecond
      _ = _ := congrArg (fun derivative : E →L[Real] F => derivative third)
        hOuterSecond
  have hThirdSecond :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby third second)
          point first =
        fderiv Real (fderiv Real (fderiv Real function))
          point first third second := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real function) nearby third)
          point first second :=
        fderiv_continuousLinearMap_apply_const _ point first second
          hHessianAtThird
      _ = _ := congrArg (fun derivative : E →L[Real] F => derivative second)
        hOuterThird
  rw [hSecondThird, hThirdSecond] at hApplied
  exact hApplied

/-- Genuine third derivative of the forward covariant-tensor frame transition,
expressed in the target base chart. -/
def throatMetricTargetFrameTransitionThirdDerivativeAt
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] TensorEnd :=
  fderiv Real
    (fderiv Real
      (fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          source.frameAnchor target.frameAnchor target.chartAnchor)))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)

/-- The first two directions of the third fiber-transition coefficient
commute. -/
theorem throatMetricTargetFrameTransitionThirdDerivativeAt_swap_first_second
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatMetricTargetFrameTransitionThirdDerivativeAt period hPeriod
        source target first second third =
      throatMetricTargetFrameTransitionThirdDerivativeAt period hPeriod
        source target second first third := by
  have hFirstDerivative :
      ContDiffAt Real 2
        (fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
        current ⟨source.frame_mem, target.frame_mem⟩ target.chart_mem).fderiv_right
          (m := 2) (by
            change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  have hSymmetric :=
    (hFirstDerivative.isSymmSndFDerivAt (by norm_num)).eq first second
  exact congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] TensorEnd =>
      derivative third) hSymmetric

/-- The last two directions of the third fiber-transition coefficient
commute. -/
theorem throatMetricTargetFrameTransitionThirdDerivativeAt_swap_second_third
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatMetricTargetFrameTransitionThirdDerivativeAt period hPeriod
        source target first second third =
      throatMetricTargetFrameTransitionThirdDerivativeAt period hPeriod
        source target first third second := by
  let transition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      source.frameAnchor target.frameAnchor target.chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners target.chartAnchor current
  have hTransitionC3 : ContDiffAt Real 3 transition coordinate :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
        current ⟨source.frame_mem, target.frame_mem⟩ target.chart_mem).of_le (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  simpa only [throatMetricTargetFrameTransitionThirdDerivativeAt,
    transition, coordinate] using
      thirdFDeriv_swap_second_third transition coordinate first second third
        hTransitionC3

/-- The genuine third derivative of a repeated-frame transition vanishes. -/
@[simp]
theorem throatMetricTargetFrameTransitionThirdDerivativeAt_self
    {current : EffectiveThroat period hPeriod}
    (frameChart : MetricFrameChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    throatMetricTargetFrameTransitionThirdDerivativeAt period hPeriod
        frameChart frameChart first second third = 0 := by
  let transition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      frameChart.frameAnchor frameChart.frameAnchor frameChart.chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners frameChart.chartAnchor current
  have hFirstDerivative :
      fderiv Real transition =ᶠ[𝓝 coordinate]
        fun _ => (0 : TensorTransitionFirstDerivative) := by
    filter_upwards [
      (throatCovariantTwoTensorTransitionCenteredChart_self_eventuallyEq
        period hPeriod frameChart.frameAnchor frameChart.chartAnchor current
          frameChart.frame_mem frameChart.chart_mem).fderiv
            (𝕜 := Real)] with nearby hNearby
    simpa [transition, coordinate] using hNearby
  have hSecondDerivative :
      fderiv Real (fderiv Real transition) =ᶠ[𝓝 coordinate]
        fun _ => (0 : TensorTransitionSecondDerivative) := by
    filter_upwards [hFirstDerivative.fderiv (𝕜 := Real)]
      with nearby hNearby
    simpa using hNearby
  have hThirdDerivative :
      fderiv Real (fderiv Real (fderiv Real transition)) coordinate = 0 :=
    (hSecondDerivative.fderiv_eq (𝕜 := Real)).trans
      (hasFDerivAt_const (𝕜 := Real) (x := coordinate)
        (c := (0 : TensorTransitionSecondDerivative))).fderiv
  simp only [throatMetricTargetFrameTransitionThirdDerivativeAt]
  rw [hThirdDerivative]
  simp

end
end P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D
end JanusFormal
