import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D

/-!
# Compatibility of metric second-jet semidirect transport

The concrete inverse-base/forward-frame semidirect transport sends the second
jet extracted in any valid source frame and chart exactly to the second jet
extracted in any valid target frame and chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportCompatibility4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedSpace

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

/-- Semidirect transport of an actually extracted source metric jet is the
actually extracted metric jet in the requested target frame and chart. -/
theorem throatMetricSecondOrderJetSemidirectTransportAt_extracted
    {current : EffectiveThroat period hPeriod}
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (source target :
      ThroatMetricSecondOrderJetFrameChartAt period hPeriod current) :
    throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        source target
        (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          source.frameAnchor source.chartAnchor current
            source.frame_mem source.chart_mem) =
      throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        target.frameAnchor target.chartAnchor current
          target.frame_mem target.chart_mem := by
  let sourceJet :=
    throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      source.frameAnchor source.chartAnchor current
        source.frame_mem source.chart_mem
  let sourceInTargetChart :=
    throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      source.frameAnchor target.chartAnchor current
        source.frame_mem target.chart_mem
  let targetJet :=
    throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      target.frameAnchor target.chartAnchor current
        target.frame_mem target.chart_mem
  let Ainv := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      target.chartAnchor source.chartAnchor)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  let Binv := fderiv Real
    (fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        target.chartAnchor source.chartAnchor))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  let D :=
    throatCovariantTwoTensorFrameTransitionAt period hPeriod
      source.frameAnchor target.frameAnchor current
  let E := fderiv Real
    (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      source.frameAnchor target.frameAnchor target.chartAnchor)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  let F := throatMetricTargetFrameTransitionSecondDerivativeAt period hPeriod
    source target
  change throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
    source target sourceJet = targetJet
  have hFrames : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) source.frameAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) target.frameAnchor).baseSet :=
    ⟨source.frame_mem, target.frame_mem⟩
  have hSourceValue : sourceInTargetChart.value = sourceJet.value := by
    simp only [sourceInTargetChart, sourceJet,
      throatTensorSecondOrderJetInFrameChartAt_value]
  have hBaseFirst : sourceInTargetChart.firstDerivative =
      sourceJet.firstDerivative.comp Ainv := by
    simpa only [sourceInTargetChart, sourceJet, Ainv] using
      throatTensorSecondOrderJetInFrameChartAt_firstDerivative_transition
        period hPeriod tensor source.frameAnchor target.chartAnchor
          source.chartAnchor current source.frame_mem target.chart_mem
            source.chart_mem
  have hBaseSecond (first second : ThroatCoverCoordinates) :
      sourceInTargetChart.secondDerivative first second =
        sourceJet.secondDerivative (Ainv first) (Ainv second) +
          sourceJet.firstDerivative (Binv first second) := by
    simpa only [sourceInTargetChart, sourceJet, Ainv, Binv] using
      throatTensorSecondOrderJetInFrameChartAt_secondDerivative_transition_apply
        period hPeriod tensor source.frameAnchor target.chartAnchor
          source.chartAnchor current source.frame_mem target.chart_mem
            source.chart_mem first second
  have hFrameValue : targetJet.value = D sourceInTargetChart.value := by
    simpa only [targetJet, sourceInTargetChart, D,
      ContinuousLinearEquiv.coe_coe] using
      throatTensorSecondOrderJet_arbitraryFrameBaseChart_value
        period hPeriod tensor source.frameAnchor target.frameAnchor
          target.chartAnchor target.chartAnchor current hFrames
            target.chart_mem target.chart_mem
  have hBaseSelfFirst :
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod target.chartAnchor current target.chart_mem
  have hBaseSelfSecond :
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
      0 := by
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod target.chartAnchor current target.chart_mem
  have hFrameFirst :=
    throatTensorSecondOrderJet_arbitraryFrameBaseChart_firstDerivative_transition
      period hPeriod tensor source.frameAnchor target.frameAnchor
        target.chartAnchor target.chartAnchor current hFrames
          target.chart_mem target.chart_mem
  have hFrameSecond (first second : ThroatCoverCoordinates) :=
    throatTensorSecondOrderJet_arbitraryFrameBaseChart_secondDerivative_transition_apply
      period hPeriod tensor source.frameAnchor target.frameAnchor
        target.chartAnchor target.chartAnchor current hFrames
          target.chart_mem target.chart_mem first second
  have hForwardDerivative : DifferentiableAt Real
      (fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          source.frameAnchor target.frameAnchor target.chartAnchor))
      (extChartAt throatCoverModelWithCorners target.chartAnchor current) := by
    have hSmooth : ((1 : ℕ∞ω) + 1) ≤ (∞ : ℕ∞ω) := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact
      ((throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
        period hPeriod source.frameAnchor target.frameAnchor target.chartAnchor
          current hFrames target.chart_mem).fderiv_right
            (m := 1) hSmooth).differentiableAt (by norm_num)
  have hFBridge (first second : ThroatCoverCoordinates) :
      fderiv Real
          (fun coordinate ↦ fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              source.frameAnchor target.frameAnchor target.chartAnchor)
            coordinate second)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first = F first second := by
    simpa only [F, throatMetricTargetFrameTransitionSecondDerivativeAt] using
      fderiv_clm_apply_const_apply
        (fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          first second hForwardDerivative
  apply FramedSecondOrderJet.ext_components
  · rw [throatMetricSecondOrderJetSemidirectTransportAt_value]
    rw [hSourceValue] at hFrameValue
    exact hFrameValue.symm
  · apply ContinuousLinearMap.ext
    intro direction
    rw [throatMetricSecondOrderJetSemidirectTransportAt_firstDerivative_apply]
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real] TensorModel ↦
        derivative direction) hFrameFirst
    have hBaseApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real] TensorModel ↦
        derivative direction) hBaseFirst
    simp only [hBaseSelfFirst, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, add_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    simp only [ContinuousLinearMap.comp_apply] at hBaseApplied
    rw [hBaseApplied, hSourceValue] at hApplied
    simpa only [sourceJet, Ainv, D, E,
      ContinuousLinearEquiv.coe_coe] using hApplied.symm
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    rw [throatMetricSecondOrderJetSemidirectTransportAt_secondDerivative_apply]
    have hSecond := hFrameSecond first second
    simp only [hBaseSelfFirst, hBaseSelfSecond,
      ContinuousLinearMap.id_apply, zero_apply, map_zero, add_zero] at hSecond
    have hBaseFirstAppliedFirst := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real] TensorModel ↦
        derivative first) hBaseFirst
    have hBaseFirstAppliedSecond := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real] TensorModel ↦
        derivative second) hBaseFirst
    simp only [ContinuousLinearMap.comp_apply] at hBaseFirstAppliedFirst
    simp only [ContinuousLinearMap.comp_apply] at hBaseFirstAppliedSecond
    rw [hBaseSecond first second, hBaseFirstAppliedFirst,
      hBaseFirstAppliedSecond, hSourceValue, hFBridge first second] at hSecond
    simp only [map_add] at hSecond
    simpa only [sourceJet, Ainv, Binv, D, E, F,
      ContinuousLinearEquiv.coe_coe] using hSecond.symm

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportCompatibility4D
end JanusFormal
