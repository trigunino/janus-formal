import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportGroupoid4D

/-!
# Groupoid laws for actual throat metric third-jet transport

The genuine reverse base-chart derivatives and forward covariant-tensor frame
derivatives satisfy the coefficient laws required by the generic third-order
semidirect groupoid criterion.  Hence the actual framed metric third-jet
transport has exact identity, composition, and inverse laws.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportGroupoid4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 4000000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatMetricCombinedFrameBaseChartSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricSecondJet :=
  FramedSecondOrderJet ThroatCoverCoordinates TensorModel

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

private abbrev MetricFrameChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatMetricSecondOrderJetFrameChartAt period hPeriod current

private abbrev TensorEnd :=
  TensorModel →L[Real] TensorModel

attribute [local instance]
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedAddCommGroup
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem contDiffThree_le_infty :
    ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
  WithTop.coe_le_coe.mpr le_top

private def metricSecondJetOfValue
    (value : TensorModel) : MetricSecondJet where
  value := value
  firstDerivative := 0
  secondDerivative := 0
  secondDerivative_symmetric first second := by simp

/-! ## Concrete coefficient projections -/

@[simp] private theorem thirdOrderChange_baseFirst_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).baseFirst direction =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor source.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        direction := by
  change
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).baseFirst direction = _
  rfl

@[simp] private theorem thirdOrderChange_baseSecond_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).baseSecond first second =
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor source.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second := by
  change
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).baseSecond first second = _
  rfl

@[simp] private theorem thirdOrderChange_baseThird_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).baseThird first second third =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second third := by
  rfl

@[simp] private theorem thirdOrderChange_fiberValue_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).fiberValue value =
      throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        source.frameAnchor target.frameAnchor target.chartAnchor
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        value := by
  change
    throatCovariantTwoTensorFrameTransitionAt period hPeriod
        source.frameAnchor target.frameAnchor current value = _
  simp only [throatCovariantTwoTensorTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
      target.chart_mem, ContinuousLinearEquiv.coe_apply]

@[simp] private theorem thirdOrderChange_fiberFirst_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).fiberFirst direction value =
      fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          source.frameAnchor target.frameAnchor target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        direction value := by
  rfl

@[simp] private theorem thirdOrderChange_fiberSecond_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).fiberSecond first second value =
      fderiv Real
        (fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second value := by
  rfl

@[simp] private theorem thirdOrderChange_fiberThird_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).fiberThird first second third value =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              source.frameAnchor target.frameAnchor target.chartAnchor)))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second third value := by
  rfl

/-! ## Lower-order coefficient laws from the actual J2 groupoid -/

private theorem thirdOrderChange_fiberValue_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).fiberValue value = value := by
  change
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).fiberValue value = value
  have hTransport :=
    throatMetricSecondOrderJetSemidirectTransportAt_self_apply period hPeriod
      presentation (metricSecondJetOfValue value)
  have hApplied := congrArg (fun jet : MetricSecondJet => jet.value) hTransport
  simpa only [throatMetricSecondOrderJetSemidirectTransportAt_value,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberValue,
    metricSecondJetOfValue, ContinuousLinearEquiv.coe_apply] using hApplied

private theorem thirdOrderChange_fiberFirst_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).fiberFirst direction value = 0 := by
  change
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).fiberFirst direction value = 0
  have hTransport :=
    throatMetricSecondOrderJetSemidirectTransportAt_self_apply period hPeriod
      presentation (metricSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : MetricSecondJet => jet.firstDerivative direction) hTransport
  simpa only [throatMetricSecondOrderJetSemidirectTransportAt_firstDerivative_apply,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberFirst,
    metricSecondJetOfValue, zero_apply, map_zero, zero_add] using hApplied

private theorem thirdOrderChange_fiberSecond_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).fiberSecond first second value = 0 := by
  change
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).fiberSecond first second value = 0
  have hTransport :=
    throatMetricSecondOrderJetSemidirectTransportAt_self_apply period hPeriod
      presentation (metricSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : MetricSecondJet => jet.secondDerivative first second) hTransport
  simpa only [throatMetricSecondOrderJetSemidirectTransportAt_secondDerivative_apply,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberSecond,
    metricSecondJetOfValue, zero_apply, map_zero, zero_add, add_zero] using hApplied

private theorem thirdOrderChange_fiberValue_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source target).fiberValue value =
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        middle target).fiberValue
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).fiberValue value) := by
  change
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        source target).fiberValue value =
      (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
        middle target).fiberValue
        ((throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          source middle).fiberValue value)
  have hTransport :=
    throatMetricSecondOrderJetSemidirectTransportAt_comp_apply period hPeriod
      source middle target (metricSecondJetOfValue value)
  have hApplied := congrArg (fun jet : MetricSecondJet => jet.value) hTransport
  simpa only [throatMetricSecondOrderJetSemidirectTransportAt_value,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberValue,
    metricSecondJetOfValue, ContinuousLinearEquiv.coe_apply] using hApplied

private theorem thirdOrderChange_fiberFirst_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source target).fiberFirst direction value =
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberValue
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst direction) value) +
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberFirst direction
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).fiberValue value) := by
  change
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
          source middle).fiberValue value)
  have hTransport :=
    throatMetricSecondOrderJetSemidirectTransportAt_comp_apply period hPeriod
      source middle target (metricSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : MetricSecondJet => jet.firstDerivative direction) hTransport
  simpa only [throatMetricSecondOrderJetSemidirectTransportAt_value,
    throatMetricSecondOrderJetSemidirectTransportAt_firstDerivative_apply,
    throatMetricSecondOrderJetSemidirectChangeAt_baseFirst,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberValue,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberFirst,
    metricSecondJetOfValue, zero_apply, map_zero, zero_add,
    ContinuousLinearEquiv.coe_apply] using hApplied

private theorem thirdOrderChange_fiberSecond_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates)
    (value : TensorModel) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source target).fiberSecond first second value =
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberValue
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberSecond
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first)
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second) value) +
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberValue
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseSecond first second) value) +
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberFirst first
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second) value) +
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberFirst second
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            source middle).fiberFirst
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first) value) +
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).fiberSecond first second
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).fiberValue value) := by
  change
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
          source middle).fiberValue value)
  have hTransport :=
    throatMetricSecondOrderJetSemidirectTransportAt_comp_apply period hPeriod
      source middle target (metricSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : MetricSecondJet => jet.secondDerivative first second) hTransport
  simpa only [throatMetricSecondOrderJetSemidirectTransportAt_value,
    throatMetricSecondOrderJetSemidirectTransportAt_firstDerivative_apply,
    throatMetricSecondOrderJetSemidirectTransportAt_secondDerivative_apply,
    throatMetricSecondOrderJetSemidirectChangeAt_baseFirst,
    throatMetricSecondOrderJetSemidirectChangeAt_baseSecond,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberValue,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberFirst,
    throatMetricSecondOrderJetSemidirectChangeAt_fiberSecond,
    metricSecondJetOfValue, zero_apply, map_zero, zero_add, add_zero,
    ContinuousLinearEquiv.coe_apply] using
      hApplied

/-! ## Reverse-base coefficient laws -/

private theorem thirdOrderChange_baseFirst_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).baseFirst direction = direction := by
  rw [thirdOrderChange_baseFirst_apply]
  have hSelf :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
      period hPeriod presentation.chartAnchor current presentation.chart_mem
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates =>
      derivative direction) hSelf
  simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    ContinuousLinearMap.id_apply] using hApplied

private theorem thirdOrderChange_baseSecond_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).baseSecond first second = 0 := by
  rw [thirdOrderChange_baseSecond_apply]
  have hSelf :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
      period hPeriod presentation.chartAnchor current presentation.chart_mem
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates =>
      derivative first second) hSelf
  simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative,
    zero_apply] using hApplied

private theorem thirdOrderChange_baseThird_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).baseThird first second third = 0 := by
  rw [thirdOrderChange_baseThird_apply]
  simpa only [throatGaugeBaseChartTransitionThirdDerivativeAt] using
    throatGaugeBaseChartTransitionThirdDerivativeAt_self period hPeriod
      presentation.chartAnchor current presentation.chart_mem
      first second third

private theorem thirdOrderChange_baseFirst_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source target).baseFirst direction =
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source middle).baseFirst
        ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          middle target).baseFirst direction) := by
  simp only [thirdOrderChange_baseFirst_apply]
  have hCocycle :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
      period hPeriod target.chartAnchor middle.chartAnchor source.chartAnchor
        current target.chart_mem middle.chart_mem source.chart_mem
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates =>
      derivative direction) hCocycle
  simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    ContinuousLinearMap.comp_apply] using hApplied

private theorem thirdOrderChange_baseSecond_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source target).baseSecond first second =
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).baseSecond
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first)
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second) +
        (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).baseFirst
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseSecond first second) := by
  simp only [thirdOrderChange_baseFirst_apply,
    thirdOrderChange_baseSecond_apply]
  simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
    throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
      period hPeriod target.chartAnchor middle.chartAnchor source.chartAnchor
        current target.chart_mem middle.chart_mem source.chart_mem first second

private theorem thirdOrderChange_baseThird_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source target).baseThird first second third =
      (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).baseThird
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first)
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second)
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst third) +
        (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).baseSecond
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseSecond first second)
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst third) +
        (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).baseSecond
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseSecond first third)
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst second) +
        (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).baseSecond
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseSecond second third)
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseFirst first) +
        (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
          source middle).baseFirst
          ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
            middle target).baseThird first second third) := by
  simp only [thirdOrderChange_baseFirst_apply,
    thirdOrderChange_baseSecond_apply, thirdOrderChange_baseThird_apply]
  exact throatGaugeBaseChartTransitionThirdDerivativeAt_cocycle period hPeriod
    target.chartAnchor middle.chartAnchor source.chartAnchor current
      target.chart_mem middle.chart_mem source.chart_mem first second third

/-! ## Reparametrization of one varying frame transition -/

private theorem transition_baseChart_eventuallyEq
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
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor firstCenter =ᶠ[nhds
          (extChartAt throatCoverModelWithCorners firstCenter current)]
      (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  have hCombined :=
    throatMetricFrameBaseChartTransition_cocycle_eventuallyEq period hPeriod
      firstAnchor firstAnchor secondAnchor firstCenter secondCenter secondCenter
      current ⟨hFrames.1, ⟨hFrames.1, hFrames.2⟩⟩ hFirst hSecond
  have hFiber := hCombined.fun_comp Prod.snd
  have hSelf :=
    throatCovariantTwoTensorTransitionCenteredChart_self_eventuallyEq period hPeriod
      firstAnchor firstCenter current hFrames.1 hFirst
  filter_upwards [hFiber, hSelf] with coordinate hFiberAt hSelfAt
  simp only [Function.comp_apply] at hFiberAt
  rw [hSelfAt] at hFiberAt
  simpa only [ContinuousLinearMap.comp_id, Function.comp_apply] using hFiberAt

private theorem transition_value_baseChart
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (value : TensorModel) :
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor firstCenter
        (extChartAt throatCoverModelWithCorners firstCenter current) value =
      throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor secondCenter
        (extChartAt throatCoverModelWithCorners secondCenter current) value := by
  simp only [throatCovariantTwoTensorTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst,
    (extChartAt throatCoverModelWithCorners secondCenter).left_inv hSecond]

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
    (direction : ThroatCoverCoordinates)
    (value : TensorModel) :
    fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)
        direction value =
      fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
          direction) value := by
  let inner :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let outer :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor secondCenter
  let point :=
    extChartAt throatCoverModelWithCorners firstCenter current
  have hInner : ContDiffAt Real 3 inner point :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le
        contDiffThree_le_infty
  have hOuter : ContDiffAt Real 3 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod firstAnchor secondAnchor secondCenter current hFrames
        hSecond).of_le contDiffThree_le_infty
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 3 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod
    firstAnchor secondAnchor firstCenter secondCenter current hFrames hFirst
      hSecond
  have hDerivative := hGerm.fderiv_eq (𝕜 := Real)
  have hChain := fderiv_comp point
    (hOuterAt.differentiableAt (by norm_num))
    (hInner.differentiableAt (by norm_num))
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] TensorEnd =>
      derivative direction value) (hDerivative.trans hChain)
  simpa only [inner, outer, point, hAt,
    ContinuousLinearMap.comp_apply] using hApplied

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
    (first second : ThroatCoverCoordinates)
    (value : TensorModel) :
    fderiv Real
        (fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter))
        (extChartAt throatCoverModelWithCorners firstCenter current)
        first second value =
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
            (extChartAt throatCoverModelWithCorners firstCenter current) second)
          value +
        fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
            first second) value := by
  let inner :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let outer :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor secondCenter
  let point :=
    extChartAt throatCoverModelWithCorners firstCenter current
  have hInner : ContDiffAt Real 3 inner point :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le
        contDiffThree_le_infty
  have hOuter : ContDiffAt Real 3 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod firstAnchor secondAnchor secondCenter current hFrames
        hSecond).of_le contDiffThree_le_infty
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 3 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod
    firstAnchor secondAnchor firstCenter secondCenter current hFrames hFirst
      hSecond
  have hSecondDerivative :=
    (hGerm.fderiv (𝕜 := Real)).fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] TensorEnd =>
      derivative first second value) hSecondDerivative
  have hFormula :=
    P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D.second_fderiv_comp_apply
      inner outer point (hInner.of_le (by norm_num))
        (hOuterAt.of_le (by norm_num)) first second
  have hFormulaApplied := congrArg
    (fun derivative : TensorEnd => derivative value) hFormula
  exact hApplied.trans (by
    simpa only [inner, outer, point, hAt, add_apply] using hFormulaApplied)

private theorem transition_thirdDerivative_baseChart
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
    (first second third : ThroatCoverCoordinates)
    (value : TensorModel) :
    fderiv Real
        (fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor firstCenter)))
        (extChartAt throatCoverModelWithCorners firstCenter current)
        first second third value =
      fderiv Real
          (fderiv Real
            (fderiv Real
              (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
                firstAnchor secondAnchor secondCenter)))
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) second)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) third)
          value +
        fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor secondCenter))
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
            first second)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) third)
          value +
        fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor secondCenter))
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
            first third)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) second)
          value +
        fderiv Real
          (fderiv Real
            (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor secondCenter))
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
            second third)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
          value +
        fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  firstCenter secondCenter)))
            (extChartAt throatCoverModelWithCorners firstCenter current)
            first second third) value := by
  let inner :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let outer :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor secondCenter
  let point :=
    extChartAt throatCoverModelWithCorners firstCenter current
  have hInner : ContDiffAt Real 3 inner point :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le
        contDiffThree_le_infty
  have hOuter : ContDiffAt Real 3 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod firstAnchor secondAnchor secondCenter current hFrames
        hSecond).of_le contDiffThree_le_infty
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 3 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod
    firstAnchor secondAnchor firstCenter secondCenter current hFrames hFirst
      hSecond
  have hThirdDerivative :=
    ((hGerm.fderiv (𝕜 := Real)).fderiv (𝕜 := Real)).fderiv_eq
      (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] TensorEnd =>
      derivative first second third value) hThirdDerivative
  have hFormula := third_fderiv_comp_apply inner outer point hInner hOuterAt
    first second third
  have hFormulaApplied := congrArg
    (fun derivative : TensorEnd => derivative value) hFormula
  exact hApplied.trans (by
    simpa only [inner, outer, point, hAt, add_apply] using hFormulaApplied)

/-! ## Actual J3 identity and composition -/

/-- Actual metric third-jet self-transport fixes every raw jet. -/
@[simp]
theorem throatMetricThirdOrderJetSemidirectTransportAt_self_apply
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current)
    (jet : MetricThirdJet) :
    throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
      presentation presentation jet = jet := by
  change
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation).transport jet = jet
  exact framedThirdOrderJetSemidirectTransport_self_of_coefficients
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      presentation presentation)
    (thirdOrderChange_baseFirst_self period hPeriod presentation)
    (thirdOrderChange_baseSecond_self period hPeriod presentation)
    (thirdOrderChange_baseThird_self period hPeriod presentation)
    (thirdOrderChange_fiberValue_self period hPeriod presentation)
    (thirdOrderChange_fiberFirst_self period hPeriod presentation)
    (thirdOrderChange_fiberSecond_self period hPeriod presentation)
    (fun first second third value => by
      rw [thirdOrderChange_fiberThird_apply]
      have hSelf :=
        throatMetricTargetFrameTransitionThirdDerivativeAt_self
          period hPeriod presentation first second third
      have hApplied := congrArg
        (fun derivative : TensorEnd => derivative value) hSelf
      simpa only [throatMetricTargetFrameTransitionThirdDerivativeAt,
        zero_apply] using hApplied)
    jet

/-- Actual metric third-jet transport composes through any intermediate
presentation. -/
theorem throatMetricThirdOrderJetSemidirectTransportAt_comp_apply
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current)
    (jet : MetricThirdJet) :
    throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
        source target jet =
      throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
        middle target
        (throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
          source middle jet) := by
  change
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      source target).transport jet =
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
      middle target).transport
      ((throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
        source middle).transport jet)
  apply framedThirdOrderJetSemidirectTransport_comp_of_coefficients
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod source middle)
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod middle target)
    (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod source target)
  · exact thirdOrderChange_baseFirst_comp period hPeriod source middle target
  · exact thirdOrderChange_baseSecond_comp period hPeriod source middle target
  · exact thirdOrderChange_baseThird_comp period hPeriod source middle target
  · exact thirdOrderChange_fiberValue_comp period hPeriod source middle target
  · exact thirdOrderChange_fiberFirst_comp period hPeriod source middle target
  · exact thirdOrderChange_fiberSecond_comp period hPeriod source middle target
  · intro first second third value
    have hBaseFirstSelf :
        fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor target.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
          ContinuousLinearMap.id Real ThroatCoverCoordinates := by
      simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative]
        using
          throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
            period hPeriod target.chartAnchor current target.chart_mem
    have hBaseSecondSelf :
        fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                target.chartAnchor target.chartAnchor))
            (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
          0 := by
      simpa only [throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative]
        using
          throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
            period hPeriod target.chartAnchor current target.chart_mem
    have hBaseThirdSelf :
        fderiv Real
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  target.chartAnchor target.chartAnchor)))
            (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
          0 := by
      apply ContinuousLinearMap.ext
      intro firstDirection
      apply ContinuousLinearMap.ext
      intro secondDirection
      apply ContinuousLinearMap.ext
      intro thirdDirection
      simpa only [throatGaugeBaseChartTransitionThirdDerivativeAt,
        zero_apply] using
        throatGaugeBaseChartTransitionThirdDerivativeAt_self period hPeriod
          target.chartAnchor current target.chart_mem firstDirection
            secondDirection thirdDirection
    have hRaw :=
      throatMetricFrameBaseChartTransition_thirdDerivative_cocycle_apply
        period hPeriod source.frameAnchor middle.frameAnchor target.frameAnchor
        target.chartAnchor target.chartAnchor current
        ⟨source.frame_mem, ⟨middle.frame_mem, target.frame_mem⟩⟩
        target.chart_mem target.chart_mem first second third value
    dsimp only at hRaw
    rw [hBaseFirstSelf, hBaseSecondSelf, hBaseThirdSelf] at hRaw
    simp only [ContinuousLinearMap.id_apply, zero_apply, map_zero,
      add_zero] at hRaw
    rw [transition_thirdDerivative_baseChart period hPeriod
      source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
      target.chart_mem middle.chart_mem first second third value] at hRaw
    rw [transition_secondDerivative_baseChart period hPeriod
      source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
      target.chart_mem middle.chart_mem second third value] at hRaw
    rw [transition_secondDerivative_baseChart period hPeriod
      source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
      target.chart_mem middle.chart_mem first third value] at hRaw
    rw [transition_secondDerivative_baseChart period hPeriod
      source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
      target.chart_mem middle.chart_mem first second value] at hRaw
    rw [transition_firstDerivative_baseChart period hPeriod
      source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
      target.chart_mem middle.chart_mem third value] at hRaw
    rw [transition_firstDerivative_baseChart period hPeriod
      source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
      target.chart_mem middle.chart_mem second value] at hRaw
    rw [transition_firstDerivative_baseChart period hPeriod
      source.frameAnchor middle.frameAnchor target.chartAnchor
      middle.chartAnchor current ⟨source.frame_mem, middle.frame_mem⟩
      target.chart_mem middle.chart_mem first value] at hRaw
    rw [transition_value_baseChart period hPeriod source.frameAnchor
      middle.frameAnchor target.chartAnchor middle.chartAnchor current
      target.chart_mem middle.chart_mem value] at hRaw
    simp only [map_add] at hRaw
    simp only [thirdOrderChange_baseFirst_apply,
      thirdOrderChange_baseSecond_apply, thirdOrderChange_baseThird_apply,
      thirdOrderChange_fiberValue_apply,
      thirdOrderChange_fiberFirst_apply,
      thirdOrderChange_fiberSecond_apply,
      thirdOrderChange_fiberThird_apply]
    rw [hRaw]
    abel

/-! ## Linear-map form and inverses -/

/-- Linear-map packaging of the actual pointwise third-jet transport. -/
def throatMetricThirdOrderJetSemidirectTransportLinearMapAt
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    MetricThirdJet →ₗ[Real] MetricThirdJet :=
  (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
    source target).toLinearMap

@[simp]
theorem throatMetricThirdOrderJetSemidirectTransportLinearMapAt_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (jet : MetricThirdJet) :
    throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        source target jet =
      throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
        source target jet :=
  rfl

/-- Self-transport is the identity linear map. -/
@[simp]
theorem throatMetricThirdOrderJetSemidirectTransportLinearMapAt_self
    {current : EffectiveThroat period hPeriod}
    (presentation : MetricFrameChartAt period hPeriod current) :
    throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        presentation presentation =
      LinearMap.id := by
  apply LinearMap.ext
  intro jet
  exact throatMetricThirdOrderJetSemidirectTransportAt_self_apply period
    hPeriod presentation jet

/-- Actual third-jet transport composes as linear maps. -/
theorem throatMetricThirdOrderJetSemidirectTransportLinearMapAt_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : MetricFrameChartAt period hPeriod current) :
    throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        source target =
      (throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        middle target).comp
        (throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
          source middle) := by
  apply LinearMap.ext
  intro jet
  exact throatMetricThirdOrderJetSemidirectTransportAt_comp_apply period
    hPeriod source middle target jet

/-- Reverse actual transport is a left inverse. -/
theorem throatMetricThirdOrderJetSemidirectTransportLinearMapAt_inverse_comp
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        target source).comp
        (throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
          source target) =
      LinearMap.id := by
  rw [← throatMetricThirdOrderJetSemidirectTransportLinearMapAt_comp
    period hPeriod source target source]
  exact throatMetricThirdOrderJetSemidirectTransportLinearMapAt_self period
    hPeriod source

/-- Reverse actual transport is a right inverse. -/
theorem throatMetricThirdOrderJetSemidirectTransportLinearMapAt_comp_inverse
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        source target).comp
        (throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
          target source) =
      LinearMap.id := by
  exact throatMetricThirdOrderJetSemidirectTransportLinearMapAt_inverse_comp
    period hPeriod target source

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportGroupoid4D
end JanusFormal
