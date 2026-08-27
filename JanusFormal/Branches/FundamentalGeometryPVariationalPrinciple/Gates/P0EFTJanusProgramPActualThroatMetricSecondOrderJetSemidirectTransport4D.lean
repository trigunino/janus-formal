import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D

/-!
# Semidirect transport of actual throat metric second jets

At a fixed throat point, a valid source and target frame/chart pair determine
the reverse base-chart two-jet and the forward covariant-tensor frame two-jet.
The generic semidirect construction then transports arbitrary framed metric
second jets continuously and linearly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D

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
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D

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

private abbrev MetricJet :=
  FramedSecondOrderJet ThroatCoverCoordinates ThroatCovariantTwoTensorModel

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- A tangent frame and base chart both valid at one throat point. -/
structure ThroatMetricSecondOrderJetFrameChartAt
    (current : EffectiveThroat period hPeriod) where
  frameAnchor : EffectiveThroat period hPeriod
  chartAnchor : EffectiveThroat period hPeriod
  frame_mem : current ∈
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) frameAnchor).baseSet
  chart_mem : current ∈
    (extChartAt throatCoverModelWithCorners chartAnchor).source

private abbrev MetricFrameChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatMetricSecondOrderJetFrameChartAt period hPeriod current

/-- Iterated derivative of the forward covariant-tensor frame transition,
expressed in the target base chart. -/
def throatMetricTargetFrameTransitionSecondDerivativeAt
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    ThroatCoverCoordinates →L[Real] TensorTransitionFirstDerivative :=
  fderiv Real
    (fderiv Real
      (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        source.frameAnchor target.frameAnchor target.chartAnchor))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)

/-- Frozen reverse-base and forward-fiber coefficients from `source` to
`target`. -/
def throatMetricSecondOrderJetSemidirectChangeAt
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    FramedSecondOrderJetSemidirectChange
      ThroatCoverCoordinates ThroatCovariantTwoTensorModel where
  baseFirst :=
    fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        target.chartAnchor source.chartAnchor)
      (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  baseSecond :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      target.chartAnchor source.chartAnchor current
        target.chart_mem source.chart_mem).secondDerivative
  baseSecond_symmetric first second :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      target.chartAnchor source.chartAnchor current
        target.chart_mem source.chart_mem).secondDerivative_symmetric
          first second
  fiberValue :=
    throatCovariantTwoTensorFrameTransitionAt period hPeriod
      source.frameAnchor target.frameAnchor current
  fiberFirst :=
    fderiv Real
      (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        source.frameAnchor target.frameAnchor target.chartAnchor)
      (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  fiberSecond :=
    throatMetricTargetFrameTransitionSecondDerivativeAt period hPeriod
      source target
  fiberSecond_symmetric first second := by
    have hSmooth : minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    simpa only [throatMetricTargetFrameTransitionSecondDerivativeAt] using
      ((throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
        period hPeriod source.frameAnchor target.frameAnchor
          target.chartAnchor current ⟨source.frame_mem, target.frame_mem⟩
            target.chart_mem).isSymmSndFDerivAt hSmooth).eq first second

@[simp]
theorem throatMetricSecondOrderJetSemidirectChangeAt_baseFirst
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).baseFirst =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor source.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
  rfl

@[simp]
theorem throatMetricSecondOrderJetSemidirectChangeAt_baseSecond
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).baseSecond =
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor source.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) := by
  simp [throatMetricSecondOrderJetSemidirectChangeAt]

@[simp]
theorem throatMetricSecondOrderJetSemidirectChangeAt_fiberValue
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).fiberValue =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
        source.frameAnchor target.frameAnchor current :=
  rfl

@[simp]
theorem throatMetricSecondOrderJetSemidirectChangeAt_fiberFirst
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).fiberFirst =
      fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          source.frameAnchor target.frameAnchor target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
  rfl

@[simp]
theorem throatMetricSecondOrderJetSemidirectChangeAt_fiberSecond
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
      source target).fiberSecond =
      throatMetricTargetFrameTransitionSecondDerivativeAt period hPeriod
        source target :=
  rfl

/-- Continuous linear transport on the full framed metric second-jet
carrier. -/
def throatMetricSecondOrderJetSemidirectTransportAt
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    MetricJet →L[Real] MetricJet :=
  (throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
    source target).toContinuousLinearMap

@[simp]
theorem throatMetricSecondOrderJetSemidirectTransportAt_value
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (jet : MetricJet) :
    (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
      source target jet).value =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
        source.frameAnchor target.frameAnchor current jet.value :=
  rfl

@[simp]
theorem throatMetricSecondOrderJetSemidirectTransportAt_firstDerivative_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (jet : MetricJet) (direction : ThroatCoverCoordinates) :
    (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
      source target jet).firstDerivative direction =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
          source.frameAnchor target.frameAnchor current
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            direction)) +
      fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          direction jet.value :=
  rfl

@[simp]
theorem throatMetricSecondOrderJetSemidirectTransportAt_secondDerivative_apply
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (jet : MetricJet) (first second : ThroatCoverCoordinates) :
    (throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
      source target jet).secondDerivative first second =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
          source.frameAnchor target.frameAnchor current
        (jet.secondDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            second)) +
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
          source.frameAnchor target.frameAnchor current
        (jet.firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                target.chartAnchor source.chartAnchor))
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first second)) +
      fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          first
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            second)) +
      fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          second
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first)) +
      throatMetricTargetFrameTransitionSecondDerivativeAt period hPeriod
        source target first second jet.value :=
  rfl

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
end JanusFormal
