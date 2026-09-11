import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D

/-!
# Semidirect transport of actual throat metric third jets

The existing second-order metric semidirect change is extended by the genuine
third derivatives of the reverse base-chart transition and the forward
covariant-tensor frame transition.  Forgetting the third derivative recovers
exactly the existing second-order transport.

No third-order fiber cocycle, third-jet groupoid, or descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D

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
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  ThroatCovariantTwoTensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedSpace

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

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

/-- Actual metric third-order semidirect coefficients from `source` to
`target`.  Its second-order parent is definitionally the existing metric
change. -/
def throatMetricThirdOrderJetSemidirectChangeAt
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current) :
    FramedThirdOrderJetSemidirectChange
      ThroatCoverCoordinates TensorModel := by
  have hSource : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod source.chartAnchor := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet] using
      source.chart_mem
  have hTarget : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod target.chartAnchor := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet] using
      target.chart_mem
  exact
    { toFramedSecondOrderJetSemidirectChange :=
        throatMetricSecondOrderJetSemidirectChangeAt period hPeriod
          source target
      baseThird :=
        (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
          source.chartAnchor target.chartAnchor current hSource hTarget).baseThird
      baseThird_swap_first_second :=
        (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
          source.chartAnchor target.chartAnchor current hSource hTarget).baseThird_swap_first_second
      baseThird_swap_second_third :=
        (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
          source.chartAnchor target.chartAnchor current hSource hTarget).baseThird_swap_second_third
      fiberThird :=
        throatMetricTargetFrameTransitionThirdDerivativeAt period hPeriod
          source target
      fiberThird_swap_first_second :=
        throatMetricTargetFrameTransitionThirdDerivativeAt_swap_first_second
          period hPeriod source target
      fiberThird_swap_second_third :=
        throatMetricTargetFrameTransitionThirdDerivativeAt_swap_second_third
          period hPeriod source target }

/-- Pointwise semidirect transport on actual framed metric third jets. -/
def throatMetricThirdOrderJetSemidirectTransportAt
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (jet : MetricThirdJet) : MetricThirdJet :=
  (throatMetricThirdOrderJetSemidirectChangeAt period hPeriod
    source target).transport jet

/-- Forgetting the third derivative recovers exactly the existing actual
metric second-order semidirect transport. -/
@[simp]
theorem throatMetricThirdOrderJetSemidirectTransportAt_truncate
    {current : EffectiveThroat period hPeriod}
    (source target : MetricFrameChartAt period hPeriod current)
    (jet : MetricThirdJet) :
    (throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
      source target jet).toFramedSecondOrderJet =
      throatMetricSecondOrderJetSemidirectTransportAt period hPeriod
        source target jet.toFramedSecondOrderJet :=
  rfl

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D
end JanusFormal
