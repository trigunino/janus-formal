import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D

/-!
# Semidirect transport of actual throat gauge third jets

The existing second-order gauge semidirect change is extended by the genuine
third derivatives of the reverse base-chart transition and the forward
covector-frame transition.  Forgetting the third derivative recovers exactly
the existing second-order transport.

No third-order fiber cocycle, third-jet groupoid, or descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransport4D

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
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev GaugePresentationAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPresentationAt period hPeriod current

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Actual gauge third-order semidirect coefficients from `source` to
`target`.  Its second-order parent is definitionally the existing gauge
change. -/
def throatGaugeThirdOrderJetSemidirectChangeAt
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    FramedThirdOrderJetSemidirectChange
      ThroatCoverCoordinates (FramedCovector ThroatCoverCoordinates) := by
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
        throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
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
        throatGaugeCovectorTargetTransitionThirdDerivativeAt period hPeriod
          source target
      fiberThird_swap_first_second :=
        throatGaugeCovectorTargetTransitionThirdDerivativeAt_swap_first_second
          period hPeriod source target
      fiberThird_swap_second_third :=
        throatGaugeCovectorTargetTransitionThirdDerivativeAt_swap_second_third
          period hPeriod source target }

/-- Pointwise semidirect transport on actual framed gauge third jets. -/
def throatGaugeThirdOrderJetSemidirectTransportAt
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (jet : GaugeThirdJet) : GaugeThirdJet :=
  (throatGaugeThirdOrderJetSemidirectChangeAt period hPeriod
    source target).transport jet

/-- Forgetting the third derivative recovers exactly the existing actual
gauge second-order semidirect transport. -/
@[simp]
theorem throatGaugeThirdOrderJetSemidirectTransportAt_truncate
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (jet : GaugeThirdJet) :
    (throatGaugeThirdOrderJetSemidirectTransportAt period hPeriod
      source target jet).toFramedSecondOrderJet =
      throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        source target jet.toFramedSecondOrderJet :=
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransport4D
end JanusFormal
