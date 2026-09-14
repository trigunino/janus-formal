import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D

/-!
# Semidirect transport of actual throat SpinC third jets

The existing second-order SpinC semidirect change is extended by the genuine
third derivatives of the reverse base-chart transition and the forward SpinC
fiber transition.  Forgetting the third derivative recovers exactly the
existing second-order transport.

No third-order SpinC cocycle, groupoid, atlas, or current descent is asserted
here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

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

/-- Actual SpinC third-order semidirect coefficients from `source` to
`target`.  Its second-order parent is definitionally the existing SpinC
change. -/
def throatSpinCThirdOrderJetSemidirectChangeAt
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    FramedThirdOrderJetSemidirectChange
      ThroatCoverCoordinates D9DoubledMatterFiber := by
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
        throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
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
        throatSpinCTargetTrivializationTransitionThirdDerivativeAt period hPeriod
          choice source target
      fiberThird_swap_first_second :=
        throatSpinCTargetTrivializationTransitionThirdDerivativeAt_swap_first_second
          period hPeriod choice source target
      fiberThird_swap_second_third :=
        throatSpinCTargetTrivializationTransitionThirdDerivativeAt_swap_second_third
          period hPeriod choice source target }

/-- Pointwise semidirect transport on actual framed SpinC third jets. -/
def throatSpinCThirdOrderJetSemidirectTransportAt
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCThirdJet) : SpinCThirdJet :=
  (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
    source target).transport jet

/-- Forgetting the third derivative recovers exactly the existing actual
SpinC second-order semidirect transport. -/
@[simp]
theorem throatSpinCThirdOrderJetSemidirectTransportAt_truncate
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCThirdJet) :
    (throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
      source target jet).toFramedSecondOrderJet =
      throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        source target jet.toFramedSecondOrderJet :=
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D
end JanusFormal
