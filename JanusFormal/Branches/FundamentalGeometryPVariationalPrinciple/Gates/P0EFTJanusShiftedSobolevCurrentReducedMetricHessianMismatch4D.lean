import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevQuotientSameActionHessian
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullMatterRobinTrueLLPureMetricInactive4D

/-!
# Obstruction to identifying the periodic pullback Hessian with the current reduced action

The periodic coefficient quotient Hessian is nondegenerate, whereas the
currently assembled global matter+Robin+LL action has no Einstein--Hilbert
block and therefore has zero Hessian on every pure metric direction.  Hence
these two Hessians cannot be identified on a nonzero periodic physical class.

This is only a precise obstruction.  It supplies neither a map from periodic
coefficients to global metric variations nor the missing gravitational action.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevCurrentReducedMetricHessianMismatch4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLPureMetricInactive4D
open P0EFTJanusShiftedSobolevPhysicalQuotient
open P0EFTJanusShiftedSobolevQuotientSameActionHessian

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The nondegenerate periodic pullback cannot equal the Hessian of the
currently assembled reduced global action on a pure metric direction. -/
theorem periodicPhysicalHessian_ne_currentReducedPureMetricHessian
    (targetWeight : P0EFTJanusLatticeFourierSaintVenantExactness.LatticeMode → Real)
    (state : PhysicalPotentialQuotient targetWeight)
    (hState : state ≠ 0)
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (metric : SmoothDiagonalMetricVariation period hPeriod) :
    physicalQuotientActionHessian targetWeight state state ≠
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields
        (pureMetricFullDirection period hPeriod metric)
        (pureMetricFullDirection period hPeriod metric) := by
  rw [pureMetricFullDirection_sectorial_Hessian_zero_left]
  intro hPeriodic
  exact hState
    ((physicalQuotientActionHessian_nondegenerate targetWeight state).mp
      hPeriodic)

end

end P0EFTJanusShiftedSobolevCurrentReducedMetricHessianMismatch4D
end JanusFormal
