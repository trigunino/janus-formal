import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

/-!
# Smooth tensor-frame coefficients for actual throat metric second jets

The base-chart coefficient regularity is imported from the gauge transition
gate.  This file adds only the covariant rank-two fiber transition and the
local `C∞` regularity of its first two Fréchet derivative fields.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
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
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorEndNormedSpace

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

/-- The covariant rank-two frame transition is `C∞` at every common frame
point represented in the selected extended chart. -/
theorem throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
    period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent hChart

/-- The first derivative field of the tensor-frame transition is locally
`C∞`. -/
theorem throatCovariantTwoTensorTransitionCenteredChart_fderiv_contDiffAt_infty
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor chartAnchor))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

/-- The second derivative field of the tensor-frame transition is locally
`C∞`. -/
theorem throatCovariantTwoTensorTransitionCenteredChart_secondFDeriv_contDiffAt_infty
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (fderiv Real
        (fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor)))
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  exact
    (throatCovariantTwoTensorTransitionCenteredChart_fderiv_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent
        hChart).fderiv_right (by simp)

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
end JanusFormal
