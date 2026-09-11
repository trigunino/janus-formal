import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D

/-!
# Third-order cocycle for the actual throat metric frame transition

The existing local metric frame/base transition germ is differentiated three
times.  The generic third-order semidirect Leibniz rule gives the complete
fifteen-term composition formula for the covariant rank-two frame transition.

This is coefficient-level third-order descent data.  No metric third-jet
groupoid, coordinate-change atlas, or bundle descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdOrderCocycle4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1200000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdDerivative4D
open P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.tensorModelNormedSpace

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
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

private abbrev TensorTransitionThirdDerivative :=
  ThroatCoverCoordinates →L[Real] TensorTransitionSecondDerivative

local instance tensorTransitionThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorTransitionThirdDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorTransitionThirdDerivativeNormedSpace :
    NormedSpace Real TensorTransitionThirdDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Actual third-order frame/base cocycle -/

/-- On a common triple overlap, the third derivative of the actual varying
tensor transition obeys the complete fifteen-term composition formula. -/
theorem throatMetricFrameBaseChartTransition_thirdDerivative_cocycle_apply
    (firstAnchor secondAnchor thirdAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) secondAnchor).baseSet ∩
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) thirdAnchor).baseSet))
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second third : ThroatCoverCoordinates)
    (tensor : FramedCovariantTwoTensor ThroatCoverCoordinates) :
    let baseTransition :=
      throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
    let firstTransition :=
      throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor firstCenter
    let secondTransition :=
      throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        secondAnchor thirdAnchor secondCenter
    let directTransition :=
      throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor thirdAnchor firstCenter
    let firstCoordinate :=
      extChartAt throatCoverModelWithCorners firstCenter current
    let secondCoordinate :=
      extChartAt throatCoverModelWithCorners secondCenter current
    fderiv Real (fderiv Real (fderiv Real directTransition))
        firstCoordinate first second third tensor =
      secondTransition secondCoordinate
          (fderiv Real (fderiv Real (fderiv Real firstTransition))
            firstCoordinate first second third tensor) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate second third tensor) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate first third tensor) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate first second tensor) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real firstTransition firstCoordinate third tensor) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first second)
          (fderiv Real firstTransition firstCoordinate third tensor) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real firstTransition firstCoordinate second tensor) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first third)
          (fderiv Real firstTransition firstCoordinate second tensor) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real firstTransition firstCoordinate first tensor) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate second third)
          (fderiv Real firstTransition firstCoordinate first tensor) +
        fderiv Real (fderiv Real (fderiv Real secondTransition))
          secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real baseTransition firstCoordinate third)
          (firstTransition firstCoordinate tensor) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first second)
          (fderiv Real baseTransition firstCoordinate third)
          (firstTransition firstCoordinate tensor) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first third)
          (fderiv Real baseTransition firstCoordinate second)
          (firstTransition firstCoordinate tensor) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate second third)
          (fderiv Real baseTransition firstCoordinate first)
          (firstTransition firstCoordinate tensor) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real (fderiv Real baseTransition))
            firstCoordinate first second third)
          (firstTransition firstCoordinate tensor) := by
  dsimp only
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstTransition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor firstCenter
  let secondTransition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      secondAnchor thirdAnchor secondCenter
  let directTransition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      firstAnchor thirdAnchor firstCenter
  let firstCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter current
  let secondCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter current
  have hBase : ContDiffAt Real 3 baseTransition firstCoordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hFirstTransition : ContDiffAt Real 3 firstTransition firstCoordinate :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod firstAnchor secondAnchor firstCenter current
        ⟨hCurrent.1, hCurrent.2.1⟩ hFirst).of_le (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hSecondTransition :
      ContDiffAt Real 3 secondTransition secondCoordinate :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod secondAnchor thirdAnchor secondCenter current
        hCurrent.2 hSecond).of_le (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hAt : baseTransition firstCoordinate = secondCoordinate := by
    simpa only [baseTransition, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hSecondAt : ContDiffAt Real 3 secondTransition
      (baseTransition firstCoordinate) := by
    simpa only [hAt] using hSecondTransition
  have hGerm : directTransition =ᶠ[nhds firstCoordinate]
      fun coordinate =>
        (secondTransition (baseTransition coordinate)).comp
          (firstTransition coordinate) := by
    have hCombined := throatMetricFrameBaseChartTransition_cocycle_eventuallyEq
      period hPeriod firstAnchor secondAnchor thirdAnchor firstCenter
        secondCenter secondCenter current hCurrent hFirst hSecond
    exact hCombined.fun_comp Prod.snd
  have hFirstDerivativeGerm := hGerm.fderiv (𝕜 := Real)
  have hSecondDerivativeGerm := hFirstDerivativeGerm.fderiv (𝕜 := Real)
  have hThirdDerivativeGerm :=
    hSecondDerivativeGerm.fderiv_eq (𝕜 := Real)
  have hGermApplied := congrArg
    (fun derivative : TensorTransitionThirdDerivative =>
      derivative first second third tensor)
    hThirdDerivativeGerm
  have hFormula := third_fderiv_semidirect_comp_apply
    baseTransition secondTransition firstTransition firstCoordinate
      first second third tensor hBase hSecondAt hFirstTransition
  rw [hGermApplied]
  rw [hAt] at hFormula
  simpa only [baseTransition, firstTransition, secondTransition,
    directTransition, firstCoordinate, secondCoordinate] using hFormula

end
end P0EFTJanusProgramPActualThroatMetricFrameTransitionThirdOrderCocycle4D
end JanusFormal
