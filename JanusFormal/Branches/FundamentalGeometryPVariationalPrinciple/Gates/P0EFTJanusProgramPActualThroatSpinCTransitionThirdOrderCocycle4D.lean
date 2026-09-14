import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D

/-!
# Third-order cocycle for the actual throat SpinC transition

The existing local SpinC trivialization/base-chart transition germ is
differentiated three times.  The generic third-order semidirect Leibniz rule
gives the complete fifteen-term composition formula for the SpinC transition.

This is coefficient-level third-order descent data.  No SpinC third-jet
groupoid, coordinate-change atlas, or bundle descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCTransitionThirdOrderCocycle4D

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
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D
open P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

local instance spinCEndNormedAddCommGroup :
    NormedAddCommGroup SpinCEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCEndNormedSpace : NormedSpace Real SpinCEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCEnd

local instance spinCTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionFirstDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCTransitionFirstDerivative

local instance spinCTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionSecondDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionThirdDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCTransitionSecondDerivative

local instance spinCTransitionThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionThirdDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionThirdDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionThirdDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Actual third-order SpinC/base cocycle -/

/-- On a common triple overlap, the third derivative of the actual varying
SpinC transition obeys the complete fifteen-term composition formula. -/
theorem throatSpinCTrivializationBaseChartTransition_thirdDerivative_cocycle_apply
    (choice : NormalRootChoice)
    (firstIndex secondIndex thirdIndex :
      D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        (d9PrimitiveSpinCBaseSet period hPeriod secondIndex ∩
          d9PrimitiveSpinCBaseSet period hPeriod thirdIndex))
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second third : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    let baseTransition :=
      throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
    let firstTransition :=
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex secondIndex firstCenter
    let secondTransition :=
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        secondIndex thirdIndex secondCenter
    let directTransition :=
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex thirdIndex firstCenter
    let firstCoordinate :=
      extChartAt throatCoverModelWithCorners firstCenter current
    let secondCoordinate :=
      extChartAt throatCoverModelWithCorners secondCenter current
    fderiv Real (fderiv Real (fderiv Real directTransition))
        firstCoordinate first second third value =
      secondTransition secondCoordinate
          (fderiv Real (fderiv Real (fderiv Real firstTransition))
            firstCoordinate first second third value) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate second third value) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate first third value) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate first second value) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real firstTransition firstCoordinate third value) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first second)
          (fderiv Real firstTransition firstCoordinate third value) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real firstTransition firstCoordinate second value) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first third)
          (fderiv Real firstTransition firstCoordinate second value) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real firstTransition firstCoordinate first value) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate second third)
          (fderiv Real firstTransition firstCoordinate first value) +
        fderiv Real (fderiv Real (fderiv Real secondTransition))
          secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real baseTransition firstCoordinate third)
          (firstTransition firstCoordinate value) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first second)
          (fderiv Real baseTransition firstCoordinate third)
          (firstTransition firstCoordinate value) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first third)
          (fderiv Real baseTransition firstCoordinate second)
          (firstTransition firstCoordinate value) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate second third)
          (fderiv Real baseTransition firstCoordinate first)
          (firstTransition firstCoordinate value) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real (fderiv Real baseTransition))
            firstCoordinate first second third)
          (firstTransition firstCoordinate value) := by
  dsimp only
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstTransition :=
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      firstIndex secondIndex firstCenter
  let secondTransition :=
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      secondIndex thirdIndex secondCenter
  let directTransition :=
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      firstIndex thirdIndex firstCenter
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
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
      period hPeriod choice firstIndex secondIndex firstCenter current
        ⟨hCurrent.1, hCurrent.2.1⟩ hFirst).of_le (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hSecondTransition :
      ContDiffAt Real 3 secondTransition secondCoordinate :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
      period hPeriod choice secondIndex thirdIndex secondCenter current
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
    have hCombined :=
      throatSpinCTrivializationBaseChartTransition_cocycle_eventuallyEq
        period hPeriod choice firstIndex secondIndex thirdIndex firstCenter
          secondCenter secondCenter current hCurrent hFirst hSecond
    exact hCombined.fun_comp Prod.snd
  have hFirstDerivativeGerm := hGerm.fderiv (𝕜 := Real)
  have hSecondDerivativeGerm := hFirstDerivativeGerm.fderiv (𝕜 := Real)
  have hThirdDerivativeGerm :=
    hSecondDerivativeGerm.fderiv_eq (𝕜 := Real)
  have hGermApplied := congrArg
    (fun derivative : SpinCTransitionThirdDerivative =>
      derivative first second third value)
    hThirdDerivativeGerm
  have hFormula := third_fderiv_semidirect_comp_apply
    baseTransition secondTransition firstTransition firstCoordinate
      first second third value hBase hSecondAt hFirstTransition
  rw [hGermApplied]
  rw [hAt] at hFormula
  simpa only [baseTransition, firstTransition, secondTransition,
    directTransition, firstCoordinate, secondCoordinate] using hFormula

end
end P0EFTJanusProgramPActualThroatSpinCTransitionThirdOrderCocycle4D
end JanusFormal
