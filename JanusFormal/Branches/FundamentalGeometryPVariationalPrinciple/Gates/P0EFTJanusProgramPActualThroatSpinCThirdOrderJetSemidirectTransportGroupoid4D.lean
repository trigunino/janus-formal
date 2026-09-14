import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportGroupoid4D

/-!
# Groupoid laws for actual throat SpinC third-jet transport

The genuine reverse base-chart derivatives and forward SpinC-fiber
derivatives satisfy the coefficient laws required by the generic third-order
semidirect groupoid criterion.  Hence the actual framed SpinC third-jet
transport has exact identity, composition, and inverse laws.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportGroupoid4D

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
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatSpinCTransitionThirdDerivative4D
open P0EFTJanusProgramPActualThroatSpinCTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0) (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCSecondJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev SpinCTrivializationChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatSpinCSecondOrderJetTrivializationChartAt period hPeriod current

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

local instance spinCEndNormedAddCommGroup : NormedAddCommGroup SpinCEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCEndNormedSpace : NormedSpace Real SpinCEnd :=
  ContinuousLinearMap.toNormedSpace

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

private def spinCSecondJetOfValue
    (value : D9DoubledMatterFiber) : SpinCSecondJet where
  value := value
  firstDerivative := 0
  secondDerivative := 0
  secondDerivative_symmetric first second := by simp

/-! ## Concrete coefficient projections -/

@[simp] private theorem thirdOrderChange_baseFirst_apply
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      source target).baseFirst direction =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor source.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        direction := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).baseFirst direction = _
  rfl

@[simp] private theorem thirdOrderChange_baseSecond_apply
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      source target).baseSecond first second =
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor source.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).baseSecond first second = _
  rfl

@[simp] private theorem thirdOrderChange_baseThird_apply
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
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
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      source target).fiberValue value =
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        source.trivializationIndex target.trivializationIndex target.chartAnchor
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        value := by
  change
    d9PrimitiveSpinCCoordChange period hPeriod choice
        source.trivializationIndex target.trivializationIndex current value = _
  simp only [d9PrimitiveSpinCTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners target.chartAnchor).left_inv
      target.chart_mem]

@[simp] private theorem thirdOrderChange_fiberFirst_apply
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      source target).fiberFirst direction value =
      fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          source.trivializationIndex target.trivializationIndex target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        direction value := by
  rfl

@[simp] private theorem thirdOrderChange_fiberSecond_apply
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      source target).fiberSecond first second value =
      fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            source.trivializationIndex target.trivializationIndex target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second value := by
  rfl

@[simp] private theorem thirdOrderChange_fiberThird_apply
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      source target).fiberThird first second third value =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              source.trivializationIndex target.trivializationIndex target.chartAnchor)))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
        first second third value := by
  rfl

/-! ## Lower-order coefficient laws from the actual J2 groupoid -/

private theorem thirdOrderChange_fiberValue_self
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).fiberValue value = value := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).fiberValue value = value
  have hTransport :=
    throatSpinCSecondOrderJetSemidirectTransportAt_self_apply period hPeriod choice
      presentation (spinCSecondJetOfValue value)
  have hApplied := congrArg (fun jet : SpinCSecondJet => jet.value) hTransport
  simpa only [throatSpinCSecondOrderJetSemidirectTransportAt_value,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    spinCSecondJetOfValue, ContinuousLinearEquiv.coe_apply] using hApplied

private theorem thirdOrderChange_fiberFirst_self
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).fiberFirst direction value = 0 := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).fiberFirst direction value = 0
  have hTransport :=
    throatSpinCSecondOrderJetSemidirectTransportAt_self_apply period hPeriod choice
      presentation (spinCSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : SpinCSecondJet => jet.firstDerivative direction) hTransport
  simpa only [throatSpinCSecondOrderJetSemidirectTransportAt_firstDerivative_apply,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst,
    spinCSecondJetOfValue, zero_apply, map_zero, zero_add] using hApplied

private theorem thirdOrderChange_fiberSecond_self
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).fiberSecond first second value = 0 := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).fiberSecond first second value = 0
  have hTransport :=
    throatSpinCSecondOrderJetSemidirectTransportAt_self_apply period hPeriod choice
      presentation (spinCSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : SpinCSecondJet => jet.secondDerivative first second) hTransport
  simpa only [throatSpinCSecondOrderJetSemidirectTransportAt_secondDerivative_apply,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberSecond,
    spinCSecondJetOfValue, zero_apply, map_zero, zero_add, add_zero] using hApplied

private theorem thirdOrderChange_fiberValue_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberValue value =
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        middle target).fiberValue
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value) := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberValue value =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value)
  have hTransport :=
    throatSpinCSecondOrderJetSemidirectTransportAt_comp_apply period hPeriod choice
      source middle target (spinCSecondJetOfValue value)
  have hApplied := congrArg (fun jet : SpinCSecondJet => jet.value) hTransport
  simpa only [throatSpinCSecondOrderJetSemidirectTransportAt_value,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    spinCSecondJetOfValue, ContinuousLinearEquiv.coe_apply] using hApplied

private theorem thirdOrderChange_fiberFirst_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberFirst direction value =
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst direction) value) +
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst direction
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value) := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberFirst direction value =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst direction) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst direction
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value)
  have hTransport :=
    throatSpinCSecondOrderJetSemidirectTransportAt_comp_apply period hPeriod choice
      source middle target (spinCSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : SpinCSecondJet => jet.firstDerivative direction) hTransport
  simpa only [throatSpinCSecondOrderJetSemidirectTransportAt_value,
    throatSpinCSecondOrderJetSemidirectTransportAt_firstDerivative_apply,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst,
    spinCSecondJetOfValue, zero_apply, map_zero, zero_add,
    ContinuousLinearEquiv.coe_apply] using hApplied

private theorem thirdOrderChange_fiberSecond_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberSecond first second value =
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberSecond
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first)
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) value) +
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseSecond first second) value) +
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst first
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) value) +
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst second
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first) value) +
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberSecond first second
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value) := by
  change
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
        source target).fiberSecond first second value =
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberSecond
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first)
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberValue
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseSecond first second) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst first
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberFirst second
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            source middle).fiberFirst
          ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first) value) +
      (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          middle target).fiberSecond first second
        ((throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
          source middle).fiberValue value)
  have hTransport :=
    throatSpinCSecondOrderJetSemidirectTransportAt_comp_apply period hPeriod choice
      source middle target (spinCSecondJetOfValue value)
  have hApplied := congrArg
    (fun jet : SpinCSecondJet => jet.secondDerivative first second) hTransport
  simpa only [throatSpinCSecondOrderJetSemidirectTransportAt_value,
    throatSpinCSecondOrderJetSemidirectTransportAt_firstDerivative_apply,
    throatSpinCSecondOrderJetSemidirectTransportAt_secondDerivative_apply,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst,
    throatSpinCSecondOrderJetSemidirectChangeAt_baseSecond,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst,
    throatSpinCSecondOrderJetSemidirectChangeAt_fiberSecond,
    spinCSecondJetOfValue, zero_apply, map_zero, zero_add, add_zero,
    ContinuousLinearEquiv.coe_apply] using
      hApplied

/-! ## Reverse-base coefficient laws -/

private theorem thirdOrderChange_baseFirst_self
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
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
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
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
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).baseThird first second third = 0 := by
  rw [thirdOrderChange_baseThird_apply]
  simpa only [throatGaugeBaseChartTransitionThirdDerivativeAt] using
    throatGaugeBaseChartTransitionThirdDerivativeAt_self period hPeriod
      presentation.chartAnchor current presentation.chart_mem
      first second third

private theorem thirdOrderChange_baseFirst_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source target).baseFirst direction =
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source middle).baseFirst
        ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
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
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (first second : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source target).baseSecond first second =
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseSecond
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first)
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) +
        (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseFirst
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
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
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (first second third : ThroatCoverCoordinates) :
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source target).baseThird first second third =
      (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseThird
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first)
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second)
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst third) +
        (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseSecond
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseSecond first second)
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst third) +
        (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseSecond
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseSecond first third)
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst second) +
        (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseSecond
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseSecond second third)
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseFirst first) +
        (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
          source middle).baseFirst
          ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
            middle target).baseThird first second third) := by
  simp only [thirdOrderChange_baseFirst_apply,
    thirdOrderChange_baseSecond_apply, thirdOrderChange_baseThird_apply]
  exact throatGaugeBaseChartTransitionThirdDerivativeAt_cocycle period hPeriod
    target.chartAnchor middle.chartAnchor source.chartAnchor current
      target.chart_mem middle.chart_mem source.chart_mem first second third

/-! ## Reparametrization of one varying SpinC transition -/

private theorem transition_baseChart_eventuallyEq
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex secondIndex firstCenter =ᶠ[nhds
          (extChartAt throatCoverModelWithCorners firstCenter current)]
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  have hFirstTarget :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hInverseContinuous := continuousAt_extChartAt_symm'' hFirstTarget
  have hSecondPreimage :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          (extChartAt throatCoverModelWithCorners secondCenter).source ∈
        nhds (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact extChartAt_source_mem_nhds' hSecond)
  filter_upwards [hSecondPreimage] with coordinate hCoordinate
  simp only [d9PrimitiveSpinCTransitionCenteredChart,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hCoordinate]

private theorem transition_value_baseChart
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (value : D9DoubledMatterFiber) :
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex secondIndex firstCenter
        (extChartAt throatCoverModelWithCorners firstCenter current) value =
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex secondIndex secondCenter
        (extChartAt throatCoverModelWithCorners secondCenter current) value := by
  simp only [d9PrimitiveSpinCTransitionCenteredChart,
    (extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst,
    (extChartAt throatCoverModelWithCorners secondCenter).left_inv hSecond]

private theorem transition_firstDerivative_baseChart
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod secondIndex)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (direction : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)
        direction value =
      fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex secondCenter)
        (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
          direction) value := by
  let inner :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let outer :=
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      firstIndex secondIndex secondCenter
  let point :=
    extChartAt throatCoverModelWithCorners firstCenter current
  have hInner : ContDiffAt Real 3 inner point :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le
        contDiffThree_le_infty
  have hOuter : ContDiffAt Real 3 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
      period hPeriod choice firstIndex secondIndex secondCenter current hIndices
        hSecond).of_le contDiffThree_le_infty
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 3 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod choice
    firstIndex secondIndex firstCenter secondCenter current hFirst hSecond
  have hDerivative := hGerm.fderiv_eq (𝕜 := Real)
  have hChain := fderiv_comp point
    (hOuterAt.differentiableAt (by norm_num))
    (hInner.differentiableAt (by norm_num))
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] SpinCEnd =>
      derivative direction value) (hDerivative.trans hChain)
  simpa only [inner, outer, point, hAt,
    ContinuousLinearMap.comp_apply] using hApplied

private theorem transition_secondDerivative_baseChart
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod secondIndex)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    fderiv Real
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex firstCenter))
        (extChartAt throatCoverModelWithCorners firstCenter current)
        first second value =
      fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex secondIndex secondCenter))
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
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex secondCenter)
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
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      firstIndex secondIndex secondCenter
  let point :=
    extChartAt throatCoverModelWithCorners firstCenter current
  have hInner : ContDiffAt Real 3 inner point :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le
        contDiffThree_le_infty
  have hOuter : ContDiffAt Real 3 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
      period hPeriod choice firstIndex secondIndex secondCenter current hIndices
        hSecond).of_le contDiffThree_le_infty
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 3 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod choice
    firstIndex secondIndex firstCenter secondCenter current hFirst hSecond
  have hSecondDerivative :=
    (hGerm.fderiv (𝕜 := Real)).fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] SpinCEnd =>
      derivative first second value) hSecondDerivative
  have hFormula :=
    P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D.second_fderiv_comp_apply
      inner outer point (hInner.of_le (by norm_num))
        (hOuterAt.of_le (by norm_num)) first second
  have hFormulaApplied := congrArg
    (fun derivative : SpinCEnd => derivative value) hFormula
  exact hApplied.trans (by
    simpa only [inner, outer, point, hAt, add_apply] using hFormulaApplied)

private theorem transition_thirdDerivative_baseChart
    (firstIndex secondIndex : D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hIndices : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod secondIndex)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second third : ThroatCoverCoordinates)
    (value : D9DoubledMatterFiber) :
    fderiv Real
        (fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex secondIndex firstCenter)))
        (extChartAt throatCoverModelWithCorners firstCenter current)
        first second third value =
      fderiv Real
          (fderiv Real
            (fderiv Real
              (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
                firstIndex secondIndex secondCenter)))
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
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex secondIndex secondCenter))
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
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex secondIndex secondCenter))
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
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex secondIndex secondCenter))
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
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex secondCenter)
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
    d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      firstIndex secondIndex secondCenter
  let point :=
    extChartAt throatCoverModelWithCorners firstCenter current
  have hInner : ContDiffAt Real 3 inner point :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le
        contDiffThree_le_infty
  have hOuter : ContDiffAt Real 3 outer
      (extChartAt throatCoverModelWithCorners secondCenter current) :=
    (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
      period hPeriod choice firstIndex secondIndex secondCenter current hIndices
        hSecond).of_le contDiffThree_le_infty
  have hAt : inner point =
      extChartAt throatCoverModelWithCorners secondCenter current := by
    simpa only [inner, point] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hOuterAt : ContDiffAt Real 3 outer (inner point) := by
    simpa only [hAt] using hOuter
  have hGerm := transition_baseChart_eventuallyEq period hPeriod choice
    firstIndex secondIndex firstCenter secondCenter current hFirst hSecond
  have hThirdDerivative :=
    ((hGerm.fderiv (𝕜 := Real)).fderiv (𝕜 := Real)).fderiv_eq
      (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] SpinCEnd =>
      derivative first second third value) hThirdDerivative
  have hFormula := third_fderiv_comp_apply inner outer point hInner hOuterAt
    first second third
  have hFormulaApplied := congrArg
    (fun derivative : SpinCEnd => derivative value) hFormula
  exact hApplied.trans (by
    simpa only [inner, outer, point, hAt, add_apply] using hFormulaApplied)

/-! ## Actual J3 identity and composition -/

/-- Actual SpinC third-jet self-transport fixes every raw jet. -/
@[simp]
theorem throatSpinCThirdOrderJetSemidirectTransportAt_self_apply
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCThirdJet) :
    throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
      presentation presentation jet = jet := by
  change
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation).transport jet = jet
  exact framedThirdOrderJetSemidirectTransport_self_of_coefficients
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      presentation presentation)
    (thirdOrderChange_baseFirst_self period hPeriod choice presentation)
    (thirdOrderChange_baseSecond_self period hPeriod choice presentation)
    (thirdOrderChange_baseThird_self period hPeriod choice presentation)
    (thirdOrderChange_fiberValue_self period hPeriod choice presentation)
    (thirdOrderChange_fiberFirst_self period hPeriod choice presentation)
    (thirdOrderChange_fiberSecond_self period hPeriod choice presentation)
    (fun first second third value => by
      rw [thirdOrderChange_fiberThird_apply]
      have hSelf :=
        throatSpinCTargetTrivializationTransitionThirdDerivativeAt_self
          period hPeriod choice presentation first second third
      have hApplied := congrArg
        (fun derivative : SpinCEnd => derivative value) hSelf
      simpa only [throatSpinCTargetTrivializationTransitionThirdDerivativeAt,
        zero_apply] using hApplied)
    jet

/-- Actual SpinC third-jet transport composes through any intermediate
presentation. -/
theorem throatSpinCThirdOrderJetSemidirectTransportAt_comp_apply
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCThirdJet) :
    throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
        source target jet =
      throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
        middle target
        (throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
          source middle jet) := by
  change
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      source target).transport jet =
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
      middle target).transport
      ((throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
        source middle).transport jet)
  apply framedThirdOrderJetSemidirectTransport_comp_of_coefficients
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice source middle)
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice middle target)
    (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice source target)
  · exact thirdOrderChange_baseFirst_comp period hPeriod choice source middle target
  · exact thirdOrderChange_baseSecond_comp period hPeriod choice source middle target
  · exact thirdOrderChange_baseThird_comp period hPeriod choice source middle target
  · exact thirdOrderChange_fiberValue_comp period hPeriod choice source middle target
  · exact thirdOrderChange_fiberFirst_comp period hPeriod choice source middle target
  · exact thirdOrderChange_fiberSecond_comp period hPeriod choice source middle target
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
      throatSpinCTrivializationBaseChartTransition_thirdDerivative_cocycle_apply
        period hPeriod choice source.trivializationIndex middle.trivializationIndex target.trivializationIndex
        target.chartAnchor target.chartAnchor current
        ⟨source.trivialization_mem, ⟨middle.trivialization_mem, target.trivialization_mem⟩⟩
        target.chart_mem target.chart_mem first second third value
    dsimp only at hRaw
    rw [hBaseFirstSelf, hBaseSecondSelf, hBaseThirdSelf] at hRaw
    simp only [ContinuousLinearMap.id_apply, zero_apply, map_zero,
      add_zero] at hRaw
    rw [transition_thirdDerivative_baseChart period hPeriod choice
      source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current ⟨source.trivialization_mem, middle.trivialization_mem⟩
      target.chart_mem middle.chart_mem first second third value] at hRaw
    rw [transition_secondDerivative_baseChart period hPeriod choice
      source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current ⟨source.trivialization_mem, middle.trivialization_mem⟩
      target.chart_mem middle.chart_mem second third value] at hRaw
    rw [transition_secondDerivative_baseChart period hPeriod choice
      source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current ⟨source.trivialization_mem, middle.trivialization_mem⟩
      target.chart_mem middle.chart_mem first third value] at hRaw
    rw [transition_secondDerivative_baseChart period hPeriod choice
      source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current ⟨source.trivialization_mem, middle.trivialization_mem⟩
      target.chart_mem middle.chart_mem first second value] at hRaw
    rw [transition_firstDerivative_baseChart period hPeriod choice
      source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current ⟨source.trivialization_mem, middle.trivialization_mem⟩
      target.chart_mem middle.chart_mem third value] at hRaw
    rw [transition_firstDerivative_baseChart period hPeriod choice
      source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current ⟨source.trivialization_mem, middle.trivialization_mem⟩
      target.chart_mem middle.chart_mem second value] at hRaw
    rw [transition_firstDerivative_baseChart period hPeriod choice
      source.trivializationIndex middle.trivializationIndex target.chartAnchor
      middle.chartAnchor current ⟨source.trivialization_mem, middle.trivialization_mem⟩
      target.chart_mem middle.chart_mem first value] at hRaw
    rw [transition_value_baseChart period hPeriod choice source.trivializationIndex
      middle.trivializationIndex target.chartAnchor middle.chartAnchor current
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
def throatSpinCThirdOrderJetSemidirectTransportLinearMapAt
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    SpinCThirdJet →ₗ[Real] SpinCThirdJet :=
  (throatSpinCThirdOrderJetSemidirectChangeAt period hPeriod choice
    source target).toLinearMap

@[simp]
theorem throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_apply
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCThirdJet) :
    throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
        source target jet =
      throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
        source target jet :=
  rfl

/-- Self-transport is the identity linear map. -/
@[simp]
theorem throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_self
    {current : EffectiveThroat period hPeriod}
    (presentation : SpinCTrivializationChartAt period hPeriod current) :
    throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
        presentation presentation =
      LinearMap.id := by
  apply LinearMap.ext
  intro jet
  exact throatSpinCThirdOrderJetSemidirectTransportAt_self_apply period
    hPeriod choice presentation jet

/-- Actual third-jet transport composes as linear maps. -/
theorem throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_comp
    {current : EffectiveThroat period hPeriod}
    (source middle target : SpinCTrivializationChartAt period hPeriod current) :
    throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
        source target =
      (throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
        middle target).comp
        (throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
          source middle) := by
  apply LinearMap.ext
  intro jet
  exact throatSpinCThirdOrderJetSemidirectTransportAt_comp_apply period
    hPeriod choice source middle target jet

/-- Reverse actual transport is a left inverse. -/
theorem throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_inverse_comp
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
        target source).comp
        (throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
          source target) =
      LinearMap.id := by
  rw [← throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_comp
    period hPeriod choice source target source]
  exact throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_self period
    hPeriod choice source

/-- Reverse actual transport is a right inverse. -/
theorem throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_comp_inverse
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
        source target).comp
        (throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
          target source) =
      LinearMap.id := by
  exact throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_inverse_comp
    period hPeriod choice target source

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportGroupoid4D
end JanusFormal
