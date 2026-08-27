import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D

/-!
# Triple SpinC cocycle for arbitrary trivialization/base-chart pairs

The transition between two arbitrary SpinC trivialization/base-chart pairs is
composed on a triple overlap.  This gate records the combined germ, value,
Jacobian, and full five-term Hessian cocycles.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderCocycle4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPActualThroatSpinCZeroOrderTransitionGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private theorem fderiv_clm_apply_const_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (field : X → Y →L[Real] Z) (point direction : X) (value : Y)
    (hField : DifferentiableAt Real field point) :
    fderiv Real (fun current ↦ field current value) point direction =
      fderiv Real field point direction value := by
  have hDerivative :=
    fderiv_clm_apply hField (differentiableAt_const (c := value))
  have hApplied := congrArg
    (fun derivative : X →L[Real] Z ↦ derivative direction) hDerivative
  simpa using hApplied

private theorem second_fderiv_clm_apply_const_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (field : X → Y →L[Real] Z) (point first second : X) (value : Y)
    (hField : ContDiffAt Real 2 field point) :
    fderiv Real (fderiv Real (fun current ↦ field current value))
        point first second =
      fderiv Real (fderiv Real field) point first second value := by
  have hFieldDerivative : DifferentiableAt Real (fderiv Real field) point :=
    (hField.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAppliedDerivative : DifferentiableAt Real
      (fun current ↦ fderiv Real field current second) point :=
    hFieldDerivative.clm_apply (differentiableAt_const (c := second))
  have hEvaluation : ContDiffAt Real 2
      (fun current ↦ field current value) point :=
    hField.clm_apply contDiffAt_const
  have hEvaluationDerivative : DifferentiableAt Real
      (fderiv Real (fun current ↦ field current value)) point :=
    (hEvaluation.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hFieldEventually : ∀ᶠ current in nhds point,
      DifferentiableAt Real field current := by
    filter_upwards [hField.eventually (by norm_num)] with current hCurrent
    exact hCurrent.differentiableAt (by norm_num)
  have hFirstFormula :
      (fun current ↦
        fderiv Real (fun base ↦ field base value) current second) =ᶠ[nhds point]
      (fun current ↦ fderiv Real field current second value) := by
    filter_upwards [hFieldEventually] with current hCurrent
    exact fderiv_clm_apply_const_apply field current second value hCurrent
  have hLeft := fderiv_clm_apply_const_apply
    (field := fderiv Real (fun current ↦ field current value))
    point first second hEvaluationDerivative
  have hRightOuter := fderiv_clm_apply_const_apply
    (field := fun current ↦ fderiv Real field current second)
    point first value hAppliedDerivative
  have hRightInner := fderiv_clm_apply_const_apply
    (field := fderiv Real field) point first second hFieldDerivative
  calc
    fderiv Real (fderiv Real (fun current ↦ field current value))
        point first second =
      fderiv Real
        (fun current ↦
          fderiv Real (fun base ↦ field base value) current second)
        point first := hLeft.symm
    _ = fderiv Real
        (fun current ↦ fderiv Real field current second value)
        point first := congrArg
          (fun derivative : X →L[Real] Z ↦ derivative first)
          hFirstFormula.fderiv_eq
    _ = fderiv Real (fun current ↦ fderiv Real field current second)
        point first value := hRightOuter
    _ = fderiv Real (fderiv Real field) point first second value := by
      exact congrArg (fun derivative : Y →L[Real] Z ↦ derivative value)
        hRightInner

private theorem second_fderiv_clm_comp_apply_raw
    {X Y Z W : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (outer : X → Z →L[Real] W) (inner : X → Y →L[Real] Z)
    (point first second : X) (value : Y)
    (hOuter : ContDiffAt Real 2 outer point)
    (hInner : ContDiffAt Real 2 inner point) :
    fderiv Real
        (fderiv Real (fun current ↦ (outer current).comp (inner current)))
        point first second value =
      outer point
          (fderiv Real (fderiv Real inner) point first second value) +
        fderiv Real outer point first
          (fderiv Real inner point second value) +
        fderiv Real outer point second
          (fderiv Real inner point first value) +
        fderiv Real (fderiv Real outer) point first second
          (inner point value) := by
  let evaluatedInner := fun current ↦ inner current value
  have hEvaluatedInner : ContDiffAt Real 2 evaluatedInner point := by
    exact hInner.clm_apply contDiffAt_const
  have hProduct := second_fderiv_clm_apply_apply outer evaluatedInner
    point first second hOuter hEvaluatedInner
  have hComposition : ContDiffAt Real 2
      (fun current ↦ (outer current).comp (inner current)) point :=
    hOuter.clm_comp hInner
  have hLeft := second_fderiv_clm_apply_const_apply
    (field := fun current ↦ (outer current).comp (inner current))
    point first second value hComposition
  have hInnerFirst := fderiv_clm_apply_const_apply inner point second value
    (hInner.differentiableAt (by norm_num))
  have hInnerSecond := fderiv_clm_apply_const_apply inner point first value
    (hInner.differentiableAt (by norm_num))
  have hInnerHessian := second_fderiv_clm_apply_const_apply inner
    point first second value hInner
  have hOuterDerivative : DifferentiableAt Real (fderiv Real outer) point :=
    (hOuter.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hOuterHessian := fderiv_clm_apply_const_apply
    (field := fderiv Real outer) point first second hOuterDerivative
  rw [← hLeft]
  simpa only [evaluatedInner, hInnerFirst, hInnerSecond, hInnerHessian,
    hOuterHessian, ContinuousLinearMap.comp_apply] using hProduct

private theorem second_fderiv_clm_comp_apply
    {X Y Z W : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    [NormedAddCommGroup W] [NormedSpace Real W]
    (outer : X → Z →L[Real] W) (inner : X → Y →L[Real] Z)
    (point first second : X) (value : Y)
    (hOuter : ContDiffAt Real 2 outer point)
    (hInner : ContDiffAt Real 2 inner point) :
    fderiv Real
        (fun current ↦
          fderiv Real (fun base ↦ (outer base).comp (inner base))
            current second)
        point first value =
      outer point
          (fderiv Real (fun current ↦ fderiv Real inner current second)
            point first value) +
        fderiv Real outer point first
          (fderiv Real inner point second value) +
        fderiv Real outer point second
          (fderiv Real inner point first value) +
        fderiv Real (fun current ↦ fderiv Real outer current second)
          point first (inner point value) := by
  let composition := fun current ↦ (outer current).comp (inner current)
  have hComposition : ContDiffAt Real 2 composition point :=
    hOuter.clm_comp hInner
  have hCompositionDerivative : DifferentiableAt Real
      (fderiv Real composition) point :=
    (hComposition.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hInnerDerivative : DifferentiableAt Real (fderiv Real inner) point :=
    (hInner.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hOuterDerivative : DifferentiableAt Real (fderiv Real outer) point :=
    (hOuter.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hCompositionBridge := fderiv_clm_apply_const_apply
    (field := fderiv Real composition) point first second
      hCompositionDerivative
  have hInnerBridge := fderiv_clm_apply_const_apply
    (field := fderiv Real inner) point first second hInnerDerivative
  have hOuterBridge := fderiv_clm_apply_const_apply
    (field := fderiv Real outer) point first second hOuterDerivative
  have hRaw := second_fderiv_clm_comp_apply_raw outer inner point first
    second value hOuter hInner
  rw [hCompositionBridge, hRaw, ← hInnerBridge, ← hOuterBridge]

private theorem second_fderiv_comp_nested_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inner : E → F) (outer : F → G) (point : E)
    (hInner : ContDiffAt Real 2 inner point)
    (hOuter : ContDiffAt Real 2 outer (inner point))
    (first second : E) :
    fderiv Real
        (fun current ↦ fderiv Real (outer ∘ inner) current second)
        point first =
      fderiv Real
          (fun current ↦
            fderiv Real outer current (fderiv Real inner point second))
          (inner point) (fderiv Real inner point first) +
        fderiv Real outer (inner point)
          (fderiv Real
            (fun current ↦ fderiv Real inner current second) point first) := by
  have hComposition : ContDiffAt Real 2 (outer ∘ inner) point :=
    hOuter.comp point hInner
  have hCompositionDerivative : DifferentiableAt Real
      (fderiv Real (outer ∘ inner)) point :=
    (hComposition.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hInnerDerivative : DifferentiableAt Real (fderiv Real inner) point :=
    (hInner.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hOuterDerivative : DifferentiableAt Real (fderiv Real outer)
      (inner point) :=
    (hOuter.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hCompositionBridge := fderiv_clm_apply_const_apply
    (field := fderiv Real (outer ∘ inner)) point first second
      hCompositionDerivative
  have hInnerBridge := fderiv_clm_apply_const_apply
    (field := fderiv Real inner) point first second hInnerDerivative
  have hOuterBridge := fderiv_clm_apply_const_apply
    (field := fderiv Real outer) (inner point)
      (fderiv Real inner point first) (fderiv Real inner point second)
      hOuterDerivative
  have hRaw := second_fderiv_comp_apply inner outer point hInner hOuter
    first second
  rw [hCompositionBridge, hRaw, ← hOuterBridge, ← hInnerBridge]
/-! ## Combined transition germ -/

/-- On a common triple overlap, the direct base/frame transition is locally
the semidirect composition of the two successive transitions. -/
theorem throatSpinCTrivializationBaseChartTransition_cocycle_eventuallyEq
    (choice : NormalRootChoice)
    (firstIndex secondIndex thirdIndex :
      D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        (d9PrimitiveSpinCBaseSet period hPeriod secondIndex ∩
          d9PrimitiveSpinCBaseSet period hPeriod thirdIndex))
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (fun coordinate =>
      (throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
          coordinate,
        d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex thirdIndex firstCenter coordinate)) =ᶠ[nhds
            (extChartAt throatCoverModelWithCorners firstCenter current)]
      (fun coordinate =>
        (throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter coordinate),
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            secondIndex thirdIndex secondCenter
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter coordinate)).comp
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex secondIndex firstCenter coordinate))) := by
  have hBase := throatGaugeBaseChartTransition_cocycle_eventuallyEq
    period hPeriod firstCenter secondCenter thirdCenter current hFirst hSecond
  have hChartInverse : ContinuousAt
      (extChartAt throatCoverModelWithCorners firstCenter).symm
      (extChartAt throatCoverModelWithCorners firstCenter current) :=
    continuousAt_extChartAt_symm' hFirst
  let tripleOverlap :=
    d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
      (d9PrimitiveSpinCBaseSet period hPeriod secondIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod thirdIndex)
  have hTripleOpen : IsOpen tripleOverlap := by
    exact (d9PrimitiveSpinCBaseSet_isOpen period hPeriod firstIndex).inter
      ((d9PrimitiveSpinCBaseSet_isOpen period hPeriod secondIndex).inter
        (d9PrimitiveSpinCBaseSet_isOpen period hPeriod thirdIndex))
  have hTripleEventually :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          tripleOverlap ∈
        nhds (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hChartInverse.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact hTripleOpen.mem_nhds hCurrent)
  have hSecondEventually :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          (extChartAt throatCoverModelWithCorners secondCenter).source ∈
        nhds (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hChartInverse.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact extChartAt_source_mem_nhds' hSecond)
  filter_upwards [hBase, hTripleEventually, hSecondEventually] with coordinate
      hCoordinateBase hCoordinateIndices hCoordinateSecond
  apply Prod.ext hCoordinateBase
  simp only [d9PrimitiveSpinCTransitionCenteredChart,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv
    hCoordinateSecond]
  exact (d9PrimitiveSpinCCoordChange_comp period hPeriod choice firstIndex
    secondIndex thirdIndex
    ((extChartAt throatCoverModelWithCorners firstCenter).symm coordinate)
    ⟨⟨hCoordinateIndices.1, hCoordinateIndices.2.1⟩,
      hCoordinateIndices.2.2⟩).symm

/-! ## Value, Jacobian and Hessian cocycles -/

/-- Value of the combined transition at the common point. -/
theorem throatSpinCTrivializationBaseChartTransition_value_cocycle
    (choice : NormalRootChoice)
    (firstIndex secondIndex thirdIndex :
      D9PrimitiveSpinCIndex period hPeriod)
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod firstIndex ∩
        (d9PrimitiveSpinCBaseSet period hPeriod secondIndex ∩
          d9PrimitiveSpinCBaseSet period hPeriod thirdIndex))
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
        (extChartAt throatCoverModelWithCorners firstCenter current),
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        firstIndex thirdIndex firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current)) =
      (throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
            (extChartAt throatCoverModelWithCorners firstCenter current)),
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          secondIndex thirdIndex secondCenter
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
              (extChartAt throatCoverModelWithCorners firstCenter current))).comp
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex firstCenter
              (extChartAt throatCoverModelWithCorners firstCenter current))) := by
  exact (throatSpinCTrivializationBaseChartTransition_cocycle_eventuallyEq period hPeriod
    choice firstIndex secondIndex thirdIndex firstCenter secondCenter thirdCenter
      current hCurrent hFirst hSecond).eq_of_nhds

/-- Jacobian cocycle of the varying frame transition, including the pullback
through the first base-chart transition. -/
theorem throatSpinCTrivializationBaseChartTransition_firstDerivative_cocycle
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
    (direction : ThroatCoverCoordinates) :
    fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex thirdIndex firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current) direction =
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          secondIndex thirdIndex secondCenter
          (extChartAt throatCoverModelWithCorners secondCenter current)).comp
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) direction) +
      (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            secondIndex thirdIndex secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)
            direction)).comp
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current)) := by
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
  have hBase : ContDiffAt Real 2 baseTransition firstCoordinate := by
    simpa only [baseTransition, firstCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod firstCenter
        secondCenter current hFirst hSecond
  have hFirstTransition : ContDiffAt Real 2 firstTransition firstCoordinate := by
    simpa only [firstTransition, firstCoordinate] using
      (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
        period hPeriod choice firstIndex secondIndex firstCenter current
          ⟨hCurrent.1, hCurrent.2.1⟩ hFirst).of_le (by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  have hSecondTransition : ContDiffAt Real 2 secondTransition secondCoordinate := by
    simpa only [secondTransition, secondCoordinate] using
      (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
        period hPeriod choice secondIndex thirdIndex secondCenter current
          hCurrent.2 hSecond).of_le (by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  have hAt : baseTransition firstCoordinate = secondCoordinate := by
    simpa only [baseTransition, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hSecondAt : ContDiffAt Real 2 secondTransition
      (baseTransition firstCoordinate) := by
    simpa only [hAt] using hSecondTransition
  have hPulledTransition : ContDiffAt Real 2
      (secondTransition ∘ baseTransition) firstCoordinate :=
    hSecondAt.comp firstCoordinate hBase
  have hGerm : directTransition =ᶠ[nhds firstCoordinate]
      fun coordinate =>
        (secondTransition (baseTransition coordinate)).comp
          (firstTransition coordinate) := by
    have hCombined := throatSpinCTrivializationBaseChartTransition_cocycle_eventuallyEq
      period hPeriod choice firstIndex secondIndex thirdIndex firstCenter
        secondCenter secondCenter current hCurrent hFirst hSecond
    exact hCombined.fun_comp Prod.snd
  have hProduct := fderiv_clm_comp
    (hPulledTransition.differentiableAt (by norm_num))
    (hFirstTransition.differentiableAt (by norm_num))
  have hProductApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        (D9DoubledMatterFiber →L[Real]
          D9DoubledMatterFiber) ↦ derivative direction)
    hProduct
  have hPulledDerivative :
      fderiv Real (secondTransition ∘ baseTransition) firstCoordinate =
        (fderiv Real secondTransition secondCoordinate).comp
          (fderiv Real baseTransition firstCoordinate) := by
    have hChain := fderiv_comp firstCoordinate
      (by simpa only [hAt] using
        hSecondTransition.differentiableAt (by norm_num))
      (hBase.differentiableAt (by norm_num))
    simpa only [hAt] using hChain
  rw [hGerm.fderiv_eq]
  rw [hPulledDerivative] at hProductApplied
  simpa only [baseTransition, firstTransition, secondTransition,
    directTransition, firstCoordinate, secondCoordinate, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply, hAt] using
      hProductApplied

/-- Full five-term Hessian cocycle for the varying frame transition. -/
theorem throatSpinCTrivializationBaseChartTransition_secondDerivative_cocycle_apply
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
    (first second : ThroatCoverCoordinates)
    (tensor : D9DoubledMatterFiber) :
    fderiv Real
        (fun coordinate =>
          fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              firstIndex thirdIndex firstCenter) coordinate second)
        (extChartAt throatCoverModelWithCorners firstCenter current)
          first tensor =
      d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          secondIndex thirdIndex secondCenter
          (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (fun coordinate =>
            fderiv Real
              (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
                firstIndex secondIndex firstCenter) coordinate second)
          (extChartAt throatCoverModelWithCorners firstCenter current)
            first tensor) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            secondIndex thirdIndex secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
            second tensor) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            secondIndex thirdIndex secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) second)
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            firstIndex secondIndex firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
            first tensor) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
                secondIndex thirdIndex secondCenter) coordinate
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  firstCenter secondCenter)
                (extChartAt throatCoverModelWithCorners firstCenter current)
                  second))
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current) tensor) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            secondIndex thirdIndex secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fun coordinate =>
              fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  firstCenter secondCenter) coordinate second)
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first)
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          firstIndex secondIndex firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current) tensor) := by
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
  have hBase : ContDiffAt Real 2 baseTransition firstCoordinate := by
    simpa only [baseTransition, firstCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod firstCenter
        secondCenter current hFirst hSecond
  have hFirstTransition : ContDiffAt Real 2 firstTransition firstCoordinate := by
    simpa only [firstTransition, firstCoordinate] using
      (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
        period hPeriod choice firstIndex secondIndex firstCenter current
          ⟨hCurrent.1, hCurrent.2.1⟩ hFirst).of_le (by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  have hSecondTransition : ContDiffAt Real 2 secondTransition secondCoordinate := by
    simpa only [secondTransition, secondCoordinate] using
      (d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
        period hPeriod choice secondIndex thirdIndex secondCenter current
          hCurrent.2 hSecond).of_le (by
            change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
  have hAt : baseTransition firstCoordinate = secondCoordinate := by
    simpa only [baseTransition, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod firstCenter
        secondCenter current hFirst
  have hSecondAt : ContDiffAt Real 2 secondTransition
      (baseTransition firstCoordinate) := by
    simpa only [hAt] using hSecondTransition
  have hPulledTransition : ContDiffAt Real 2
      (secondTransition ∘ baseTransition) firstCoordinate :=
    hSecondAt.comp firstCoordinate hBase
  have hGerm : directTransition =ᶠ[nhds firstCoordinate]
      fun coordinate =>
        (secondTransition (baseTransition coordinate)).comp
          (firstTransition coordinate) := by
    have hCombined := throatSpinCTrivializationBaseChartTransition_cocycle_eventuallyEq
      period hPeriod choice firstIndex secondIndex thirdIndex firstCenter
        secondCenter secondCenter current hCurrent hFirst hSecond
    exact hCombined.fun_comp Prod.snd
  have hProduct := second_fderiv_clm_comp_apply
    (secondTransition ∘ baseTransition) firstTransition firstCoordinate
      first second tensor hPulledTransition hFirstTransition
  simp only [Function.comp_apply] at hProduct
  have hPulledFirst :
      fderiv Real (secondTransition ∘ baseTransition) firstCoordinate =
        (fderiv Real secondTransition secondCoordinate).comp
          (fderiv Real baseTransition firstCoordinate) := by
    have hChain := fderiv_comp firstCoordinate
      (by simpa only [hAt] using
        hSecondTransition.differentiableAt (by norm_num))
      (hBase.differentiableAt (by norm_num))
    simpa only [hAt] using hChain
  have hPulledSecond := second_fderiv_comp_nested_apply baseTransition
    secondTransition firstCoordinate hBase hSecondAt first second
  have hFirstDerivativeGerm :
      (fun coordinate => fderiv Real directTransition coordinate second) =ᶠ[
          nhds firstCoordinate]
        (fun coordinate =>
          fderiv Real
            (fun point =>
              (secondTransition (baseTransition point)).comp
                (firstTransition point)) coordinate second) :=
    hGerm.fderiv.fun_comp (fun derivative => derivative second)
  have hGermSecond :
      fderiv Real
          (fun coordinate => fderiv Real directTransition coordinate second)
          firstCoordinate =
        fderiv Real
          (fun coordinate =>
            fderiv Real
              (fun point =>
                (secondTransition (baseTransition point)).comp
                  (firstTransition point)) coordinate second)
          firstCoordinate :=
    hFirstDerivativeGerm.fderiv_eq
  have hGermSecondApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        (D9DoubledMatterFiber →L[Real]
          D9DoubledMatterFiber) ↦ derivative first tensor)
    hGermSecond
  rw [hGermSecondApplied, hProduct, hPulledFirst, hPulledSecond, hAt]
  simp only [baseTransition, firstTransition, secondTransition,
    firstCoordinate, secondCoordinate, add_apply,
    ContinuousLinearMap.comp_apply]
  abel

end
end P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderCocycle4D
end JanusFormal
