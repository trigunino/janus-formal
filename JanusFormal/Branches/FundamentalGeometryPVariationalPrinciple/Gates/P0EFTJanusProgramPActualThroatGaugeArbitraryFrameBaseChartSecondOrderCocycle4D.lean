import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderJetOverlap4D

/-!
# Triple cocycle for arbitrary throat frame/base-chart pairs

The transition between two arbitrary tangent-frame/base-chart pairs is
composed on a triple overlap.  Besides the combined representative germ, this
gate records the exact Jacobian law and the full five-term Hessian law for the
varying covector transition.

This is local second-order descent data, not yet a global jet-bundle section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderCocycle4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeFrameTransitionInBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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
theorem throatGaugeFrameBaseChartTransition_cocycle_eventuallyEq
    (firstAnchor secondAnchor thirdAnchor firstCenter secondCenter thirdCenter
      current : EffectiveThroat period hPeriod)
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
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (fun coordinate =>
      (throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
          coordinate,
        throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor thirdAnchor firstCenter coordinate)) =ᶠ[nhds
            (extChartAt throatCoverModelWithCorners firstCenter current)]
      (fun coordinate =>
        (throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter coordinate),
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            secondAnchor thirdAnchor secondCenter
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter coordinate)).comp
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              firstAnchor secondAnchor firstCenter coordinate))) := by
  have hBase := throatGaugeBaseChartTransition_cocycle_eventuallyEq
    period hPeriod firstCenter secondCenter thirdCenter current hFirst hSecond
  have hChartInverse : ContinuousAt
      (extChartAt throatCoverModelWithCorners firstCenter).symm
      (extChartAt throatCoverModelWithCorners firstCenter current) :=
    continuousAt_extChartAt_symm' hFirst
  let tripleOverlap :=
    (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) thirdAnchor).baseSet)
  have hTripleOpen : IsOpen tripleOverlap := by
    exact (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor).open_baseSet.inter
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).open_baseSet.inter
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) thirdAnchor).open_baseSet)
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
      hCoordinateBase hCoordinateFrames hCoordinateSecond
  apply Prod.ext hCoordinateBase
  apply ContinuousLinearMap.ext
  intro covector
  have hCocycle := throatGaugeCovectorTrivializationTransitionAt_cocycle
    period hPeriod firstAnchor secondAnchor thirdAnchor
      ((extChartAt throatCoverModelWithCorners firstCenter).symm coordinate)
      hCoordinateFrames
  simp only [throatGaugeCovectorTransitionCenteredChart,
    throatGaugeBaseChartTransition, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  simp only [Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv
    hCoordinateSecond, ← hCocycle]
  rfl

/-! ## Value, Jacobian and Hessian cocycles -/

/-- Value of the combined transition at the common point. -/
theorem throatGaugeFrameBaseChartTransition_value_cocycle
    (firstAnchor secondAnchor thirdAnchor firstCenter secondCenter thirdCenter
      current : EffectiveThroat period hPeriod)
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
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
        (extChartAt throatCoverModelWithCorners firstCenter current),
      throatGaugeCovectorTransitionCenteredChart period hPeriod
        firstAnchor thirdAnchor firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current)) =
      (throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
            (extChartAt throatCoverModelWithCorners firstCenter current)),
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor thirdAnchor secondCenter
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
              (extChartAt throatCoverModelWithCorners firstCenter current))).comp
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter
              (extChartAt throatCoverModelWithCorners firstCenter current))) := by
  exact (throatGaugeFrameBaseChartTransition_cocycle_eventuallyEq period hPeriod
    firstAnchor secondAnchor thirdAnchor firstCenter secondCenter thirdCenter
      current hCurrent hFirst hSecond).eq_of_nhds

/-- Jacobian cocycle of the varying frame transition, including the pullback
through the first base-chart transition. -/
theorem throatGaugeFrameBaseChartTransition_firstDerivative_cocycle
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
    (direction : ThroatCoverCoordinates) :
    fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor thirdAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current) direction =
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor thirdAnchor secondCenter
          (extChartAt throatCoverModelWithCorners secondCenter current)).comp
        (fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) direction) +
      (fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            secondAnchor thirdAnchor secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)
            direction)).comp
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current)) := by
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstTransition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor firstCenter
  let secondTransition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      secondAnchor thirdAnchor secondCenter
  let directTransition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      firstAnchor thirdAnchor firstCenter
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
      throatGaugeCovectorTransitionCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod firstAnchor secondAnchor firstCenter current
          ⟨hCurrent.1, hCurrent.2.1⟩ hFirst
  have hSecondTransition : ContDiffAt Real 2 secondTransition secondCoordinate := by
    simpa only [secondTransition, secondCoordinate] using
      throatGaugeCovectorTransitionCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod secondAnchor thirdAnchor secondCenter current
          hCurrent.2 hSecond
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
    have hCombined := throatGaugeFrameBaseChartTransition_cocycle_eventuallyEq
      period hPeriod firstAnchor secondAnchor thirdAnchor firstCenter
        secondCenter secondCenter current hCurrent hFirst hSecond
    exact hCombined.fun_comp Prod.snd
  have hProduct := fderiv_clm_comp
    (hPulledTransition.differentiableAt (by norm_num))
    (hFirstTransition.differentiableAt (by norm_num))
  have hProductApplied := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        (FramedCovector ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates) ↦ derivative direction)
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
theorem throatGaugeFrameBaseChartTransition_secondDerivative_cocycle_apply
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
    (first second : ThroatCoverCoordinates)
    (covector : FramedCovector ThroatCoverCoordinates) :
    fderiv Real
        (fun coordinate =>
          fderiv Real
            (throatGaugeCovectorTransitionCenteredChart period hPeriod
              firstAnchor thirdAnchor firstCenter) coordinate second)
        (extChartAt throatCoverModelWithCorners firstCenter current)
          first covector =
      throatGaugeCovectorTransitionCenteredChart period hPeriod
          secondAnchor thirdAnchor secondCenter
          (extChartAt throatCoverModelWithCorners secondCenter current)
        (fderiv Real
          (fun coordinate =>
            fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                firstAnchor secondAnchor firstCenter) coordinate second)
          (extChartAt throatCoverModelWithCorners firstCenter current)
            first covector) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            secondAnchor thirdAnchor secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) first)
        (fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
            second covector) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            secondAnchor thirdAnchor secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current) second)
        (fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)
            first covector) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (throatGaugeCovectorTransitionCenteredChart period hPeriod
                secondAnchor thirdAnchor secondCenter) coordinate
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
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current) covector) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            secondAnchor thirdAnchor secondCenter)
          (extChartAt throatCoverModelWithCorners secondCenter current)
          (fderiv Real
            (fun coordinate =>
              fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  firstCenter secondCenter) coordinate second)
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first)
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter
          (extChartAt throatCoverModelWithCorners firstCenter current) covector) := by
  let baseTransition :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let firstTransition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor firstCenter
  let secondTransition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      secondAnchor thirdAnchor secondCenter
  let directTransition :=
    throatGaugeCovectorTransitionCenteredChart period hPeriod
      firstAnchor thirdAnchor firstCenter
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
      throatGaugeCovectorTransitionCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod firstAnchor secondAnchor firstCenter current
          ⟨hCurrent.1, hCurrent.2.1⟩ hFirst
  have hSecondTransition : ContDiffAt Real 2 secondTransition secondCoordinate := by
    simpa only [secondTransition, secondCoordinate] using
      throatGaugeCovectorTransitionCenteredChart_contDiffAt_two_of_mem_source
        period hPeriod secondAnchor thirdAnchor secondCenter current
          hCurrent.2 hSecond
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
    have hCombined := throatGaugeFrameBaseChartTransition_cocycle_eventuallyEq
      period hPeriod firstAnchor secondAnchor thirdAnchor firstCenter
        secondCenter secondCenter current hCurrent hFirst hSecond
    exact hCombined.fun_comp Prod.snd
  have hProduct := second_fderiv_clm_comp_apply
    (secondTransition ∘ baseTransition) firstTransition firstCoordinate
      first second covector hPulledTransition hFirstTransition
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
        (FramedCovector ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates) ↦ derivative first covector)
    hGermSecond
  rw [hGermSecondApplied, hProduct, hPulledFirst, hPulledSecond, hAt]
  simp only [baseTransition, firstTransition, secondTransition,
    firstCoordinate, secondCoordinate, add_apply,
    ContinuousLinearMap.comp_apply]
  abel

end
end P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderCocycle4D
end JanusFormal
