import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Third-order Leibniz rule for semidirect continuous-linear-map composition

This gate isolates the real Frechet-calculus identity for a pulled-back
varying continuous linear map composed with another varying continuous linear
map.  Its public theorem is the full fifteen-term third-order formula.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 1200000

noncomputable section

open Filter Topology
open P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
  NormedSpace.toModule PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

variable
    {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup V] [NormedSpace Real V]

private theorem fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  have hApplied := congrArg
    (fun derivative : E →L[Real] G => derivative direction) hDerivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hApplied

private theorem fderiv_secondFDeriv_apply_const_apply
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (function : E → F) (point first second third : E)
    (hFunction : ContDiffAt Real 3 function point) :
    fderiv Real
        (fun current =>
          fderiv Real (fderiv Real function) current second third)
        point first =
      fderiv Real (fderiv Real (fderiv Real function))
        point first second third := by
  have hHessian :
      DifferentiableAt Real
        (fderiv Real (fderiv Real function)) point :=
    ((hFunction.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  let hessianAtSecond : E → E →L[Real] F :=
    fun current => fderiv Real (fderiv Real function) current second
  have hHessianAtSecond :
      DifferentiableAt Real hessianAtSecond point := by
    have hApplied := hHessian.clm_apply
      (differentiableAt_const (c := second))
    simpa only [hessianAtSecond] using hApplied
  calc
    fderiv Real
        (fun current =>
          fderiv Real (fderiv Real function) current second third)
        point first =
      fderiv Real hessianAtSecond point first third := by
        simpa only [hessianAtSecond] using
          fderiv_continuousLinearMap_apply_const hessianAtSecond
            point first third hHessianAtSecond
    _ = fderiv Real (fderiv Real (fderiv Real function))
        point first second third := by
      rw [fderiv_continuousLinearMap_apply_const
        (fderiv Real (fderiv Real function)) point first second hHessian]

private theorem second_fderiv_clm_apply_const_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (field : X → Y →L[Real] Z) (point first second : X) (value : Y)
    (hField : ContDiffAt Real 2 field point) :
    fderiv Real (fderiv Real (fun current => field current value))
        point first second =
      fderiv Real (fderiv Real field) point first second value := by
  have hFieldDerivative : DifferentiableAt Real (fderiv Real field) point :=
    (hField.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hAppliedDerivative : DifferentiableAt Real
      (fun current => fderiv Real field current second) point :=
    hFieldDerivative.clm_apply (differentiableAt_const (c := second))
  have hEvaluation : ContDiffAt Real 2
      (fun current => field current value) point :=
    hField.clm_apply contDiffAt_const
  have hEvaluationDerivative : DifferentiableAt Real
      (fderiv Real (fun current => field current value)) point :=
    (hEvaluation.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hFieldEventually : ∀ᶠ current in nhds point,
      DifferentiableAt Real field current := by
    filter_upwards [hField.eventually (by norm_num)] with current hCurrent
    exact hCurrent.differentiableAt (by norm_num)
  have hFirstFormula :
      (fun current =>
        fderiv Real (fun base => field base value) current second) =ᶠ[nhds point]
      (fun current => fderiv Real field current second value) := by
    filter_upwards [hFieldEventually] with current hCurrent
    exact fderiv_continuousLinearMap_apply_const field current second value
      hCurrent
  have hLeft := fderiv_continuousLinearMap_apply_const
    (maps := fderiv Real (fun current => field current value))
    point first second hEvaluationDerivative
  have hRightOuter := fderiv_continuousLinearMap_apply_const
    (maps := fun current => fderiv Real field current second)
    point first value hAppliedDerivative
  have hRightInner := fderiv_continuousLinearMap_apply_const
    (maps := fderiv Real field) point first second hFieldDerivative
  calc
    fderiv Real (fderiv Real (fun current => field current value))
        point first second =
      fderiv Real
        (fun current =>
          fderiv Real (fun base => field base value) current second)
        point first := hLeft.symm
    _ = fderiv Real
        (fun current => fderiv Real field current second value)
        point first := congrArg
          (fun derivative : X →L[Real] Z => derivative first)
          hFirstFormula.fderiv_eq
    _ = fderiv Real (fun current => fderiv Real field current second)
        point first value := hRightOuter
    _ = fderiv Real (fderiv Real field) point first second value := by
      exact congrArg (fun derivative : Y →L[Real] Z => derivative value)
        hRightInner

/-- Pointwise second-order chain rule for composition. -/
private theorem second_fderiv_comp_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inner : E → F) (outer : F → G) (point : E)
    (hInner : ContDiffAt Real 2 inner point)
    (hOuter : ContDiffAt Real 2 outer (inner point))
    (first second : E) :
    fderiv Real (fderiv Real (outer ∘ inner)) point first second =
      fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real inner point first)
          (fderiv Real inner point second) +
        fderiv Real outer (inner point)
          (fderiv Real (fderiv Real inner) point first second) := by
  have hInnerDiff : DifferentiableAt Real inner point :=
    hInner.differentiableAt (by norm_num)
  have hInnerNear := hInner.eventually (by norm_num)
  have hOuterNearAt := hOuter.eventually (by norm_num)
  have hOuterNear := hInner.continuousAt.eventually hOuterNearAt
  have hFirstDerivative :
      (fderiv Real (outer ∘ inner)) =ᶠ[𝓝 point]
        (fun current =>
          (fderiv Real outer (inner current)).comp
            (fderiv Real inner current)) := by
    filter_upwards [hInnerNear, hOuterNear] with current hCurrentInner
      hCurrentOuter
    exact fderiv_comp current
      (hCurrentOuter.differentiableAt (by norm_num))
      (hCurrentInner.differentiableAt (by norm_num))
  have hSecondDerivative :
      fderiv Real (fderiv Real (outer ∘ inner)) point =
        fderiv Real
          (fun current =>
            (fderiv Real outer (inner current)).comp
              (fderiv Real inner current)) point :=
    hFirstDerivative.fderiv_eq
  rw [hSecondDerivative]
  have hOuterDerivative :
      ContDiffAt Real 1 (fderiv Real outer) (inner point) :=
    hOuter.fderiv_right (m := 1) (by norm_num)
  have hInnerDerivative :
      ContDiffAt Real 1 (fderiv Real inner) point :=
    hInner.fderiv_right (m := 1) (by norm_num)
  have hComposedOuterDerivative :
      DifferentiableAt Real
        (fun current => fderiv Real outer (inner current)) point :=
    (hOuterDerivative.differentiableAt (by norm_num)).comp point hInnerDiff
  have hInnerDerivativeDiff :
      DifferentiableAt Real (fderiv Real inner) point :=
    hInnerDerivative.differentiableAt (by norm_num)
  rw [fderiv_clm_comp hComposedOuterDerivative hInnerDerivativeDiff]
  have hComposedOuterFDeriv :
      fderiv Real (fun current => fderiv Real outer (inner current)) point =
        (fderiv Real (fderiv Real outer) (inner point)).comp
          (fderiv Real inner point) :=
    fderiv_comp point
      (hOuterDerivative.differentiableAt (by norm_num)) hInnerDiff
  rw [hComposedOuterFDeriv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  abel

private theorem third_fderiv_comp_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inner : E → F) (outer : F → G) (point : E)
    (hInner : ContDiffAt Real 3 inner point)
    (hOuter : ContDiffAt Real 3 outer (inner point))
    (first second third : E) :
    fderiv Real (fderiv Real (fderiv Real (outer ∘ inner)))
        point first second third =
      fderiv Real (fderiv Real (fderiv Real outer)) (inner point)
          (fderiv Real inner point first)
          (fderiv Real inner point second)
          (fderiv Real inner point third) +
        fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real (fderiv Real inner) point first second)
          (fderiv Real inner point third) +
        fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real (fderiv Real inner) point first third)
          (fderiv Real inner point second) +
        fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real (fderiv Real inner) point second third)
          (fderiv Real inner point first) +
        fderiv Real outer (inner point)
          (fderiv Real (fderiv Real (fderiv Real inner))
            point first second third) := by
  let innerJacobianAtSecond : E → F :=
    fun current => fderiv Real inner current second
  let innerJacobianAtThird : E → F :=
    fun current => fderiv Real inner current third
  let innerHessianAtSecondThird : E → F :=
    fun current =>
      fderiv Real (fderiv Real inner) current second third
  let outerJacobianAlongInner : E → F →L[Real] G :=
    fun current => fderiv Real outer (inner current)
  let outerHessianAlongInner : E → F →L[Real] F →L[Real] G :=
    fun current => fderiv Real (fderiv Real outer) (inner current)
  let outerHessianAppliedSecond : E → F →L[Real] G :=
    fun current =>
      outerHessianAlongInner current (innerJacobianAtSecond current)
  let firstTerm : E → G :=
    fun current =>
      outerHessianAppliedSecond current (innerJacobianAtThird current)
  let secondTerm : E → G :=
    fun current =>
      outerJacobianAlongInner current (innerHessianAtSecondThird current)
  have hInnerDiff : DifferentiableAt Real inner point :=
    hInner.differentiableAt (by norm_num)
  have hInnerJacobian :
      DifferentiableAt Real (fderiv Real inner) point :=
    (hInner.fderiv_right (m := 2) (by norm_num)).differentiableAt
      (by norm_num)
  have hInnerHessian :
      DifferentiableAt Real (fderiv Real (fderiv Real inner)) point :=
    ((hInner.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hOuterJacobian :
      DifferentiableAt Real (fderiv Real outer) (inner point) :=
    (hOuter.fderiv_right (m := 2) (by norm_num)).differentiableAt
      (by norm_num)
  have hOuterHessian :
      DifferentiableAt Real (fderiv Real (fderiv Real outer))
        (inner point) :=
    ((hOuter.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hInnerJacobianAtSecond :
      DifferentiableAt Real innerJacobianAtSecond point := by
    have hApplied := hInnerJacobian.clm_apply
      (differentiableAt_const (c := second))
    simpa only [innerJacobianAtSecond] using hApplied
  have hInnerJacobianAtThird :
      DifferentiableAt Real innerJacobianAtThird point := by
    have hApplied := hInnerJacobian.clm_apply
      (differentiableAt_const (c := third))
    simpa only [innerJacobianAtThird] using hApplied
  have hInnerHessianAtSecond :
      DifferentiableAt Real
        (fun current =>
          fderiv Real (fderiv Real inner) current second) point :=
    hInnerHessian.clm_apply (differentiableAt_const (c := second))
  have hInnerHessianAtSecondThird :
      DifferentiableAt Real innerHessianAtSecondThird point := by
    have hApplied := hInnerHessianAtSecond.clm_apply
      (differentiableAt_const (c := third))
    simpa only [innerHessianAtSecondThird] using hApplied
  have hOuterJacobianAlongInner :
      DifferentiableAt Real outerJacobianAlongInner point := by
    simpa only [outerJacobianAlongInner, Function.comp_def] using
      hOuterJacobian.comp point hInnerDiff
  have hOuterHessianAlongInner :
      DifferentiableAt Real outerHessianAlongInner point := by
    simpa only [outerHessianAlongInner, Function.comp_def] using
      hOuterHessian.comp point hInnerDiff
  have hOuterHessianAppliedSecond :
      DifferentiableAt Real outerHessianAppliedSecond point := by
    have hApplied :=
      hOuterHessianAlongInner.clm_apply hInnerJacobianAtSecond
    simpa only [outerHessianAppliedSecond] using hApplied
  have hFirstTerm : DifferentiableAt Real firstTerm point := by
    have hApplied :=
      hOuterHessianAppliedSecond.clm_apply hInnerJacobianAtThird
    simpa only [firstTerm] using hApplied
  have hSecondTerm : DifferentiableAt Real secondTerm point := by
    have hApplied :=
      hOuterJacobianAlongInner.clm_apply hInnerHessianAtSecondThird
    simpa only [secondTerm] using hApplied
  have hInnerJacobianAtSecondDerivative :
      fderiv Real innerJacobianAtSecond point first =
        fderiv Real (fderiv Real inner) point first second := by
    simpa only [innerJacobianAtSecond] using
      fderiv_continuousLinearMap_apply_const
        (fderiv Real inner) point first second hInnerJacobian
  have hInnerJacobianAtThirdDerivative :
      fderiv Real innerJacobianAtThird point first =
        fderiv Real (fderiv Real inner) point first third := by
    simpa only [innerJacobianAtThird] using
      fderiv_continuousLinearMap_apply_const
        (fderiv Real inner) point first third hInnerJacobian
  have hInnerHessianAtSecondThirdDerivative :
      fderiv Real innerHessianAtSecondThird point first =
        fderiv Real (fderiv Real (fderiv Real inner))
          point first second third := by
    simpa only [innerHessianAtSecondThird] using
      fderiv_secondFDeriv_apply_const_apply inner point first second third hInner
  have hOuterJacobianAlongInnerDerivative :
      fderiv Real outerJacobianAlongInner point first =
        fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real inner point first) := by
    have hDerivative :=
      fderiv_comp point hOuterJacobian hInnerDiff
    have hApplied := congrArg
      (fun derivative : E →L[Real] (F →L[Real] G) =>
        derivative first) hDerivative
    simpa only [outerJacobianAlongInner, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hApplied
  have hOuterHessianAlongInnerDerivative :
      fderiv Real outerHessianAlongInner point first =
        fderiv Real (fderiv Real (fderiv Real outer)) (inner point)
          (fderiv Real inner point first) := by
    have hDerivative :=
      fderiv_comp point hOuterHessian hInnerDiff
    have hApplied := congrArg
      (fun derivative : E →L[Real]
          (F →L[Real] F →L[Real] G) => derivative first) hDerivative
    simpa only [outerHessianAlongInner, Function.comp_def,
      ContinuousLinearMap.comp_apply] using hApplied
  have hOuterHessianAppliedSecondDerivative :
      fderiv Real outerHessianAppliedSecond point first =
        outerHessianAlongInner point
            (fderiv Real innerJacobianAtSecond point first) +
          fderiv Real outerHessianAlongInner point first
            (innerJacobianAtSecond point) := by
    have hDerivative :=
      fderiv_clm_apply hOuterHessianAlongInner hInnerJacobianAtSecond
    have hApplied := congrArg
      (fun derivative : E →L[Real] (F →L[Real] G) =>
        derivative first) hDerivative
    simpa only [outerHessianAppliedSecond, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
      using hApplied
  have hFirstTermDerivative :
      fderiv Real firstTerm point first =
        fderiv Real (fderiv Real outer) (inner point)
            (fderiv Real inner point second)
            (fderiv Real (fderiv Real inner) point first third) +
          fderiv Real (fderiv Real outer) (inner point)
            (fderiv Real (fderiv Real inner) point first second)
            (fderiv Real inner point third) +
          fderiv Real (fderiv Real (fderiv Real outer)) (inner point)
            (fderiv Real inner point first)
            (fderiv Real inner point second)
            (fderiv Real inner point third) := by
    have hDerivative :=
      fderiv_clm_apply hOuterHessianAppliedSecond hInnerJacobianAtThird
    have hApplied := congrArg
      (fun derivative : E →L[Real] G => derivative first) hDerivative
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    rw [hInnerJacobianAtThirdDerivative,
      hOuterHessianAppliedSecondDerivative,
      hInnerJacobianAtSecondDerivative,
      hOuterHessianAlongInnerDerivative] at hApplied
    simp only [outerHessianAppliedSecond, outerHessianAlongInner,
      innerJacobianAtSecond, innerJacobianAtThird, add_apply] at hApplied
    rw [hApplied]
    abel
  have hSecondTermDerivative :
      fderiv Real secondTerm point first =
        fderiv Real outer (inner point)
            (fderiv Real (fderiv Real (fderiv Real inner))
              point first second third) +
          fderiv Real (fderiv Real outer) (inner point)
            (fderiv Real inner point first)
            (fderiv Real (fderiv Real inner) point second third) := by
    have hDerivative :=
      fderiv_clm_apply hOuterJacobianAlongInner
        hInnerHessianAtSecondThird
    have hApplied := congrArg
      (fun derivative : E →L[Real] G => derivative first) hDerivative
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    rw [hInnerHessianAtSecondThirdDerivative,
      hOuterJacobianAlongInnerDerivative] at hApplied
    simpa only [outerJacobianAlongInner, innerHessianAtSecondThird]
      using hApplied
  have hOuterSecondDerivativeSymmetric
      (firstVector secondVector : F) :
      fderiv Real (fderiv Real outer) (inner point)
          firstVector secondVector =
        fderiv Real (fderiv Real outer) (inner point)
          secondVector firstVector :=
    (hOuter.isSymmSndFDerivAt (by norm_num)).eq
      firstVector secondVector
  have hRightDerivative :
      fderiv Real (fun current => firstTerm current + secondTerm current)
          point first =
        fderiv Real (fderiv Real (fderiv Real outer)) (inner point)
            (fderiv Real inner point first)
            (fderiv Real inner point second)
            (fderiv Real inner point third) +
          fderiv Real (fderiv Real outer) (inner point)
            (fderiv Real (fderiv Real inner) point first second)
            (fderiv Real inner point third) +
          fderiv Real (fderiv Real outer) (inner point)
            (fderiv Real (fderiv Real inner) point first third)
            (fderiv Real inner point second) +
          fderiv Real (fderiv Real outer) (inner point)
            (fderiv Real (fderiv Real inner) point second third)
            (fderiv Real inner point first) +
          fderiv Real outer (inner point)
            (fderiv Real (fderiv Real (fderiv Real inner))
              point first second third) := by
    have hDerivative := fderiv_fun_add hFirstTerm hSecondTerm
    have hApplied := congrArg
      (fun derivative : E →L[Real] G => derivative first) hDerivative
    simp only [add_apply] at hApplied
    rw [hFirstTermDerivative, hSecondTermDerivative] at hApplied
    calc
      fderiv Real (fun current => firstTerm current + secondTerm current)
          point first =
        fderiv Real (fderiv Real outer) (inner point)
              (fderiv Real inner point second)
              (fderiv Real (fderiv Real inner) point first third) +
            fderiv Real (fderiv Real outer) (inner point)
              (fderiv Real (fderiv Real inner) point first second)
              (fderiv Real inner point third) +
            fderiv Real (fderiv Real (fderiv Real outer)) (inner point)
              (fderiv Real inner point first)
              (fderiv Real inner point second)
              (fderiv Real inner point third) +
            (fderiv Real outer (inner point)
                (fderiv Real (fderiv Real (fderiv Real inner))
                  point first second third) +
              fderiv Real (fderiv Real outer) (inner point)
                (fderiv Real inner point first)
                (fderiv Real (fderiv Real inner) point second third)) :=
        hApplied
      _ = _ := by
        rw [hOuterSecondDerivativeSymmetric
          (fderiv Real inner point second)
          (fderiv Real (fderiv Real inner) point first third)]
        rw [hOuterSecondDerivativeSymmetric
          (fderiv Real inner point first)
          (fderiv Real (fderiv Real inner) point second third)]
        abel
  have hComposition : ContDiffAt Real 3 (outer ∘ inner) point :=
    hOuter.comp point hInner
  have hLeftDerivative :=
    fderiv_secondFDeriv_apply_const_apply (outer ∘ inner)
      point first second third hComposition
  have hInnerNear := hInner.eventually (by norm_num)
  have hOuterNearAt := hOuter.eventually (by norm_num)
  have hOuterNear := hInner.continuousAt.eventually hOuterNearAt
  have hSecondDerivativeFormula :
      (fun current =>
        fderiv Real (fderiv Real (outer ∘ inner)) current second third) =ᶠ[𝓝 point]
        (fun current => firstTerm current + secondTerm current) := by
    filter_upwards [hInnerNear, hOuterNear]
      with current hCurrentInner hCurrentOuter
    simpa only [firstTerm, secondTerm, outerHessianAppliedSecond,
      outerHessianAlongInner, outerJacobianAlongInner,
      innerJacobianAtSecond, innerJacobianAtThird,
      innerHessianAtSecondThird] using
        second_fderiv_comp_apply inner outer current
          (hCurrentInner.of_le (by norm_num))
          (hCurrentOuter.of_le (by norm_num)) second third
  have hDerivativeEquality :=
    hSecondDerivativeFormula.fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : E →L[Real] G => derivative first)
    hDerivativeEquality
  exact hLeftDerivative.symm.trans (hApplied.trans hRightDerivative)

private theorem third_fderiv_clm_apply_const_apply
    (field : X → (V →L[Real] V))
    (point first second third : X)
    (value : V) (hField : ContDiffAt Real 3 field point) :
    fderiv Real (fderiv Real
        (fderiv Real (fun current => field current value)))
        point first second third =
      fderiv Real (fderiv Real (fderiv Real field))
        point first second third value := by
  let evaluated := fun current => field current value
  have hEvaluated : ContDiffAt Real 3 evaluated point :=
    hField.clm_apply contDiffAt_const
  have hSecondFieldApplied : DifferentiableAt Real
      (fun current =>
        fderiv Real (fderiv Real field) current second third) point := by
    have hSecondField : DifferentiableAt Real
        (fderiv Real (fderiv Real field)) point :=
      ((hField.fderiv_right (m := 2) (by norm_num)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hAtSecond : DifferentiableAt Real
        (fun current =>
          fderiv Real (fderiv Real field) current second) point :=
      DifferentiableAt.clm_apply
        (𝕜 := Real) (E := X) (G := X)
        (H := X →L[Real] (V →L[Real] V))
        (c := fderiv Real (fderiv Real field))
        (u := fun _ : X => second) hSecondField
        (differentiableAt_const (c := second))
    exact hAtSecond.clm_apply (differentiableAt_const (c := third))
  have hNearby : ∀ᶠ current in nhds point,
      ContDiffAt Real 2 field current := by
    filter_upwards [hField.eventually (by norm_num)] with current hCurrent
    exact hCurrent.of_le (by norm_num)
  have hSecondFormula :
      (fun current =>
        fderiv Real (fderiv Real evaluated) current second third) =ᶠ[nhds point]
      (fun current =>
        fderiv Real (fderiv Real field) current second third value) := by
    filter_upwards [hNearby] with current hCurrent
    exact second_fderiv_clm_apply_const_apply field current second third value
      hCurrent
  have hLeft := fderiv_secondFDeriv_apply_const_apply evaluated point first
    second third hEvaluated
  have hRightOuter := fderiv_continuousLinearMap_apply_const
    (maps := fun current =>
      fderiv Real (fderiv Real field) current second third)
    point first value hSecondFieldApplied
  have hRightInner := fderiv_secondFDeriv_apply_const_apply field point first
    second third hField
  calc
    fderiv Real (fderiv Real (fderiv Real evaluated))
        point first second third =
      fderiv Real
        (fun current =>
          fderiv Real (fderiv Real evaluated) current second third)
        point first := hLeft.symm
    _ = fderiv Real
        (fun current =>
          fderiv Real (fderiv Real field) current second third value)
        point first := congrArg
          (fun derivative : X →L[Real] V =>
            derivative first)
          hSecondFormula.fderiv_eq
    _ = fderiv Real
        (fun current =>
          fderiv Real (fderiv Real field) current second third)
        point first value := hRightOuter
    _ = fderiv Real (fderiv Real (fderiv Real field))
        point first second third value := by
      exact congrArg (fun derivative : (V →L[Real] V) => derivative value)
        hRightInner

/-- Third-order Leibniz rule for a varying continuous linear map applied to a
varying vector. -/
private theorem third_fderiv_clm_apply_apply
    (c : X → (V →L[Real] V)) (u : X → V)
    (point first second third : X)
    (hC : ContDiffAt Real 3 c point)
    (hU : ContDiffAt Real 3 u point) :
    fderiv Real (fderiv Real (fderiv Real
        (fun current => c current (u current))))
        point first second third =
      c point
          (fderiv Real (fderiv Real (fderiv Real u))
            point first second third) +
        fderiv Real c point first
          (fderiv Real (fderiv Real u) point second third) +
        fderiv Real c point second
          (fderiv Real (fderiv Real u) point first third) +
        fderiv Real c point third
          (fderiv Real (fderiv Real u) point first second) +
        fderiv Real (fderiv Real c) point first second
          (fderiv Real u point third) +
        fderiv Real (fderiv Real c) point first third
          (fderiv Real u point second) +
        fderiv Real (fderiv Real c) point second third
          (fderiv Real u point first) +
        fderiv Real (fderiv Real (fderiv Real c))
          point first second third (u point) := by
  let uFirstAtSecond : X → V :=
    fun current => fderiv Real u current second
  let uFirstAtThird : X → V :=
    fun current => fderiv Real u current third
  let uSecondAtSecondThird : X → V :=
    fun current => fderiv Real (fderiv Real u) current second third
  let cFirstAtSecond : X → (V →L[Real] V) :=
    fun current => fderiv Real c current second
  let cFirstAtThird : X → (V →L[Real] V) :=
    fun current => fderiv Real c current third
  let cSecondAtSecondThird : X → (V →L[Real] V) :=
    fun current => fderiv Real (fderiv Real c) current second third
  let termZero : X → V :=
    fun current => c current (uSecondAtSecondThird current)
  let termOne : X → V :=
    fun current => cFirstAtSecond current (uFirstAtThird current)
  let termTwo : X → V :=
    fun current => cFirstAtThird current (uFirstAtSecond current)
  let termThree : X → V :=
    fun current => cSecondAtSecondThird current (u current)
  have hCDifferentiable : DifferentiableAt Real c point :=
    hC.differentiableAt (by norm_num)
  have hUDifferentiable : DifferentiableAt Real u point :=
    hU.differentiableAt (by norm_num)
  have hCFirstDerivative : DifferentiableAt Real (fderiv Real c) point :=
    (hC.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hUFirstDerivative : DifferentiableAt Real (fderiv Real u) point :=
    (hU.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hCSecondDerivative :
      DifferentiableAt Real (fderiv Real (fderiv Real c)) point :=
    ((hC.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hUSecondDerivative :
      DifferentiableAt Real (fderiv Real (fderiv Real u)) point :=
    ((hU.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hUFirstAtSecond : DifferentiableAt Real uFirstAtSecond point := by
    simpa only [uFirstAtSecond] using
      hUFirstDerivative.clm_apply (differentiableAt_const (c := second))
  have hUFirstAtThird : DifferentiableAt Real uFirstAtThird point := by
    simpa only [uFirstAtThird] using
      hUFirstDerivative.clm_apply (differentiableAt_const (c := third))
  have hUSecondAtSecondThird :
      DifferentiableAt Real uSecondAtSecondThird point := by
    have hAtSecond : DifferentiableAt Real
        (fun current =>
          fderiv Real (fderiv Real u) current second) point :=
      hUSecondDerivative.clm_apply (differentiableAt_const (c := second))
    simpa only [uSecondAtSecondThird] using
      hAtSecond.clm_apply (differentiableAt_const (c := third))
  have hCFirstAtSecond : DifferentiableAt Real cFirstAtSecond point := by
    simpa only [cFirstAtSecond] using
      hCFirstDerivative.clm_apply (differentiableAt_const (c := second))
  have hCFirstAtThird : DifferentiableAt Real cFirstAtThird point := by
    simpa only [cFirstAtThird] using
      hCFirstDerivative.clm_apply (differentiableAt_const (c := third))
  have hCSecondAtSecondThird :
      DifferentiableAt Real cSecondAtSecondThird point := by
    have hAtSecond : DifferentiableAt Real
        (fun current =>
          fderiv Real (fderiv Real c) current second) point :=
      DifferentiableAt.clm_apply
        (𝕜 := Real) (E := X) (G := X)
        (H := X →L[Real] (V →L[Real] V))
        (c := fderiv Real (fderiv Real c))
        (u := fun _ : X => second) hCSecondDerivative
        (differentiableAt_const (c := second))
    simpa only [cSecondAtSecondThird] using
      hAtSecond.clm_apply (differentiableAt_const (c := third))
  have hTermZero : DifferentiableAt Real termZero point := by
    simpa only [termZero] using
      hCDifferentiable.clm_apply hUSecondAtSecondThird
  have hTermOne : DifferentiableAt Real termOne point := by
    simpa only [termOne] using
      hCFirstAtSecond.clm_apply hUFirstAtThird
  have hTermTwo : DifferentiableAt Real termTwo point := by
    simpa only [termTwo] using
      hCFirstAtThird.clm_apply hUFirstAtSecond
  have hTermThree : DifferentiableAt Real termThree point := by
    simpa only [termThree] using
      hCSecondAtSecondThird.clm_apply hUDifferentiable
  have hUFirstAtSecondDerivative :
      fderiv Real uFirstAtSecond point first =
        fderiv Real (fderiv Real u) point first second := by
    simpa only [uFirstAtSecond] using
      fderiv_continuousLinearMap_apply_const (fderiv Real u)
        point first second hUFirstDerivative
  have hUFirstAtThirdDerivative :
      fderiv Real uFirstAtThird point first =
        fderiv Real (fderiv Real u) point first third := by
    simpa only [uFirstAtThird] using
      fderiv_continuousLinearMap_apply_const (fderiv Real u)
        point first third hUFirstDerivative
  have hUSecondAtSecondThirdDerivative :
      fderiv Real uSecondAtSecondThird point first =
        fderiv Real (fderiv Real (fderiv Real u))
          point first second third := by
    simpa only [uSecondAtSecondThird] using
      fderiv_secondFDeriv_apply_const_apply u point first second third hU
  have hCFirstAtSecondDerivative :
      fderiv Real cFirstAtSecond point first =
        fderiv Real (fderiv Real c) point first second := by
    simpa only [cFirstAtSecond] using
      fderiv_continuousLinearMap_apply_const (fderiv Real c)
        point first second hCFirstDerivative
  have hCFirstAtThirdDerivative :
      fderiv Real cFirstAtThird point first =
        fderiv Real (fderiv Real c) point first third := by
    simpa only [cFirstAtThird] using
      fderiv_continuousLinearMap_apply_const (fderiv Real c)
        point first third hCFirstDerivative
  have hCSecondAtSecondThirdDerivative :
      fderiv Real cSecondAtSecondThird point first =
        fderiv Real (fderiv Real (fderiv Real c))
          point first second third := by
    simpa only [cSecondAtSecondThird] using
      fderiv_secondFDeriv_apply_const_apply c point first second third hC
  have hTermZeroDerivative :
      fderiv Real termZero point first =
        c point
            (fderiv Real (fderiv Real (fderiv Real u))
              point first second third) +
          fderiv Real c point first
            (fderiv Real (fderiv Real u) point second third) := by
    have hProduct := fderiv_clm_apply hCDifferentiable
      hUSecondAtSecondThird
    have hApplied := congrArg
      (fun derivative : (X →L[Real] V) => derivative first) hProduct
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    rw [hUSecondAtSecondThirdDerivative] at hApplied
    simpa only [termZero, uSecondAtSecondThird] using hApplied
  have hTermOneDerivative :
      fderiv Real termOne point first =
        fderiv Real c point second
            (fderiv Real (fderiv Real u) point first third) +
          fderiv Real (fderiv Real c) point first second
            (fderiv Real u point third) := by
    have hProduct := fderiv_clm_apply hCFirstAtSecond hUFirstAtThird
    have hApplied := congrArg
      (fun derivative : (X →L[Real] V) => derivative first) hProduct
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    rw [hUFirstAtThirdDerivative, hCFirstAtSecondDerivative] at hApplied
    simpa only [termOne, cFirstAtSecond, uFirstAtThird] using hApplied
  have hTermTwoDerivative :
      fderiv Real termTwo point first =
        fderiv Real c point third
            (fderiv Real (fderiv Real u) point first second) +
          fderiv Real (fderiv Real c) point first third
            (fderiv Real u point second) := by
    have hProduct := fderiv_clm_apply hCFirstAtThird hUFirstAtSecond
    have hApplied := congrArg
      (fun derivative : (X →L[Real] V) => derivative first) hProduct
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    rw [hUFirstAtSecondDerivative, hCFirstAtThirdDerivative] at hApplied
    simpa only [termTwo, cFirstAtThird, uFirstAtSecond] using hApplied
  have hTermThreeDerivative :
      fderiv Real termThree point first =
        fderiv Real (fderiv Real c) point second third
            (fderiv Real u point first) +
          fderiv Real (fderiv Real (fderiv Real c))
            point first second third (u point) := by
    have hProduct := fderiv_clm_apply hCSecondAtSecondThird hUDifferentiable
    have hApplied := congrArg
      (fun derivative : (X →L[Real] V) => derivative first) hProduct
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    rw [hCSecondAtSecondThirdDerivative] at hApplied
    simpa only [termThree, cSecondAtSecondThird] using hApplied
  have hCNear := hC.eventually (by norm_num)
  have hUNear := hU.eventually (by norm_num)
  have hSecondFormula :
      (fun current =>
        fderiv Real (fderiv Real (fun base => c base (u base)))
          current second third) =ᶠ[nhds point]
      (fun current =>
        termZero current + termOne current + termTwo current +
          termThree current) := by
    filter_upwards [hCNear, hUNear] with current hCurrentC hCurrentU
    have hCurrentC3 : ContDiffAt Real 3 c current := hCurrentC
    have hCurrentC2 : ContDiffAt Real 2 c current :=
      hCurrentC.of_le (by norm_num)
    have hCurrentU2 : ContDiffAt Real 2 u current :=
      hCurrentU.of_le (by norm_num)
    have hFormula := second_fderiv_clm_apply_apply c u current second third
      hCurrentC2 hCurrentU2
    have hCFirstDerivativeCurrent :
        DifferentiableAt Real (fderiv Real c) current :=
      (hCurrentC3.fderiv_right (m := 2) (by norm_num)).differentiableAt
        (by norm_num)
    have hBridge := fderiv_continuousLinearMap_apply_const
      (fderiv Real c) current second third hCFirstDerivativeCurrent
    rw [hBridge] at hFormula
    simpa only [termZero, termOne, termTwo, termThree,
      uFirstAtSecond, uFirstAtThird, uSecondAtSecondThird,
      cFirstAtSecond, cFirstAtThird, cSecondAtSecondThird] using hFormula
  have hRightDerivative :
      fderiv Real
          (fun current =>
            termZero current + termOne current + termTwo current +
              termThree current)
          point first =
        c point
            (fderiv Real (fderiv Real (fderiv Real u))
              point first second third) +
          fderiv Real c point first
            (fderiv Real (fderiv Real u) point second third) +
          fderiv Real c point second
            (fderiv Real (fderiv Real u) point first third) +
          fderiv Real c point third
            (fderiv Real (fderiv Real u) point first second) +
          fderiv Real (fderiv Real c) point first second
            (fderiv Real u point third) +
          fderiv Real (fderiv Real c) point first third
            (fderiv Real u point second) +
          fderiv Real (fderiv Real c) point second third
            (fderiv Real u point first) +
          fderiv Real (fderiv Real (fderiv Real c))
            point first second third (u point) := by
    change
      fderiv Real (termZero + termOne + termTwo + termThree)
          point first = _
    rw [fderiv_add ((hTermZero.add hTermOne).add hTermTwo) hTermThree,
      fderiv_add (hTermZero.add hTermOne) hTermTwo,
      fderiv_add hTermZero hTermOne]
    simp only [add_apply]
    rw [hTermZeroDerivative, hTermOneDerivative,
      hTermTwoDerivative, hTermThreeDerivative]
    abel
  have hProduct : ContDiffAt Real 3
      (fun current => c current (u current)) point :=
    hC.clm_apply hU
  have hLeft := fderiv_secondFDeriv_apply_const_apply
    (fun current => c current (u current)) point first second third hProduct
  calc
    fderiv Real (fderiv Real (fderiv Real
        (fun current => c current (u current))))
        point first second third =
      fderiv Real
          (fun current =>
            fderiv Real (fderiv Real (fun base => c base (u base)))
              current second third)
          point first := hLeft.symm
    _ = fderiv Real
          (fun current =>
            termZero current + termOne current + termTwo current +
              termThree current)
          point first := congrArg
            (fun derivative : (X →L[Real] V) => derivative first)
            hSecondFormula.fderiv_eq
    _ = _ := hRightDerivative

/-- Third derivative of pointwise composition of two varying continuous
linear maps, evaluated on a fixed vector. -/
private theorem third_fderiv_clm_comp_apply_raw
    (outer inner : X → (V →L[Real] V))
    (point first second third : X) (value : V)
    (hOuter : ContDiffAt Real 3 outer point)
    (hInner : ContDiffAt Real 3 inner point) :
    fderiv Real (fderiv Real (fderiv Real
        (fun current => (outer current).comp (inner current))))
        point first second third value =
      outer point
          (fderiv Real (fderiv Real (fderiv Real inner))
            point first second third value) +
        fderiv Real outer point first
          (fderiv Real (fderiv Real inner) point second third value) +
        fderiv Real outer point second
          (fderiv Real (fderiv Real inner) point first third value) +
        fderiv Real outer point third
          (fderiv Real (fderiv Real inner) point first second value) +
        fderiv Real (fderiv Real outer) point first second
          (fderiv Real inner point third value) +
        fderiv Real (fderiv Real outer) point first third
          (fderiv Real inner point second value) +
        fderiv Real (fderiv Real outer) point second third
          (fderiv Real inner point first value) +
        fderiv Real (fderiv Real (fderiv Real outer))
          point first second third (inner point value) := by
  let evaluatedInner := fun current => inner current value
  let composition := fun current => (outer current).comp (inner current)
  have hEvaluatedInner : ContDiffAt Real 3 evaluatedInner point := by
    simpa only [evaluatedInner] using hInner.clm_apply contDiffAt_const
  have hComposition : ContDiffAt Real 3 composition point := by
    simpa only [composition] using hOuter.clm_comp hInner
  have hFormula := third_fderiv_clm_apply_apply outer evaluatedInner point
    first second third hOuter hEvaluatedInner
  have hLeft := third_fderiv_clm_apply_const_apply composition point first
    second third value hComposition
  have hInnerFirst (direction : X) :
      fderiv Real evaluatedInner point direction =
        fderiv Real inner point direction value := by
    simpa only [evaluatedInner] using
      fderiv_continuousLinearMap_apply_const inner point direction value
        (hInner.differentiableAt (by norm_num))
  have hInnerSecond (firstDirection secondDirection : X) :
      fderiv Real (fderiv Real evaluatedInner) point
          firstDirection secondDirection =
        fderiv Real (fderiv Real inner) point
          firstDirection secondDirection value := by
    simpa only [evaluatedInner] using
      second_fderiv_clm_apply_const_apply inner point firstDirection
        secondDirection value (hInner.of_le (by norm_num))
  have hInnerThird :
      fderiv Real (fderiv Real (fderiv Real evaluatedInner))
          point first second third =
        fderiv Real (fderiv Real (fderiv Real inner))
          point first second third value := by
    simpa only [evaluatedInner] using
      third_fderiv_clm_apply_const_apply inner point first second third value
        hInner
  rw [← hLeft]
  simpa only [composition, evaluatedInner, ContinuousLinearMap.comp_apply,
    hInnerFirst, hInnerSecond, hInnerThird] using hFormula

/-- The full fifteen-term third-order formula for
`x ↦ outer (base x) ∘ inner x`. -/
theorem third_fderiv_semidirect_comp_apply
    (base : X → X)
    (outer inner : X → (V →L[Real] V))
    (point first second third : X) (value : V)
    (hBase : ContDiffAt Real 3 base point)
    (hOuter : ContDiffAt Real 3 outer (base point))
    (hInner : ContDiffAt Real 3 inner point) :
    fderiv Real (fderiv Real (fderiv Real
        (fun current =>
          (outer (base current)).comp (inner current))))
        point first second third value =
      outer (base point)
          (fderiv Real (fderiv Real (fderiv Real inner))
            point first second third value) +
        fderiv Real outer (base point)
          (fderiv Real base point first)
          (fderiv Real (fderiv Real inner) point second third value) +
        fderiv Real outer (base point)
          (fderiv Real base point second)
          (fderiv Real (fderiv Real inner) point first third value) +
        fderiv Real outer (base point)
          (fderiv Real base point third)
          (fderiv Real (fderiv Real inner) point first second value) +
        fderiv Real (fderiv Real outer) (base point)
          (fderiv Real base point first)
          (fderiv Real base point second)
          (fderiv Real inner point third value) +
        fderiv Real outer (base point)
          (fderiv Real (fderiv Real base) point first second)
          (fderiv Real inner point third value) +
        fderiv Real (fderiv Real outer) (base point)
          (fderiv Real base point first)
          (fderiv Real base point third)
          (fderiv Real inner point second value) +
        fderiv Real outer (base point)
          (fderiv Real (fderiv Real base) point first third)
          (fderiv Real inner point second value) +
        fderiv Real (fderiv Real outer) (base point)
          (fderiv Real base point second)
          (fderiv Real base point third)
          (fderiv Real inner point first value) +
        fderiv Real outer (base point)
          (fderiv Real (fderiv Real base) point second third)
          (fderiv Real inner point first value) +
        fderiv Real (fderiv Real (fderiv Real outer)) (base point)
          (fderiv Real base point first)
          (fderiv Real base point second)
          (fderiv Real base point third)
          (inner point value) +
        fderiv Real (fderiv Real outer) (base point)
          (fderiv Real (fderiv Real base) point first second)
          (fderiv Real base point third)
          (inner point value) +
        fderiv Real (fderiv Real outer) (base point)
          (fderiv Real (fderiv Real base) point first third)
          (fderiv Real base point second)
          (inner point value) +
        fderiv Real (fderiv Real outer) (base point)
          (fderiv Real (fderiv Real base) point second third)
          (fderiv Real base point first)
          (inner point value) +
        fderiv Real outer (base point)
          (fderiv Real (fderiv Real (fderiv Real base))
            point first second third)
          (inner point value) := by
  let pulledOuter := outer ∘ base
  have hPulledOuter : ContDiffAt Real 3 pulledOuter point := by
    simpa only [pulledOuter] using hOuter.comp point hBase
  have hProduct := third_fderiv_clm_comp_apply_raw pulledOuter inner point
    first second third value hPulledOuter hInner
  have hPulledFirst (direction : X) :
      fderiv Real pulledOuter point direction =
        fderiv Real outer (base point)
          (fderiv Real base point direction) := by
    have hChain := fderiv_comp point
      (hOuter.differentiableAt (by norm_num))
      (hBase.differentiableAt (by norm_num))
    have hApplied := congrArg
      (fun derivative : (X →L[Real] (V →L[Real] V)) =>
        derivative direction) hChain
    simpa only [pulledOuter, ContinuousLinearMap.comp_apply] using hApplied
  have hPulledSecond
      (firstDirection secondDirection : X) :
      fderiv Real (fderiv Real pulledOuter) point
          firstDirection secondDirection =
        fderiv Real (fderiv Real outer) (base point)
            (fderiv Real base point firstDirection)
            (fderiv Real base point secondDirection) +
          fderiv Real outer (base point)
            (fderiv Real (fderiv Real base) point
              firstDirection secondDirection) := by
    simpa only [pulledOuter] using
      second_fderiv_comp_apply base outer point
        (hBase.of_le (by norm_num)) (hOuter.of_le (by norm_num))
        firstDirection secondDirection
  have hPulledThird :
      fderiv Real (fderiv Real (fderiv Real pulledOuter))
          point first second third =
        fderiv Real (fderiv Real (fderiv Real outer)) (base point)
            (fderiv Real base point first)
            (fderiv Real base point second)
            (fderiv Real base point third) +
          fderiv Real (fderiv Real outer) (base point)
            (fderiv Real (fderiv Real base) point first second)
            (fderiv Real base point third) +
          fderiv Real (fderiv Real outer) (base point)
            (fderiv Real (fderiv Real base) point first third)
            (fderiv Real base point second) +
          fderiv Real (fderiv Real outer) (base point)
            (fderiv Real (fderiv Real base) point second third)
            (fderiv Real base point first) +
          fderiv Real outer (base point)
            (fderiv Real (fderiv Real (fderiv Real base))
              point first second third) := by
    simpa only [pulledOuter] using
      third_fderiv_comp_apply base outer point hBase hOuter first second third
  change
    fderiv Real (fderiv Real (fderiv Real
        (fun current => (pulledOuter current).comp (inner current))))
        point first second third value = _
  rw [hProduct, hPulledFirst first, hPulledFirst second,
    hPulledFirst third, hPulledSecond first second,
    hPulledSecond first third, hPulledSecond second third, hPulledThird]
  simp only [pulledOuter, Function.comp_apply, add_apply]
  abel
end
end P0EFTJanusProgramPContinuousLinearMapThirdOrderLeibniz4D
end JanusFormal
