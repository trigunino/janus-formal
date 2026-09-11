import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D

/-!
# Third-order cocycle for actual throat base-chart transitions

On a triple overlap, the third derivative of the direct extended-chart
transition satisfies the five-term third-order chain rule.  This is only the
base-coordinate cocycle; no fiber transition or physical third-jet atlas is
constructed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdJet4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
  NormedSpace.toModule PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

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

private theorem fderiv_secondFDeriv_apply_const
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

/-- Pointwise third-order chain rule for maps between real normed spaces. -/
theorem third_fderiv_comp_apply
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
      fderiv_secondFDeriv_apply_const inner point first second third hInner
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
    fderiv_secondFDeriv_apply_const (outer ∘ inner)
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

/-- On a triple overlap, the actual base-transition third derivatives obey
the exact five-term composition law. -/
theorem throatGaugeBaseChartTransitionThirdDerivativeAt_cocycle
    (firstCenter secondCenter thirdCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (hThird : current ∈
      (extChartAt throatCoverModelWithCorners thirdCenter).source)
    (first second third : ThroatCoverCoordinates) :
    throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
        firstCenter thirdCenter current first second third =
      throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
          secondCenter thirdCenter current
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
            (extChartAt throatCoverModelWithCorners firstCenter current) third) +
        fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                secondCenter thirdCenter))
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
              (extChartAt throatCoverModelWithCorners firstCenter current)
              third) +
        fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                secondCenter thirdCenter))
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
              (extChartAt throatCoverModelWithCorners firstCenter current)
              second) +
        fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                secondCenter thirdCenter))
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
              (extChartAt throatCoverModelWithCorners firstCenter current)
              first) +
        fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              secondCenter thirdCenter)
            (extChartAt throatCoverModelWithCorners secondCenter current)
            (throatGaugeBaseChartTransitionThirdDerivativeAt period hPeriod
              firstCenter secondCenter current first second third) := by
  let firstToSecond :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let secondToThird :=
    throatGaugeBaseChartTransition period hPeriod secondCenter thirdCenter
  let firstToThird :=
    throatGaugeBaseChartTransition period hPeriod firstCenter thirdCenter
  let firstCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter current
  let secondCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter current
  have hFirstToSecond : ContDiffAt Real 3 firstToSecond firstCoordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hSecondToThird : ContDiffAt Real 3 secondToThird secondCoordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      secondCenter thirdCenter current hSecond hThird).of_le (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hAt : firstToSecond firstCoordinate = secondCoordinate := by
    simpa only [firstToSecond, firstCoordinate, secondCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        firstCenter secondCenter current hFirst
  have hSecondToThirdAtFirstToSecond :
      ContDiffAt Real 3 secondToThird (firstToSecond firstCoordinate) := by
    simpa only [hAt] using hSecondToThird
  have hGerm : firstToThird =ᶠ[𝓝 firstCoordinate]
      secondToThird ∘ firstToSecond := by
    simpa only [firstToThird, secondToThird, firstToSecond, firstCoordinate]
      using throatGaugeBaseChartTransition_cocycle_eventuallyEq period hPeriod
        firstCenter secondCenter thirdCenter current hFirst hSecond
  have hThirdDerivative :
      fderiv Real (fderiv Real (fderiv Real firstToThird)) firstCoordinate =
        fderiv Real
          (fderiv Real (fderiv Real (secondToThird ∘ firstToSecond)))
          firstCoordinate :=
    ((hGerm.fderiv (𝕜 := Real)).fderiv (𝕜 := Real)).fderiv_eq
  simp only [throatGaugeBaseChartTransitionThirdDerivativeAt]
  rw [show
    fderiv Real (fderiv Real (fderiv Real firstToThird)) firstCoordinate
          first second third =
        fderiv Real
            (fderiv Real (fderiv Real (secondToThird ∘ firstToSecond)))
            firstCoordinate first second third by
      exact congrArg
        (fun derivative : ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real]
              ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates =>
          derivative first second third) hThirdDerivative]
  rw [third_fderiv_comp_apply firstToSecond secondToThird firstCoordinate
    hFirstToSecond hSecondToThirdAtFirstToSecond, hAt]

end
end P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
end JanusFormal
