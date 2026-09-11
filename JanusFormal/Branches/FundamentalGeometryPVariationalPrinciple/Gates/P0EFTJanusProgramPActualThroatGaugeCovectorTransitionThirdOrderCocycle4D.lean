import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D

/-!
# Third-order cocycle for the actual throat gauge covector transition

The existing local frame/base transition germ is differentiated three times.
The result is the full fifteen-term chain--Leibniz formula: eight terms come
from differentiating composition of the two varying fiber maps, and the
derivatives of the pulled-back second map are expanded through the actual
base-chart transition.

This is coefficient-level third-order descent data.  No third-jet quotient or
global bundle descent is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdOrderCocycle4D

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
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdDerivative4D
open P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeBase := ThroatCoverCoordinates

private abbrev GaugeFiber :=
  FramedCovector ThroatCoverCoordinates

private abbrev CovectorEnd :=
  GaugeFiber →L[Real] GaugeFiber

local instance covectorEndNormedAddCommGroup :
    NormedAddCommGroup CovectorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorEndNormedSpace : NormedSpace Real CovectorEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev GaugeFirstDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeFiber

local instance gaugeFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeFirstDerivativeNormedSpace :
    NormedSpace Real GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev GaugeSecondDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeFirstDerivative

local instance gaugeSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeSecondDerivativeNormedSpace :
    NormedSpace Real GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorEnd

local instance covectorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionSecondDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorTransitionFirstDerivative

local instance covectorTransitionSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionSecondDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionThirdDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorTransitionSecondDerivative

local instance covectorTransitionThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionThirdDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionThirdDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionThirdDerivative :=
  ContinuousLinearMap.toNormedSpace

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

private theorem third_fderiv_clm_apply_const_apply
    (field : GaugeBase → CovectorEnd)
    (point first second third : GaugeBase)
    (value : GaugeFiber) (hField : ContDiffAt Real 3 field point) :
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
      hSecondField.clm_apply (differentiableAt_const (c := second))
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
          (fun derivative : GaugeBase →L[Real] GaugeFiber =>
            derivative first)
          hSecondFormula.fderiv_eq
    _ = fderiv Real
        (fun current =>
          fderiv Real (fderiv Real field) current second third)
        point first value := hRightOuter
    _ = fderiv Real (fderiv Real (fderiv Real field))
        point first second third value := by
      exact congrArg (fun derivative : CovectorEnd => derivative value)
        hRightInner

/-- Third-order Leibniz rule for a varying continuous linear map applied to a
varying vector. -/
private theorem third_fderiv_clm_apply_apply
    (c : GaugeBase → CovectorEnd) (u : GaugeBase → GaugeFiber)
    (point first second third : GaugeBase)
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
  let uFirstAtSecond : GaugeBase → GaugeFiber :=
    fun current => fderiv Real u current second
  let uFirstAtThird : GaugeBase → GaugeFiber :=
    fun current => fderiv Real u current third
  let uSecondAtSecondThird : GaugeBase → GaugeFiber :=
    fun current => fderiv Real (fderiv Real u) current second third
  let cFirstAtSecond : GaugeBase → CovectorEnd :=
    fun current => fderiv Real c current second
  let cFirstAtThird : GaugeBase → CovectorEnd :=
    fun current => fderiv Real c current third
  let cSecondAtSecondThird : GaugeBase → CovectorEnd :=
    fun current => fderiv Real (fderiv Real c) current second third
  let termZero : GaugeBase → GaugeFiber :=
    fun current => c current (uSecondAtSecondThird current)
  let termOne : GaugeBase → GaugeFiber :=
    fun current => cFirstAtSecond current (uFirstAtThird current)
  let termTwo : GaugeBase → GaugeFiber :=
    fun current => cFirstAtThird current (uFirstAtSecond current)
  let termThree : GaugeBase → GaugeFiber :=
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
      hCSecondDerivative.clm_apply (differentiableAt_const (c := second))
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
      (fun derivative : GaugeFirstDerivative => derivative first) hProduct
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
      (fun derivative : GaugeFirstDerivative => derivative first) hProduct
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
      (fun derivative : GaugeFirstDerivative => derivative first) hProduct
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
      (fun derivative : GaugeFirstDerivative => derivative first) hProduct
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
            (fun derivative : GaugeFirstDerivative => derivative first)
            hSecondFormula.fderiv_eq
    _ = _ := hRightDerivative

/-- Third derivative of pointwise composition of two varying continuous
linear maps, evaluated on a fixed vector. -/
private theorem third_fderiv_clm_comp_apply_raw
    (outer inner : GaugeBase → CovectorEnd)
    (point first second third : GaugeBase) (value : GaugeFiber)
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
  have hInnerFirst (direction : GaugeBase) :
      fderiv Real evaluatedInner point direction =
        fderiv Real inner point direction value := by
    simpa only [evaluatedInner] using
      fderiv_continuousLinearMap_apply_const inner point direction value
        (hInner.differentiableAt (by norm_num))
  have hInnerSecond (firstDirection secondDirection : GaugeBase) :
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
private theorem third_fderiv_semidirect_comp_apply
    (base : GaugeBase → GaugeBase)
    (outer inner : GaugeBase → CovectorEnd)
    (point first second third : GaugeBase) (value : GaugeFiber)
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
  have hPulledFirst (direction : GaugeBase) :
      fderiv Real pulledOuter point direction =
        fderiv Real outer (base point)
          (fderiv Real base point direction) := by
    have hChain := fderiv_comp point
      (hOuter.differentiableAt (by norm_num))
      (hBase.differentiableAt (by norm_num))
    have hApplied := congrArg
      (fun derivative : CovectorTransitionFirstDerivative =>
        derivative direction) hChain
    simpa only [pulledOuter, ContinuousLinearMap.comp_apply] using hApplied
  have hPulledSecond
      (firstDirection secondDirection : GaugeBase) :
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

/-! ## Actual third-order frame/base cocycle -/

/-- On a common triple overlap, the third derivative of the actual varying
covector transition obeys the complete fifteen-term composition formula. -/
theorem throatGaugeFrameBaseChartTransition_thirdDerivative_cocycle_apply
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
    (covector : FramedCovector ThroatCoverCoordinates) :
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
    fderiv Real (fderiv Real (fderiv Real directTransition))
        firstCoordinate first second third covector =
      secondTransition secondCoordinate
          (fderiv Real (fderiv Real (fderiv Real firstTransition))
            firstCoordinate first second third covector) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate second third covector) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate first third covector) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real (fderiv Real firstTransition)
            firstCoordinate first second covector) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real firstTransition firstCoordinate third covector) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first second)
          (fderiv Real firstTransition firstCoordinate third covector) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real firstTransition firstCoordinate second covector) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first third)
          (fderiv Real firstTransition firstCoordinate second covector) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real baseTransition firstCoordinate third)
          (fderiv Real firstTransition firstCoordinate first covector) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate second third)
          (fderiv Real firstTransition firstCoordinate first covector) +
        fderiv Real (fderiv Real (fderiv Real secondTransition))
          secondCoordinate
          (fderiv Real baseTransition firstCoordinate first)
          (fderiv Real baseTransition firstCoordinate second)
          (fderiv Real baseTransition firstCoordinate third)
          (firstTransition firstCoordinate covector) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first second)
          (fderiv Real baseTransition firstCoordinate third)
          (firstTransition firstCoordinate covector) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate first third)
          (fderiv Real baseTransition firstCoordinate second)
          (firstTransition firstCoordinate covector) +
        fderiv Real (fderiv Real secondTransition) secondCoordinate
          (fderiv Real (fderiv Real baseTransition)
            firstCoordinate second third)
          (fderiv Real baseTransition firstCoordinate first)
          (firstTransition firstCoordinate covector) +
        fderiv Real secondTransition secondCoordinate
          (fderiv Real (fderiv Real (fderiv Real baseTransition))
            firstCoordinate first second third)
          (firstTransition firstCoordinate covector) := by
  dsimp only
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
  have hBase : ContDiffAt Real 3 baseTransition firstCoordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond).of_le (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hFirstTransition : ContDiffAt Real 3 firstTransition firstCoordinate :=
    (throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
      period hPeriod firstAnchor secondAnchor firstCenter current
        ⟨hCurrent.1, hCurrent.2.1⟩ hFirst).of_le (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hSecondTransition :
      ContDiffAt Real 3 secondTransition secondCoordinate :=
    (throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
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
    have hCombined := throatGaugeFrameBaseChartTransition_cocycle_eventuallyEq
      period hPeriod firstAnchor secondAnchor thirdAnchor firstCenter
        secondCenter secondCenter current hCurrent hFirst hSecond
    exact hCombined.fun_comp Prod.snd
  have hFirstDerivativeGerm := hGerm.fderiv (𝕜 := Real)
  have hSecondDerivativeGerm := hFirstDerivativeGerm.fderiv (𝕜 := Real)
  have hThirdDerivativeGerm :=
    hSecondDerivativeGerm.fderiv_eq (𝕜 := Real)
  have hGermApplied := congrArg
    (fun derivative : CovectorTransitionThirdDerivative =>
      derivative first second third covector)
    hThirdDerivativeGerm
  have hFormula := third_fderiv_semidirect_comp_apply
    baseTransition secondTransition firstTransition firstCoordinate
      first second third covector hBase hSecondAt hFirstTransition
  rw [hGermApplied]
  rw [hAt] at hFormula
  simpa only [baseTransition, firstTransition, secondTransition,
    directTransition, firstCoordinate, secondCoordinate] using hFormula

end
end P0EFTJanusProgramPActualThroatGaugeCovectorTransitionThirdOrderCocycle4D
end JanusFormal
