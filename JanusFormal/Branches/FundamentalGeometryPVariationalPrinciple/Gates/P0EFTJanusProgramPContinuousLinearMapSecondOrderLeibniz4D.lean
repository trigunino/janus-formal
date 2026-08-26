import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Second-order Leibniz rule for continuous-linear-map application

This gate isolates the ordinary real Frechet-calculus identity used when a
varying continuous linear map is applied to a varying vector.  The result is
evaluated in two directions to keep all tangent spaces fixed and explicit.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

set_option autoImplicit false

noncomputable section

open Filter Topology

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

/-- The second Frechet derivative of `x ↦ c x (u x)`, evaluated in two
directions, is the four-term second-order Leibniz formula. -/
theorem second_fderiv_clm_apply_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (c : X → Y →L[Real] Z) (u : X → Y)
    (point first second : X)
    (hC : ContDiffAt Real 2 c point)
    (hU : ContDiffAt Real 2 u point) :
    fderiv Real (fderiv Real (fun current ↦ c current (u current)))
        point first second =
      c point (fderiv Real (fderiv Real u) point first second) +
        fderiv Real c point first (fderiv Real u point second) +
        fderiv Real c point second (fderiv Real u point first) +
        fderiv Real (fun current ↦ fderiv Real c current second)
          point first (u point) := by
  have hCDifferentiable : DifferentiableAt Real c point :=
    hC.differentiableAt (by norm_num)
  have hUDifferentiable : DifferentiableAt Real u point :=
    hU.differentiableAt (by norm_num)
  have hCDerivative : DifferentiableAt Real (fderiv Real c) point :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hUDerivative : DifferentiableAt Real (fderiv Real u) point :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hProductDerivative : DifferentiableAt Real
      (fderiv Real (fun current ↦ c current (u current))) point :=
    ((hC.clm_apply hU).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hCEventually : ∀ᶠ current in 𝓝 point,
      DifferentiableAt Real c current := by
    filter_upwards [hC.eventually (by norm_num)] with current hCurrent
    exact hCurrent.differentiableAt (by norm_num)
  have hUEventually : ∀ᶠ current in 𝓝 point,
      DifferentiableAt Real u current := by
    filter_upwards [hU.eventually (by norm_num)] with current hCurrent
    exact hCurrent.differentiableAt (by norm_num)
  have hFirstFormula :
      (fun current ↦
        fderiv Real (fun base ↦ c base (u base)) current second) =ᶠ[𝓝 point]
        (fun current ↦
          c current (fderiv Real u current second) +
            fderiv Real c current second (u current)) := by
    filter_upwards [hCEventually, hUEventually] with current hCurrentC hCurrentU
    have hProduct := fderiv_clm_apply hCurrentC hCurrentU
    have hApplied := congrArg
      (fun derivative : X →L[Real] Z ↦ derivative second) hProduct
    simpa using hApplied
  have hFirstEvaluation :
      fderiv Real
          (fun current ↦
            fderiv Real (fun base ↦ c base (u base)) current second)
          point first =
        fderiv Real (fderiv Real (fun current ↦ c current (u current)))
          point first second :=
    fderiv_clm_apply_const_apply
      (field := fderiv Real (fun current ↦ c current (u current)))
      point first second hProductDerivative
  have hUSecond : DifferentiableAt Real
      (fun current ↦ fderiv Real u current second) point :=
    hUDerivative.clm_apply (differentiableAt_const (c := second))
  have hCSecond : DifferentiableAt Real
      (fun current ↦ fderiv Real c current second) point :=
    hCDerivative.clm_apply (differentiableAt_const (c := second))
  have hFirstTerm : DifferentiableAt Real
      (fun current ↦ c current (fderiv Real u current second)) point :=
    hCDifferentiable.clm_apply hUSecond
  have hSecondTerm : DifferentiableAt Real
      (fun current ↦ fderiv Real c current second (u current)) point :=
    hCSecond.clm_apply hUDifferentiable
  have hUSecondDerivative :
      fderiv Real (fun current ↦ fderiv Real u current second) point first =
        fderiv Real (fderiv Real u) point first second :=
    fderiv_clm_apply_const_apply (field := fderiv Real u)
      point first second hUDerivative
  have hFirstTermDerivative :
      fderiv Real
          (fun current ↦ c current (fderiv Real u current second))
          point first =
        c point (fderiv Real (fderiv Real u) point first second) +
          fderiv Real c point first (fderiv Real u point second) := by
    have hProduct := fderiv_clm_apply hCDifferentiable hUSecond
    have hApplied := congrArg
      (fun derivative : X →L[Real] Z ↦ derivative first) hProduct
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    rw [hUSecondDerivative] at hApplied
    exact hApplied
  have hSecondTermDerivative :
      fderiv Real
          (fun current ↦ fderiv Real c current second (u current))
          point first =
        fderiv Real c point second (fderiv Real u point first) +
          fderiv Real (fun current ↦ fderiv Real c current second)
            point first (u point) := by
    have hProduct := fderiv_clm_apply hCSecond hUDifferentiable
    have hApplied := congrArg
      (fun derivative : X →L[Real] Z ↦ derivative first) hProduct
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    exact hApplied
  calc
    fderiv Real (fderiv Real (fun current ↦ c current (u current)))
        point first second =
      fderiv Real
          (fun current ↦
            fderiv Real (fun base ↦ c base (u base)) current second)
          point first := hFirstEvaluation.symm
    _ = fderiv Real
          (fun current ↦
            c current (fderiv Real u current second) +
              fderiv Real c current second (u current))
          point first := by
      exact congrArg
        (fun derivative : X →L[Real] Z ↦ derivative first)
        hFirstFormula.fderiv_eq
    _ = fderiv Real
          (fun current ↦ c current (fderiv Real u current second))
          point first +
        fderiv Real
          (fun current ↦ fderiv Real c current second (u current))
          point first := by
      exact congrArg
        (fun derivative : X →L[Real] Z ↦ derivative first)
        (fderiv_add hFirstTerm hSecondTerm)
    _ = _ := by
      rw [hFirstTermDerivative, hSecondTermDerivative]
      abel

end
end P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D
end JanusFormal
