import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring

/-! Differentiation of a reconstructed moving tangent.  The derivative of the
source vector field is retained; only a normal covector can remove it. -/
namespace JanusFormal.P0EFTJanusProgramPT12MovingFrameAccelerationCalculus4D
set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
  [NormedAddCommGroup Y] [NormedSpace Real Y]
  {ι : Type*} [Fintype ι]

/-- Reconstructing finite connection coefficients commutes with the two
tangent contractions, including for a redundant spanning family. -/
theorem movingFrameAcceleration_rearrange
    (derivative first second : ι → Real) (connection : ι → ι → ι → Real)
    (frame : ι → Y) :
    (∑ a, (derivative a + ∑ b, ∑ c, connection a b c * first b * second c) • frame a) =
      (∑ a, derivative a • frame a) +
        ∑ b, ∑ c, (first b * second c) • (∑ a, connection a b c • frame a) := by
  simp only [add_smul, Finset.sum_add_distrib, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  ring

/-- Product and chain rules for an actual local frame reconstruction. -/
theorem movingFrameDerivative_eq_hessian_add_sourceDerivative
    (F : X → Y) (v : X → X) (coefficient : ι → X → Real) (frame : ι → Y → Y)
    (x u : X) (hF : DifferentiableAt Real F x)
    (hDF : DifferentiableAt Real (fderiv Real F) x)
    (hv : DifferentiableAt Real v x)
    (hCoefficient : ∀ a, DifferentiableAt Real (coefficient a) x)
    (hFrame : ∀ a, DifferentiableAt Real (frame a) (F x))
    (hReconstruct : (fun y => ∑ a, coefficient a y • frame a (F y)) =ᶠ[𝓝 x]
      (fun y => fderiv Real F y (v y))) :
    (∑ a, (fderiv Real (coefficient a) x u • frame a (F x) +
      coefficient a x • fderiv Real (frame a) (F x) (fderiv Real F x u))) =
      fderiv Real (fderiv Real F) x u (v x) + fderiv Real F x (fderiv Real v x u) := by
  have hTerm (a : ι) : DifferentiableAt Real
      (fun y => coefficient a y • frame a (F y)) x :=
    (hCoefficient a).smul ((hFrame a).comp x hF)
  have hLeft : fderiv Real (fun y => ∑ a, coefficient a y • frame a (F y)) x u =
      ∑ a, (fderiv Real (coefficient a) x u • frame a (F x) +
        coefficient a x • fderiv Real (frame a) (F x) (fderiv Real F x u)) := by
    rw [fderiv_fun_sum (fun a _ => hTerm a)]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    have hProduct := (hCoefficient a).hasFDerivAt.smul
      ((hFrame a).hasFDerivAt.comp x hF.hasFDerivAt)
    have hApply := congrArg (fun L : X →L[Real] Y => L u) hProduct.fderiv
    simpa only [Function.comp_def, Pi.smul_def', add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, add_comm] using hApply
  have hRight : fderiv Real (fun y => fderiv Real F y (v y)) x u =
      fderiv Real (fderiv Real F) x u (v x) + fderiv Real F x (fderiv Real v x u) := by
    rw [fderiv_clm_apply hDF hv]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    exact add_comm _ _
  exact hLeft.symm.trans ((congrArg (fun L : X →L[Real] Y => L u)
    hReconstruct.fderiv_eq).trans hRight)

/-- Adding the genuine coordinate connection leaves precisely the tangential
source-generator correction.  No coordinate vector is treated as constant. -/
theorem movingFrameCovariantAcceleration_eq_holonomic_add_sourceDerivative
    (F : X → Y) (v : X → X) (coefficient : ι → X → Real) (frame : ι → Y → Y)
    (connection : Y →L[Real] Y →L[Real] Y)
    (x u : X) (hF : DifferentiableAt Real F x)
    (hDF : DifferentiableAt Real (fderiv Real F) x)
    (hv : DifferentiableAt Real v x)
    (hCoefficient : ∀ a, DifferentiableAt Real (coefficient a) x)
    (hFrame : ∀ a, DifferentiableAt Real (frame a) (F x))
    (hReconstruct : (fun y => ∑ a, coefficient a y • frame a (F y)) =ᶠ[𝓝 x]
      (fun y => fderiv Real F y (v y))) :
    (∑ a, (fderiv Real (coefficient a) x u • frame a (F x) +
      coefficient a x • fderiv Real (frame a) (F x) (fderiv Real F x u))) +
        connection (fderiv Real F x u) (fderiv Real F x (v x)) =
      (fderiv Real (fderiv Real F) x u (v x) +
        connection (fderiv Real F x u) (fderiv Real F x (v x))) +
          fderiv Real F x (fderiv Real v x u) := by
  rw [movingFrameDerivative_eq_hessian_add_sourceDerivative F v coefficient frame x u
    hF hDF hv hCoefficient hFrame hReconstruct]
  exact add_right_comm _ _ _

/-- The extra term vanishes only after contraction by an orthogonal covector. -/
theorem normalContraction_add_sourceDerivative
    (F : X → Y) (v : X → X) (x u : X) (acceleration : Y) (normal : Y →L[Real] Real)
    (hNormal : ∀ tangent : X, normal (fderiv Real F x tangent) = 0) :
    normal (acceleration + fderiv Real F x (fderiv Real v x u)) = normal acceleration := by
  rw [map_add, hNormal, add_zero]

end
end JanusFormal.P0EFTJanusProgramPT12MovingFrameAccelerationCalculus4D
