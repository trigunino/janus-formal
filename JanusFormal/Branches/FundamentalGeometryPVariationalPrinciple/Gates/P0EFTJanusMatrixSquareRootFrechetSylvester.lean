import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootInteractionDensity

/-!
Fréchet gate for the pointwise matrix square-root equation.  The derivative
of `X ↦ X * X` is the Sylvester operator `H ↦ X * H + H * X`.  A supplied
continuous-linear two-sided inverse then determines the derivative of any
already differentiable square-root selection.

No inverse is constructed here, and no existence or smoothness of a
principal Lorentzian square-root branch is inferred.
-/

namespace JanusFormal
namespace P0EFTJanusMatrixSquareRootFrechetSylvester

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

/-- The pointwise matrix squaring map whose inverse would select a square
root branch. -/
def squareMap (root : Matrix4) : Matrix4 :=
  root * root

/-- The Sylvester operators form one continuous-linear family in their base
matrix. -/
def sylvesterFamily : Matrix4 →L[ℝ] Matrix4 →L[ℝ] Matrix4 :=
  ContinuousLinearMap.mul ℝ Matrix4 +
    (ContinuousLinearMap.mul ℝ Matrix4).flip

/-- Linearization of `squareMap` at `root`. -/
def sylvesterOperator (root : Matrix4) : Matrix4 →L[ℝ] Matrix4 :=
  sylvesterFamily root

@[simp]
theorem sylvesterOperator_apply (root variation : Matrix4) :
    sylvesterOperator root variation =
      root * variation + variation * root := by
  rfl

/-- The actual Fréchet derivative of matrix squaring is the Sylvester
operator. -/
theorem squareMap_hasFDerivAt (root : Matrix4) :
    HasFDerivAt squareMap (sylvesterOperator root) root := by
  have hIdentity :
      HasFDerivAt (fun point : Matrix4 => point)
        (ContinuousLinearMap.id ℝ Matrix4) root :=
    hasFDerivAt_id root
  have hProduct := hIdentity.mul' hIdentity
  refine hProduct.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro variation
  rfl

theorem squareMap_fderiv (root : Matrix4) :
    fderiv ℝ squareMap root = sylvesterOperator root :=
  (squareMap_hasFDerivAt root).fderiv

/-- The derivative field of `squareMap` is itself differentiable. -/
theorem squareMap_fderiv_hasFDerivAt (root : Matrix4) :
    HasFDerivAt (fun point => fderiv ℝ squareMap point)
      sylvesterFamily root := by
  have hFunctions :
      (fun point => fderiv ℝ squareMap point) = sylvesterOperator := by
    funext point
    exact squareMap_fderiv point
  rw [hFunctions]
  exact sylvesterFamily.hasFDerivAt

/-- The genuine second Fréchet derivative of matrix squaring is the constant
bilinear Sylvester family. -/
theorem squareMap_second_fderiv (root : Matrix4) :
    fderiv ℝ (fun point => fderiv ℝ squareMap point) root =
      sylvesterFamily :=
  (squareMap_fderiv_hasFDerivAt root).fderiv

theorem squareMap_second_fderiv_apply
    (root first second : Matrix4) :
    fderiv ℝ (fun point => fderiv ℝ squareMap point) root first second =
      first * second + second * first := by
  rw [squareMap_second_fderiv]
  rfl

/-- Explicit data required to invert the Sylvester equation at one supplied
root.  Both inverse laws are fields, rather than an existence claim. -/
structure SylvesterInverseWitness (root : Matrix4) where
  inverse : Matrix4 →L[ℝ] Matrix4
  leftInverse : ∀ variation,
    inverse (sylvesterOperator root variation) = variation
  rightInverse : ∀ variation,
    sylvesterOperator root (inverse variation) = variation

theorem inverse_comp_sylvester
    (root : Matrix4) (witness : SylvesterInverseWitness root) :
    witness.inverse.comp (sylvesterOperator root) =
      ContinuousLinearMap.id ℝ Matrix4 := by
  apply ContinuousLinearMap.ext
  intro variation
  exact witness.leftInverse variation

theorem sylvester_comp_inverse
    (root : Matrix4) (witness : SylvesterInverseWitness root) :
    (sylvesterOperator root).comp witness.inverse =
      ContinuousLinearMap.id ℝ Matrix4 := by
  apply ContinuousLinearMap.ext
  intro variation
  exact witness.rightInverse variation

/-- Differentiating a supplied square-root equation gives the exact
Sylvester equation for its derivative. -/
theorem squareRoot_derivative_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {root target : E → Matrix4}
    {rootDerivative targetDerivative : E →L[ℝ] Matrix4}
    {point : E}
    (hRoot : HasFDerivAt root rootDerivative point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : ∀ x, squareMap (root x) = target x) :
    (sylvesterOperator (root point)).comp rootDerivative =
      targetDerivative := by
  have hComposite :
      HasFDerivAt (fun x => squareMap (root x))
        ((sylvesterOperator (root point)).comp rootDerivative) point :=
    (squareMap_hasFDerivAt (root point)).comp point hRoot
  have hFunctions : (fun x => squareMap (root x)) = target := by
    funext x
    exact hSquare x
  rw [hFunctions] at hComposite
  exact hComposite.unique hTarget

/-- A supplied Sylvester inverse solves the differentiated square-root
equation. -/
theorem rootDerivative_eq_inverse_comp_targetDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {root target : E → Matrix4}
    {rootDerivative targetDerivative : E →L[ℝ] Matrix4}
    {point : E}
    (witness : SylvesterInverseWitness (root point))
    (hRoot : HasFDerivAt root rootDerivative point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : ∀ x, squareMap (root x) = target x) :
    rootDerivative = witness.inverse.comp targetDerivative := by
  have hEquation :=
    squareRoot_derivative_equation hRoot hTarget hSquare
  apply ContinuousLinearMap.ext
  intro direction
  calc
    rootDerivative direction =
        witness.inverse
          (sylvesterOperator (root point) (rootDerivative direction)) :=
      (witness.leftInverse (rootDerivative direction)).symm
    _ = witness.inverse
          (((sylvesterOperator (root point)).comp rootDerivative) direction) := by
      rfl
    _ = witness.inverse (targetDerivative direction) := by
      rw [hEquation]
    _ = (witness.inverse.comp targetDerivative) direction := by
      rfl

/-- Conditional local derivative formula for an already differentiable
square-root selection of a differentiable target map. -/
theorem differentiable_squareRoot_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {root target : E → Matrix4}
    {targetDerivative : E →L[ℝ] Matrix4}
    {point : E}
    (witness : SylvesterInverseWitness (root point))
    (hRoot : DifferentiableAt ℝ root point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : ∀ x, squareMap (root x) = target x) :
    HasFDerivAt root (witness.inverse.comp targetDerivative) point := by
  have hActual := hRoot.hasFDerivAt
  exact hActual.congr_fderiv
    (rootDerivative_eq_inverse_comp_targetDerivative witness hActual
      hTarget hSquare)

theorem differentiable_squareRoot_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {root target : E → Matrix4}
    {targetDerivative : E →L[ℝ] Matrix4}
    {point : E}
    (witness : SylvesterInverseWitness (root point))
    (hRoot : DifferentiableAt ℝ root point)
    (hTarget : HasFDerivAt target targetDerivative point)
    (hSquare : ∀ x, squareMap (root x) = target x) :
    fderiv ℝ root point = witness.inverse.comp targetDerivative :=
  (differentiable_squareRoot_hasFDerivAt witness hRoot hTarget hSquare).fderiv

/- This gate does not assert that a Sylvester inverse exists, that a selected
root branch is nonempty, or that such a branch is differentiable. -/

end

end P0EFTJanusMatrixSquareRootFrechetSylvester
end JanusFormal
