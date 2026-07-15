import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootFrechetSylvester

/-!
Actual pointwise variation of the relative-metric target
`A = g_plus_inverse * g_minus`, followed by the conditional Sylvester formula
for a supplied differentiable square-root selection.

The inverse plus metric is an independent input in this gate.  Deriving its
variation from `g_plus` and globalizing the Lorentzian branch remain open.
-/

namespace JanusFormal
namespace P0EFTJanusRelativeMetricProductFrechet

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusMatrixSquareRootFrechetSylvester

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

/-- `(g_plus_inverse, g_minus)` at one point. -/
abbrev RelativeMetricInput := Matrix4 × Matrix4

def relativeMetricTarget (input : RelativeMetricInput) : Matrix4 :=
  input.1 * input.2

def relativeMetricDerivative
    (input : RelativeMetricInput) : RelativeMetricInput →L[ℝ] Matrix4 :=
  ((ContinuousLinearMap.mul ℝ Matrix4).flip input.2).comp
      (ContinuousLinearMap.fst ℝ Matrix4 Matrix4) +
    ((ContinuousLinearMap.mul ℝ Matrix4) input.1).comp
      (ContinuousLinearMap.snd ℝ Matrix4 Matrix4)

@[simp]
theorem relativeMetricDerivative_apply
    (input variation : RelativeMetricInput) :
    relativeMetricDerivative input variation =
      variation.1 * input.2 + input.1 * variation.2 := by
  rfl

theorem relativeMetricTarget_hasFDerivAt (input : RelativeMetricInput) :
    HasFDerivAt relativeMetricTarget (relativeMetricDerivative input) input := by
  have hFirst : HasFDerivAt (fun point : RelativeMetricInput => point.1)
      (ContinuousLinearMap.fst ℝ Matrix4 Matrix4) input :=
    (ContinuousLinearMap.fst ℝ Matrix4 Matrix4).hasFDerivAt
  have hSecond : HasFDerivAt (fun point : RelativeMetricInput => point.2)
      (ContinuousLinearMap.snd ℝ Matrix4 Matrix4) input :=
    (ContinuousLinearMap.snd ℝ Matrix4 Matrix4).hasFDerivAt
  have hProduct := hFirst.mul' hSecond
  refine hProduct.congr_fderiv ?_
  exact add_comm _ _

theorem relativeMetricTarget_fderiv (input : RelativeMetricInput) :
    fderiv ℝ relativeMetricTarget input = relativeMetricDerivative input :=
  (relativeMetricTarget_hasFDerivAt input).fderiv

/-- Conditional derivative of a differentiable selection
`X² = g_plus_inverse * g_minus`. -/
theorem relativeSquareRoot_hasFDerivAt
    (root : RelativeMetricInput → Matrix4)
    (input : RelativeMetricInput)
    (witness : SylvesterInverseWitness (root input))
    (hRoot : DifferentiableAt ℝ root input)
    (hSquare : ∀ point,
      squareMap (root point) = relativeMetricTarget point) :
    HasFDerivAt root
      (witness.inverse.comp (relativeMetricDerivative input)) input := by
  exact differentiable_squareRoot_hasFDerivAt witness hRoot
    (relativeMetricTarget_hasFDerivAt input) hSquare

theorem relativeSquareRoot_fderiv
    (root : RelativeMetricInput → Matrix4)
    (input : RelativeMetricInput)
    (witness : SylvesterInverseWitness (root input))
    (hRoot : DifferentiableAt ℝ root input)
    (hSquare : ∀ point,
      squareMap (root point) = relativeMetricTarget point) :
    fderiv ℝ root input =
      witness.inverse.comp (relativeMetricDerivative input) :=
  (relativeSquareRoot_hasFDerivAt root input witness hRoot hSquare).fderiv

/- No derivative of matrix inversion, Sylvester invertibility theorem, branch
existence or spacetime covariance is inferred. -/

end

end P0EFTJanusRelativeMetricProductFrechet
end JanusFormal
