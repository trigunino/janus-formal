import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRelativeMetricProductFrechet

/-!
Fréchet chain from the plus metric itself to the relative square root.

At an invertible matrix, inversion has derivative
`δg ↦ -(g⁻¹ * δg * g⁻¹)`.  Composing it with multiplication gives the
variation of `gPlus⁻¹ * gMinus`; a supplied differentiable square-root
selection is then differentiated through a supplied Sylvester inverse.

No global Lorentzian or principal square-root branch is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMetricInverseRelativeRootFrechet

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusMatrixSquareRootFrechetSylvester

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

/-- Pointwise metric pair `(gPlus, gMinus)`. -/
abbrev MetricPair := Matrix4 × Matrix4

/-- Actual derivative of matrix inversion at `metric`. -/
def matrixInverseDerivative (metric : Matrix4) : Matrix4 →L[ℝ] Matrix4 :=
  -ContinuousLinearMap.mulLeftRight ℝ Matrix4 metric⁻¹ metric⁻¹

@[simp]
theorem matrixInverseDerivative_apply (metric variation : Matrix4) :
    matrixInverseDerivative metric variation =
      -(metric⁻¹ * variation * metric⁻¹) := by
  rfl

/-- Matrix inversion is Fréchet differentiable at every invertible metric,
with the standard noncommutative derivative. -/
theorem matrixInverse_hasFDerivAt
    (metric : Matrix4) (hMetric : IsUnit metric) :
    HasFDerivAt (fun point : Matrix4 => point⁻¹)
      (matrixInverseDerivative metric) metric := by
  obtain ⟨unit, rfl⟩ := hMetric
  convert (hasFDerivAt_ringInverse (𝕜 := ℝ) unit) using 1
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext point
    exact Matrix.nonsing_inv_eq_ringInverse point
  · rename_i hAdd hModule hTopology
    cases hAdd
    cases hModule
    cases hTopology
    simp only [matrixInverseDerivative,
      Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
    apply HEq.rfl

theorem matrixInverse_fderiv
    (metric : Matrix4) (hMetric : IsUnit metric) :
    fderiv ℝ (fun point : Matrix4 => point⁻¹) metric =
      matrixInverseDerivative metric :=
  (matrixInverse_hasFDerivAt metric hMetric).fderiv

/-- Relative metric formed from the two metrics themselves. -/
def relativeMetricTarget (input : MetricPair) : Matrix4 :=
  input.1⁻¹ * input.2

/-- Chain-rule derivative of `(gPlus, gMinus) ↦ gPlus⁻¹ * gMinus`. -/
def relativeMetricDerivative
    (input : MetricPair) : MetricPair →L[ℝ] Matrix4 :=
  ((ContinuousLinearMap.mul ℝ Matrix4).flip input.2).comp
      ((matrixInverseDerivative input.1).comp
        (ContinuousLinearMap.fst ℝ Matrix4 Matrix4)) +
    ((ContinuousLinearMap.mul ℝ Matrix4) input.1⁻¹).comp
      (ContinuousLinearMap.snd ℝ Matrix4 Matrix4)

@[simp]
theorem relativeMetricDerivative_apply
    (input variation : MetricPair) :
    relativeMetricDerivative input variation =
      -(input.1⁻¹ * variation.1 * input.1⁻¹) * input.2 +
        input.1⁻¹ * variation.2 := by
  rfl

theorem relativeMetricTarget_hasFDerivAt
    (input : MetricPair) (hPlus : IsUnit input.1) :
    HasFDerivAt relativeMetricTarget (relativeMetricDerivative input) input := by
  have hFirst : HasFDerivAt (fun point : MetricPair => point.1)
      (ContinuousLinearMap.fst ℝ Matrix4 Matrix4) input :=
    (ContinuousLinearMap.fst ℝ Matrix4 Matrix4).hasFDerivAt
  have hInverse :
      HasFDerivAt (fun point : MetricPair => point.1⁻¹)
        ((matrixInverseDerivative input.1).comp
          (ContinuousLinearMap.fst ℝ Matrix4 Matrix4)) input :=
    (matrixInverse_hasFDerivAt input.1 hPlus).comp input hFirst
  have hSecond : HasFDerivAt (fun point : MetricPair => point.2)
      (ContinuousLinearMap.snd ℝ Matrix4 Matrix4) input :=
    (ContinuousLinearMap.snd ℝ Matrix4 Matrix4).hasFDerivAt
  have hProduct := hInverse.mul' hSecond
  refine hProduct.congr_fderiv ?_
  exact add_comm _ _

theorem relativeMetricTarget_fderiv
    (input : MetricPair) (hPlus : IsUnit input.1) :
    fderiv ℝ relativeMetricTarget input = relativeMetricDerivative input :=
  (relativeMetricTarget_hasFDerivAt input hPlus).fderiv

/-- Conditional local derivative of a supplied differentiable selection
`X² = gPlus⁻¹ * gMinus`. -/
theorem relativeSquareRoot_hasFDerivAt
    (root : MetricPair → Matrix4)
    (input : MetricPair)
    (hPlus : IsUnit input.1)
    (witness : SylvesterInverseWitness (root input))
    (hRoot : DifferentiableAt ℝ root input)
    (hSquare : ∀ point,
      squareMap (root point) = relativeMetricTarget point) :
    HasFDerivAt root
      (witness.inverse.comp (relativeMetricDerivative input)) input := by
  exact differentiable_squareRoot_hasFDerivAt witness hRoot
    (relativeMetricTarget_hasFDerivAt input hPlus) hSquare

theorem relativeSquareRoot_fderiv
    (root : MetricPair → Matrix4)
    (input : MetricPair)
    (hPlus : IsUnit input.1)
    (witness : SylvesterInverseWitness (root input))
    (hRoot : DifferentiableAt ℝ root input)
    (hSquare : ∀ point,
      squareMap (root point) = relativeMetricTarget point) :
    fderiv ℝ root input =
      witness.inverse.comp (relativeMetricDerivative input) :=
  (relativeSquareRoot_hasFDerivAt root input hPlus witness hRoot hSquare).fderiv

/- Invertibility of `gPlus`, differentiability of the selected root and a
Sylvester inverse remain explicit local hypotheses. -/

end

end P0EFTJanusMetricInverseRelativeRootFrechet
end JanusFormal
