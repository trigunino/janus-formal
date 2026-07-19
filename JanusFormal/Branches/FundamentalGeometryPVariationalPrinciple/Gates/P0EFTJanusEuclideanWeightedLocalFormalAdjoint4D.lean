import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Local weighted formal adjoint in a Euclidean chart

This gate isolates the analytic integration-by-parts identity needed in one
coordinate direction.  A compactly supported smooth test absorbs both the
smooth density and the smooth coordinate coefficient of a vector field.
-/

namespace JanusFormal
namespace P0EFTJanusEuclideanWeightedLocalFormalAdjoint4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E]

/-- Coordinate expression for the formal adjoint of `coefficient * D_direction`
in the measure `density * volume`. -/
def weightedCoordinateFormalAdjoint
    (direction : E) (test density coefficient : E -> Real) (point : E) : Real :=
  -(density point)⁻¹ *
    fderiv Real
      (fun point => density point * coefficient point * test point)
      point direction

/-- In one fixed chart direction, the adjoint of a weighted directional
derivative is the negative derivative of the density-weighted test
coefficient.  Compact support of the test removes the boundary term. -/
theorem integral_weighted_fderiv_eq_formalAdjoint
    (direction : E)
    (field test density coefficient : E -> Real)
    (hField : ContDiff Real ∞ field)
    (hTest : ContDiff Real ∞ test)
    (hDensity : ContDiff Real ∞ density)
    (hCoefficient : ContDiff Real ∞ coefficient)
    (hTestCompact : HasCompactSupport test) :
    (∫ point,
        (density point * coefficient point * test point) *
          fderiv Real field point direction ∂Measure.addHaar) =
      -∫ point,
        fderiv Real
            (fun point => density point * coefficient point * test point)
            point direction * field point ∂Measure.addHaar := by
  let weightedTest : E -> Real := fun point =>
    density point * coefficient point * test point
  have hWeightedTest : ContDiff Real ∞ weightedTest :=
    (hDensity.mul hCoefficient).mul hTest
  have hWeightedTestCompact : HasCompactSupport weightedTest := by
    exact hTestCompact.mul_left
  have hDerivativeWeightedTest : Continuous (fun point =>
      fderiv Real weightedTest point direction) :=
    (hWeightedTest.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDerivativeField : Continuous (fun point =>
      fderiv Real field point direction) :=
    (hField.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDerivativeWeightedTestCompact : HasCompactSupport (fun point =>
      fderiv Real weightedTest point direction) :=
    hWeightedTestCompact.fderiv_apply Real direction
  have hLeftIntegrable : Integrable (fun point =>
      fderiv Real weightedTest point direction * field point) Measure.addHaar :=
    (hDerivativeWeightedTest.mul hField.continuous).integrable_of_hasCompactSupport
      hDerivativeWeightedTestCompact.mul_right
  have hRightIntegrable : Integrable (fun point =>
      weightedTest point * fderiv Real field point direction) Measure.addHaar :=
    (hWeightedTest.continuous.mul hDerivativeField).integrable_of_hasCompactSupport
      hWeightedTestCompact.mul_right
  have hProductIntegrable : Integrable (fun point =>
      weightedTest point * field point) Measure.addHaar :=
    (hWeightedTest.continuous.mul hField.continuous).integrable_of_hasCompactSupport
      hWeightedTestCompact.mul_right
  simpa only [weightedTest] using
    (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := Measure.addHaar) hLeftIntegrable hRightIntegrable hProductIntegrable
      (fun point _ => hWeightedTest.differentiable (by simp) point)
      (fun point _ => hField.differentiable (by simp) point))

/-- The same identity written in the weighted measure pairing.  Nonvanishing
of the density is exactly what permits division by it in the local adjoint. -/
theorem integral_weighted_fderiv_eq_weighted_formalAdjoint
    (direction : E)
    (field test density coefficient : E -> Real)
    (hField : ContDiff Real ∞ field)
    (hTest : ContDiff Real ∞ test)
    (hDensity : ContDiff Real ∞ density)
    (hCoefficient : ContDiff Real ∞ coefficient)
    (hTestCompact : HasCompactSupport test)
    (hDensityNonzero : ∀ point, density point ≠ 0) :
    (∫ point,
        (density point * coefficient point * test point) *
          fderiv Real field point direction ∂Measure.addHaar) =
      ∫ point,
        density point * field point *
          weightedCoordinateFormalAdjoint direction test density coefficient point
        ∂Measure.addHaar := by
  calc
    (∫ point,
        (density point * coefficient point * test point) *
          fderiv Real field point direction ∂Measure.addHaar) =
        -∫ point,
          fderiv Real
              (fun point => density point * coefficient point * test point)
              point direction * field point ∂Measure.addHaar :=
      integral_weighted_fderiv_eq_formalAdjoint direction field test density coefficient
        hField hTest hDensity hCoefficient hTestCompact
    _ = ∫ point,
        -(fderiv Real
            (fun point => density point * coefficient point * test point)
            point direction * field point) ∂Measure.addHaar := by
      rw [integral_neg]
    _ = ∫ point,
        density point * field point *
          weightedCoordinateFormalAdjoint direction test density coefficient point
        ∂Measure.addHaar := by
      apply integral_congr_ae
      filter_upwards
      intro point
      simp only [weightedCoordinateFormalAdjoint]
      field_simp [hDensityNonzero point]

end

end P0EFTJanusEuclideanWeightedLocalFormalAdjoint4D
end JanusFormal
