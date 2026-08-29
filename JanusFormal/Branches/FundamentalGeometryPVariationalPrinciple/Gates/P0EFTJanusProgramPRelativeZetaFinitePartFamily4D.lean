import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-!
# Family comparison between the zeta connection and finite-part metric

A pointwise real-part comparison identifies the norm of the complex zeta
determinant with the finite-part determinant.  Differentiating that comparison
identifies the real part of the zeta connection coefficient with the logarithmic
variation of the Quillen metric.

The imaginary part remains the unitary phase/eta connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-- Compatibility of one finite-part family with one complex zeta family. -/
structure RelativeZetaFinitePartFamilyComparisonData where
  finitePartFamily : RelativeHeatFinitePartFamilyData
  zetaFamily : RelativeZetaDeterminantFamilyData
  finitePart_realPart : ∀ parameter,
    relativeHeatFinitePartLogDeterminant
        (finitePartFamily.finitePart parameter) =
      -(zetaFamily.zetaPrimeAtZero parameter).re
  derivative_realPart : ∀ parameter,
    finitePartFamily.logDerivative parameter =
      -(zetaFamily.parameterDerivative parameter).re

/-- Pointwise norm equality between the zeta determinant and finite-part
magnitude. -/
theorem RelativeZetaFinitePartFamilyComparisonData.norm_zeta_eq_finitePart
    (comparison : RelativeZetaFinitePartFamilyComparisonData)
    (parameter : Real) :
    ‖relativeZetaDeterminantCoordinate comparison.zetaFamily parameter‖ =
      relativeHeatFinitePartDeterminantFamily comparison.finitePartFamily
        parameter := by
  rw [relativeZetaDeterminantCoordinate, Complex.norm_exp]
  change Real.exp (-(comparison.zetaFamily.zetaPrimeAtZero parameter).re) = _
  rw [← comparison.finitePart_realPart parameter]
  rfl

/-- Squared norm equality, i.e. equality of metric weights. -/
theorem RelativeZetaFinitePartFamilyComparisonData.normSq_zeta_eq_metricWeight
    (comparison : RelativeZetaFinitePartFamilyComparisonData)
    (parameter : Real) :
    Complex.normSq
        (relativeZetaDeterminantCoordinate comparison.zetaFamily parameter) =
      relativeHeatFinitePartMetricWeight comparison.finitePartFamily
        parameter := by
  rw [Complex.normSq_eq_norm_sq,
    comparison.norm_zeta_eq_finitePart parameter]
  rfl

/-- The real part of the zeta connection is minus the logarithmic derivative
of the finite-part determinant. -/
theorem RelativeZetaFinitePartFamilyComparisonData.connection_realPart
    (comparison : RelativeZetaFinitePartFamilyComparisonData)
    (parameter : Real) :
    (relativeZetaConnectionCoefficient comparison.zetaFamily parameter).re =
      -comparison.finitePartFamily.logDerivative parameter := by
  unfold relativeZetaConnectionCoefficient
  linarith [comparison.derivative_realPart parameter]

/-- Metric-weight variation written entirely in terms of the real part of the
zeta connection coefficient. -/
theorem RelativeZetaFinitePartFamilyComparisonData.metricWeightDerivative_eq_connection
    (comparison : RelativeZetaFinitePartFamilyComparisonData)
    (parameter : Real) :
    relativeHeatFinitePartMetricWeightDerivative comparison.finitePartFamily
        parameter =
      -2 *
        (relativeZetaConnectionCoefficient comparison.zetaFamily parameter).re *
        relativeHeatFinitePartMetricWeight comparison.finitePartFamily
          parameter := by
  unfold relativeHeatFinitePartMetricWeightDerivative
  rw [comparison.connection_realPart parameter]
  ring

/-- The normalized zeta determinant is a unit complex phase at every
parameter. -/
def relativeZetaFinitePartPhase
    (comparison : RelativeZetaFinitePartFamilyComparisonData)
    (parameter : Real) : Complex :=
  relativeZetaDeterminantCoordinate comparison.zetaFamily parameter /
    (relativeHeatFinitePartDeterminantFamily comparison.finitePartFamily
      parameter : Complex)

/-- Norm-one property of the family phase. -/
theorem relativeZetaFinitePartPhase_norm_one
    (comparison : RelativeZetaFinitePartFamilyComparisonData)
    (parameter : Real) :
    ‖relativeZetaFinitePartPhase comparison parameter‖ = 1 := by
  rw [relativeZetaFinitePartPhase, norm_div,
    comparison.norm_zeta_eq_finitePart parameter,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos
      (relativeHeatFinitePartDeterminantFamily_pos
        comparison.finitePartFamily parameter),
    div_self
      (ne_of_gt
        (relativeHeatFinitePartDeterminantFamily_pos
          comparison.finitePartFamily parameter))]

/-- Recombination of magnitude and unit phase. -/
theorem relativeZetaFinitePart_magnitude_mul_phase
    (comparison : RelativeZetaFinitePartFamilyComparisonData)
    (parameter : Real) :
    (relativeHeatFinitePartDeterminantFamily comparison.finitePartFamily
        parameter : Complex) *
        relativeZetaFinitePartPhase comparison parameter =
      relativeZetaDeterminantCoordinate comparison.zetaFamily parameter := by
  unfold relativeZetaFinitePartPhase
  have hNonzero :
      (relativeHeatFinitePartDeterminantFamily comparison.finitePartFamily
        parameter : Complex) ≠ 0 := by
    exact_mod_cast ne_of_gt
      (relativeHeatFinitePartDeterminantFamily_pos
        comparison.finitePartFamily parameter)
  field_simp

/-- Public finite-part/zeta family checkpoint. -/
theorem relative_zeta_finite_part_family_gate
    (comparison : RelativeZetaFinitePartFamilyComparisonData) :
    (∀ parameter,
      ‖relativeZetaDeterminantCoordinate comparison.zetaFamily parameter‖ =
        relativeHeatFinitePartDeterminantFamily comparison.finitePartFamily
          parameter) ∧
      (∀ parameter,
        relativeHeatFinitePartMetricWeightDerivative comparison.finitePartFamily
            parameter =
          -2 *
            (relativeZetaConnectionCoefficient comparison.zetaFamily
              parameter).re *
            relativeHeatFinitePartMetricWeight comparison.finitePartFamily
              parameter) ∧
      (∀ parameter,
        ‖relativeZetaFinitePartPhase comparison parameter‖ = 1) :=
  ⟨comparison.norm_zeta_eq_finitePart,
    comparison.metricWeightDerivative_eq_connection,
    relativeZetaFinitePartPhase_norm_one comparison⟩

end
end P0EFTJanusProgramPRelativeZetaFinitePartFamily4D
end JanusFormal
