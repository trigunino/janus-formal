import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-!
# Parameter-uniform Mellin continuation and zeta metric family

Pointwise Mellin continuation is not enough for a Quillen connection: the
regularized derivative at zero must itself vary differentiably with the Janus
parameter.  This file packages that requirement and converts it to the zeta
family and finite-part metric comparison already consumed by the terminal
Quillen frontier.

Every pointwise zeta function is still tied to the corresponding heat trace in
a right half-plane.  The only additional family input is the derivative of
`zetaPrimeAtZero` and its real-part agreement with the derivative of the
finite-part logarithm.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-- A differentiable family of honest Mellin continuations. -/
structure RelativeHeatMellinZetaFamilyData where
  finitePartFamily : RelativeHeatFinitePartFamilyData
  continuation : ∀ parameter : Real,
    RelativeHeatMellinZetaContinuationData
      (finitePartFamily.finitePart parameter)
  parameterDerivative : Real → Complex
  hasDerivAt_zetaPrime : ∀ parameter : Real,
    HasDerivAt
      (fun current => (continuation current).derivativeAtZero)
      (parameterDerivative parameter) parameter
  connection_realPart : ∀ parameter : Real,
    finitePartFamily.logDerivative parameter =
      -(parameterDerivative parameter).re

/-- The regularized derivative at zero as a parameter family. -/
def RelativeHeatMellinZetaFamilyData.zetaPrimeAtZero
    (family : RelativeHeatMellinZetaFamilyData) (parameter : Real) : Complex :=
  (family.continuation parameter).derivativeAtZero

/-- Conversion to the abstract zeta connection family. -/
def RelativeHeatMellinZetaFamilyData.toZetaFamily
    (family : RelativeHeatMellinZetaFamilyData) :
    RelativeZetaDeterminantFamilyData where
  zetaPrimeAtZero := family.zetaPrimeAtZero
  parameterDerivative := family.parameterDerivative
  hasDerivAt_zetaPrime := family.hasDerivAt_zetaPrime

/-- Conversion to the finite-part metric comparison.  The pointwise real-part
identity comes from the Mellin continuation certificate at each parameter. -/
def RelativeHeatMellinZetaFamilyData.toFinitePartComparison
    (family : RelativeHeatMellinZetaFamilyData) :
    RelativeZetaFinitePartFamilyComparisonData where
  finitePartFamily := family.finitePartFamily
  zetaFamily := family.toZetaFamily
  finitePart_realPart := by
    intro parameter
    exact (family.continuation parameter).finitePart_realPart
  derivative_realPart := family.connection_realPart

/-- The complex determinant family obtained from the Mellin continuation. -/
def relativeHeatMellinZetaFamilyDeterminant
    (family : RelativeHeatMellinZetaFamilyData) (parameter : Real) : Complex :=
  relativeZetaDeterminantCoordinate family.toZetaFamily parameter

/-- Every family value has the intrinsic finite-part magnitude. -/
theorem norm_relativeHeatMellinZetaFamilyDeterminant
    (family : RelativeHeatMellinZetaFamilyData) (parameter : Real) :
    ‖relativeHeatMellinZetaFamilyDeterminant family parameter‖ =
      relativeHeatFinitePartDeterminantFamily
        family.finitePartFamily parameter :=
  family.toFinitePartComparison.norm_zeta_eq_finitePart parameter

/-- The parameter connection is metric-compatible with the finite-part metric. -/
theorem relativeHeatMellinZetaFamily_metricVariation
    (family : RelativeHeatMellinZetaFamilyData) (parameter : Real) :
    relativeHeatFinitePartMetricWeightDerivative
        family.finitePartFamily parameter =
      -2 *
        (relativeZetaConnectionCoefficient
          family.toZetaFamily parameter).re *
        relativeHeatFinitePartMetricWeight
          family.finitePartFamily parameter :=
  family.toFinitePartComparison.metricWeightDerivative_eq_connection parameter

/-- The normalized spectral-asymmetry phase is unitary throughout the family. -/
theorem relativeHeatMellinZetaFamily_phase_norm_one
    (family : RelativeHeatMellinZetaFamilyData) (parameter : Real) :
    ‖relativeZetaFinitePartPhase family.toFinitePartComparison parameter‖ = 1 :=
  relativeZetaFinitePartPhase_norm_one family.toFinitePartComparison parameter

/-- Public family-level Mellin continuation checkpoint. -/
theorem relative_heat_mellin_zeta_family_gate
    (family : RelativeHeatMellinZetaFamilyData) :
    (∀ parameter : Real,
      ‖relativeHeatMellinZetaFamilyDeterminant family parameter‖ =
        relativeHeatFinitePartDeterminantFamily
          family.finitePartFamily parameter) ∧
      (∀ parameter : Real,
        relativeHeatFinitePartMetricWeightDerivative
            family.finitePartFamily parameter =
          -2 *
            (relativeZetaConnectionCoefficient
              family.toZetaFamily parameter).re *
            relativeHeatFinitePartMetricWeight
              family.finitePartFamily parameter) ∧
      ∀ parameter : Real,
        ‖relativeZetaFinitePartPhase
          family.toFinitePartComparison parameter‖ = 1 :=
  ⟨norm_relativeHeatMellinZetaFamilyDeterminant family,
    relativeHeatMellinZetaFamily_metricVariation family,
    relativeHeatMellinZetaFamily_phase_norm_one family⟩

end
end P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
end JanusFormal
