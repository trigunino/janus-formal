import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Connection equation of a relative zeta determinant family

For a differentiable one-parameter family of zeta derivatives at zero,

`D(a) = exp (-zeta'_a(0))`

satisfies

`D'(a) + (d/da zeta'_a(0)) D(a) = 0`.

This is the local trivialization formula underlying the determinant-line
connection.  The analytic family theorem must still identify the displayed
coefficient with the Bismut--Freed one-form.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

set_option autoImplicit false
noncomputable section

/-- Differentiable family of zeta derivatives at zero. -/
structure RelativeZetaDeterminantFamilyData where
  zetaPrimeAtZero : Real → Complex
  parameterDerivative : Real → Complex
  hasDerivAt_zetaPrime : ∀ parameter,
    HasDerivAt zetaPrimeAtZero (parameterDerivative parameter) parameter

/-- Complex determinant coordinate of the family. -/
def relativeZetaDeterminantCoordinate
    (family : RelativeZetaDeterminantFamilyData)
    (parameter : Real) : Complex :=
  Complex.exp (-family.zetaPrimeAtZero parameter)

/-- The determinant coordinate never vanishes. -/
theorem relativeZetaDeterminantCoordinate_ne_zero
    (family : RelativeZetaDeterminantFamilyData)
    (parameter : Real) :
    relativeZetaDeterminantCoordinate family parameter ≠ 0 :=
  Complex.exp_ne_zero _

/-- Ordinary derivative of the determinant coordinate. -/
def relativeZetaDeterminantCoordinateDerivative
    (family : RelativeZetaDeterminantFamilyData)
    (parameter : Real) : Complex :=
  relativeZetaDeterminantCoordinate family parameter *
    -family.parameterDerivative parameter

/-- Chain rule for `exp(-zeta')`. -/
theorem relativeZetaDeterminantCoordinate_hasDerivAt
    (family : RelativeZetaDeterminantFamilyData)
    (parameter : Real) :
    HasDerivAt (relativeZetaDeterminantCoordinate family)
      (relativeZetaDeterminantCoordinateDerivative family parameter)
      parameter := by
  have hNegative : HasDerivAt
      (fun current => -family.zetaPrimeAtZero current)
      (-family.parameterDerivative parameter) parameter :=
    (family.hasDerivAt_zetaPrime parameter).neg
  change HasDerivAt
    (fun current => Complex.exp (-family.zetaPrimeAtZero current))
    (relativeZetaDeterminantCoordinateDerivative family parameter) parameter
  refine hNegative.cexp.congr_deriv ?_
  unfold relativeZetaDeterminantCoordinateDerivative
    relativeZetaDeterminantCoordinate
  ring

/-- Connection coefficient in the determinant trivialization. -/
def relativeZetaConnectionCoefficient
    (family : RelativeZetaDeterminantFamilyData)
    (parameter : Real) : Complex :=
  family.parameterDerivative parameter

/-- Covariant derivative of a first jet in the zeta trivialization. -/
def relativeZetaConnectionAt
    (family : RelativeZetaDeterminantFamilyData)
    (parameter : Real) (value derivative : Complex) : Complex :=
  derivative + relativeZetaConnectionCoefficient family parameter * value

/-- The zeta determinant is parallel for its canonical connection. -/
theorem relativeZetaDeterminantCoordinate_parallel
    (family : RelativeZetaDeterminantFamilyData)
    (parameter : Real) :
    relativeZetaConnectionAt family parameter
        (relativeZetaDeterminantCoordinate family parameter)
        (relativeZetaDeterminantCoordinateDerivative family parameter) = 0 := by
  unfold relativeZetaConnectionAt relativeZetaConnectionCoefficient
    relativeZetaDeterminantCoordinateDerivative
  ring

/-- Public determinant-connection checkpoint. -/
theorem relative_zeta_determinant_connection_gate
    (family : RelativeZetaDeterminantFamilyData) :
    (∀ parameter,
      HasDerivAt (relativeZetaDeterminantCoordinate family)
        (relativeZetaDeterminantCoordinateDerivative family parameter)
        parameter) ∧
      (∀ parameter,
        relativeZetaConnectionAt family parameter
            (relativeZetaDeterminantCoordinate family parameter)
            (relativeZetaDeterminantCoordinateDerivative family parameter) =
          0) :=
  ⟨relativeZetaDeterminantCoordinate_hasDerivAt family,
    relativeZetaDeterminantCoordinate_parallel family⟩

end
end P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
end JanusFormal
