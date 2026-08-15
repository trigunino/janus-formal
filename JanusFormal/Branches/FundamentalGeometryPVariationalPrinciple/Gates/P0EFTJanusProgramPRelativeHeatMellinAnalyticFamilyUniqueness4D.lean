import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinAnalyticContinuationUniqueness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Family-level uniqueness of relative Mellin continuations

For one fixed differentiable family of finite-part heat renormalizations, a
family of Mellin continuations consists of

```text
a ↦ zeta_a,
a ↦ zeta'_a(0),
a ↦ d/da zeta'_a(0).
```

If two such presentations are analytically connected to the same heat Mellin
transform at every parameter, pointwise analytic continuation uniqueness gives

```text
zeta'_{1,a}(0) = zeta'_{2,a}(0).
```

Since these two parameter functions are equal and both differentiable, their
parameter derivatives agree as well.  Hence their determinant coordinates and
connection coefficients are identical.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinAnalyticFamilyUniqueness4D

set_option autoImplicit false
noncomputable section

open Filter
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticContinuationUniqueness4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-- One differentiable presentation of Mellin continuations over a fixed
finite-part family. -/
structure RelativeHeatMellinZetaFamilyPresentation
    (finitePartFamily : RelativeHeatFinitePartFamilyData) where
  continuation : ∀ parameter : Real,
    RelativeHeatMellinZetaContinuationData
      (finitePartFamily.finitePart parameter)
  parameterDerivative : Real → Complex
  hasDerivAt_zetaPrime : ∀ parameter : Real,
    HasDerivAt
      (fun current => (continuation current).derivativeAtZero)
      (parameterDerivative parameter) parameter

/-- The regularized zeta derivative at zero. -/
def RelativeHeatMellinZetaFamilyPresentation.zetaPrimeAtZero
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    (presentation : RelativeHeatMellinZetaFamilyPresentation finitePartFamily)
    (parameter : Real) : Complex :=
  (presentation.continuation parameter).derivativeAtZero

/-- Forget the explicit continuation and retain the determinant connection
family. -/
def RelativeHeatMellinZetaFamilyPresentation.toZetaFamily
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    (presentation : RelativeHeatMellinZetaFamilyPresentation finitePartFamily) :
    RelativeZetaDeterminantFamilyData where
  zetaPrimeAtZero := presentation.zetaPrimeAtZero
  parameterDerivative := presentation.parameterDerivative
  hasDerivAt_zetaPrime := presentation.hasDerivAt_zetaPrime

/-- Determinant coordinate of one analytic family presentation. -/
def RelativeHeatMellinZetaFamilyPresentation.determinant
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    (presentation : RelativeHeatMellinZetaFamilyPresentation finitePartFamily)
    (parameter : Real) : Complex :=
  relativeZetaDeterminantCoordinate presentation.toZetaFamily parameter

/-- Every existing Mellin zeta family has an underlying analytic presentation. -/
def RelativeHeatMellinZetaFamilyData.toAnalyticPresentation
    (family : RelativeHeatMellinZetaFamilyData) :
    RelativeHeatMellinZetaFamilyPresentation family.finitePartFamily where
  continuation := family.continuation
  parameterDerivative := family.parameterDerivative
  hasDerivAt_zetaPrime := family.hasDerivAt_zetaPrime

/-- Pointwise analytic comparison of two family presentations. -/
structure RelativeHeatMellinAnalyticFamilyComparisonData
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    (first second : RelativeHeatMellinZetaFamilyPresentation finitePartFamily) where
  analyticComparison : ∀ parameter : Real,
    RelativeHeatMellinAnalyticContinuationComparisonData
      (first.continuation parameter) (second.continuation parameter)

namespace RelativeHeatMellinAnalyticFamilyComparisonData

/-- Pointwise uniqueness makes the two regularized derivative functions equal. -/
theorem zetaPrimeAtZero_eq
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    {first second : RelativeHeatMellinZetaFamilyPresentation finitePartFamily}
    (data : RelativeHeatMellinAnalyticFamilyComparisonData first second) :
    first.zetaPrimeAtZero = second.zetaPrimeAtZero := by
  funext parameter
  exact (data.analyticComparison parameter).derivativeAtZero_eq

/-- The parameter derivatives of the regularized zeta derivatives are equal. -/
theorem parameterDerivative_eq
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    {first second : RelativeHeatMellinZetaFamilyPresentation finitePartFamily}
    (data : RelativeHeatMellinAnalyticFamilyComparisonData first second) :
    first.parameterDerivative = second.parameterDerivative := by
  funext parameter
  have hSecondAsFirst :
      HasDerivAt first.zetaPrimeAtZero
        (second.parameterDerivative parameter) parameter := by
    rw [data.zetaPrimeAtZero_eq]
    exact second.hasDerivAt_zetaPrime parameter
  exact (first.hasDerivAt_zetaPrime parameter).unique hSecondAsFirst

/-- The determinant connection coefficients are presentation-independent. -/
theorem connectionCoefficient_eq
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    {first second : RelativeHeatMellinZetaFamilyPresentation finitePartFamily}
    (data : RelativeHeatMellinAnalyticFamilyComparisonData first second)
    (parameter : Real) :
    relativeZetaConnectionCoefficient first.toZetaFamily parameter =
      relativeZetaConnectionCoefficient second.toZetaFamily parameter := by
  change first.parameterDerivative parameter =
    second.parameterDerivative parameter
  exact congrFun data.parameterDerivative_eq parameter

/-- The complex determinant coordinates are presentation-independent. -/
theorem determinant_eq
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    {first second : RelativeHeatMellinZetaFamilyPresentation finitePartFamily}
    (data : RelativeHeatMellinAnalyticFamilyComparisonData first second)
    (parameter : Real) :
    first.determinant parameter = second.determinant parameter := by
  unfold RelativeHeatMellinZetaFamilyPresentation.determinant
    relativeZetaDeterminantCoordinate
  rw [congrFun data.zetaPrimeAtZero_eq parameter]

/-- Their determinant-coordinate derivatives agree as well. -/
theorem determinantDerivative_eq
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    {first second : RelativeHeatMellinZetaFamilyPresentation finitePartFamily}
    (data : RelativeHeatMellinAnalyticFamilyComparisonData first second)
    (parameter : Real) :
    relativeZetaDeterminantCoordinateDerivative first.toZetaFamily parameter =
      relativeZetaDeterminantCoordinateDerivative second.toZetaFamily parameter := by
  unfold relativeZetaDeterminantCoordinateDerivative
  rw [data.connectionCoefficient_eq parameter]
  rw [data.determinant_eq parameter]

/-- Public family-level analytic uniqueness checkpoint. -/
theorem relative_heat_mellin_analytic_family_uniqueness_gate
    {finitePartFamily : RelativeHeatFinitePartFamilyData}
    (first second : RelativeHeatMellinZetaFamilyPresentation finitePartFamily)
    (data : RelativeHeatMellinAnalyticFamilyComparisonData first second) :
    first.zetaPrimeAtZero = second.zetaPrimeAtZero ∧
    first.parameterDerivative = second.parameterDerivative ∧
    (∀ parameter,
      first.determinant parameter = second.determinant parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient first.toZetaFamily parameter =
        relativeZetaConnectionCoefficient second.toZetaFamily parameter) ∧
    (∀ parameter,
      relativeZetaDeterminantCoordinateDerivative first.toZetaFamily parameter =
        relativeZetaDeterminantCoordinateDerivative second.toZetaFamily parameter) :=
  ⟨data.zetaPrimeAtZero_eq,
    data.parameterDerivative_eq,
    data.determinant_eq,
    data.connectionCoefficient_eq,
    data.determinantDerivative_eq⟩

end RelativeHeatMellinAnalyticFamilyComparisonData

end
end P0EFTJanusProgramPRelativeHeatMellinAnalyticFamilyUniqueness4D
end JanusFormal
