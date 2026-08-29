import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatDataTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinAnalyticDifference4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Family-level analytic subtraction for relative Mellin zeta determinants

Suppose three parameterized heat traces satisfy

```text
h_rel(a,t) = h_actual(a,t) - h_reference(a,t)
```

and their Mellin continuations satisfy the common-domain analytic comparison at
every parameter.  Then

```text
zeta'_rel,a(0)
  = zeta'_actual,a(0) - zeta'_reference,a(0).
```

Differentiating in `a` gives the determinant-connection identity

```text
T_rel(a) = T_actual(a) - T_reference(a).
```

If the actual family is unitarily transported and hence `T_actual = 0`, the
relative coefficient is `-T_reference`.  Combined with the usual standalone
inverse-trace formula `T_reference = -Tr(G_ref H'_ref)`, this is exactly the
reference-trace coefficient required by the Bismut--Freed comparison.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D

set_option autoImplicit false
noncomputable section

open Filter
open P0EFTJanusProgramPRelativeHeatDataTransport4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifference4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-- Parameterwise analytic comparison between a relative zeta family and the
difference of actual/reference zeta families. -/
structure RelativeHeatMellinAnalyticDifferenceFamilyData
    (relative actual reference : RelativeHeatMellinZetaFamilyData) where
  heatTrace_eq_difference : ∀ parameter,
    relative.finitePartFamily.heatTrace parameter =
      heatTraceDifference
        (actual.finitePartFamily.heatTrace parameter)
        (reference.finitePartFamily.heatTrace parameter)
  analyticDifference : ∀ parameter,
    RelativeHeatMellinAnalyticDifferenceData
      ((relative.continuation parameter).transportHeatTrace
        (heatTrace_eq_difference parameter))
      (actual.continuation parameter)
      (reference.continuation parameter)

namespace RelativeHeatMellinAnalyticDifferenceFamilyData

/-- Pointwise subtraction of regularized zeta derivatives at zero. -/
theorem zetaPrimeAtZero_eq_difference
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference)
    (parameter : Real) :
    relative.zetaPrimeAtZero parameter =
      actual.zetaPrimeAtZero parameter - reference.zetaPrimeAtZero parameter := by
  have hDifference :=
    (data.analyticDifference parameter).derivativeAtZero_eq_difference
  simpa [RelativeHeatMellinZetaFamilyData.zetaPrimeAtZero] using hDifference

/-- Equality of the complete parameter functions. -/
theorem zetaPrimeAtZero_function_eq
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference) :
    relative.zetaPrimeAtZero =
      fun parameter => actual.zetaPrimeAtZero parameter -
        reference.zetaPrimeAtZero parameter := by
  funext parameter
  exact data.zetaPrimeAtZero_eq_difference parameter

/-- Parameter derivatives satisfy the same subtraction identity. -/
theorem parameterDerivative_eq_difference
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference)
    (parameter : Real) :
    relative.parameterDerivative parameter =
      actual.parameterDerivative parameter -
        reference.parameterDerivative parameter := by
  have hDifference :
      HasDerivAt
        (fun current => actual.zetaPrimeAtZero current -
          reference.zetaPrimeAtZero current)
        (actual.parameterDerivative parameter -
          reference.parameterDerivative parameter) parameter :=
    (actual.hasDerivAt_zetaPrime parameter).sub
      (reference.hasDerivAt_zetaPrime parameter)
  have hDifferenceAsRelative :
      HasDerivAt relative.zetaPrimeAtZero
        (actual.parameterDerivative parameter -
          reference.parameterDerivative parameter) parameter := by
    rw [data.zetaPrimeAtZero_function_eq]
    exact hDifference
  exact (relative.hasDerivAt_zetaPrime parameter).unique hDifferenceAsRelative

/-- Relative determinant connection coefficient is actual minus reference. -/
theorem connectionCoefficient_eq_difference
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference)
    (parameter : Real) :
    relativeZetaConnectionCoefficient relative.toZetaFamily parameter =
      relativeZetaConnectionCoefficient actual.toZetaFamily parameter -
        relativeZetaConnectionCoefficient reference.toZetaFamily parameter :=
  data.parameterDerivative_eq_difference parameter

/-- The relative determinant is the quotient of actual and reference
determinants. -/
theorem determinant_eq_div
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference)
    (parameter : Real) :
    relativeHeatMellinZetaFamilyDeterminant relative parameter =
      relativeHeatMellinZetaFamilyDeterminant actual parameter /
        relativeHeatMellinZetaFamilyDeterminant reference parameter := by
  unfold relativeHeatMellinZetaFamilyDeterminant
    relativeZetaDeterminantCoordinate
  change Complex.exp (-relative.zetaPrimeAtZero parameter) =
    Complex.exp (-actual.zetaPrimeAtZero parameter) /
      Complex.exp (-reference.zetaPrimeAtZero parameter)
  rw [data.zetaPrimeAtZero_eq_difference parameter]
  rw [show
    -(actual.zetaPrimeAtZero parameter - reference.zetaPrimeAtZero parameter) =
      -actual.zetaPrimeAtZero parameter -
        (-reference.zetaPrimeAtZero parameter) by ring]
  exact Complex.exp_sub _ _

/-- If the actual zeta family is constant, the relative coefficient is minus
the reference coefficient. -/
theorem connectionCoefficient_eq_neg_reference_of_actual_zero
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference)
    (hActual : ∀ parameter,
      relativeZetaConnectionCoefficient actual.toZetaFamily parameter = 0)
    (parameter : Real) :
    relativeZetaConnectionCoefficient relative.toZetaFamily parameter =
      -relativeZetaConnectionCoefficient reference.toZetaFamily parameter := by
  rw [data.connectionCoefficient_eq_difference parameter,
    hActual parameter, zero_sub]

/-- If the standalone reference coefficient is minus its logarithmic trace,
the relative coefficient is the positive reference trace. -/
theorem connectionCoefficient_eq_referenceTrace
    {relative actual reference : RelativeHeatMellinZetaFamilyData}
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference)
    (hActual : ∀ parameter,
      relativeZetaConnectionCoefficient actual.toZetaFamily parameter = 0)
    (referenceTrace : Real → Real)
    (hReference : ∀ parameter,
      relativeZetaConnectionCoefficient reference.toZetaFamily parameter =
        -referenceTrace parameter)
    (parameter : Real) :
    relativeZetaConnectionCoefficient relative.toZetaFamily parameter =
      referenceTrace parameter := by
  rw [data.connectionCoefficient_eq_neg_reference_of_actual_zero hActual
    parameter, hReference parameter, neg_neg]

/-- Public family-level analytic subtraction checkpoint. -/
theorem relative_heat_mellin_analytic_difference_family_gate
    (relative actual reference : RelativeHeatMellinZetaFamilyData)
    (data : RelativeHeatMellinAnalyticDifferenceFamilyData
      relative actual reference) :
    (∀ parameter,
      relative.zetaPrimeAtZero parameter =
        actual.zetaPrimeAtZero parameter - reference.zetaPrimeAtZero parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient relative.toZetaFamily parameter =
        relativeZetaConnectionCoefficient actual.toZetaFamily parameter -
          relativeZetaConnectionCoefficient reference.toZetaFamily parameter) ∧
    (∀ parameter,
      relativeHeatMellinZetaFamilyDeterminant relative parameter =
        relativeHeatMellinZetaFamilyDeterminant actual parameter /
          relativeHeatMellinZetaFamilyDeterminant reference parameter) :=
  ⟨data.zetaPrimeAtZero_eq_difference,
    data.connectionCoefficient_eq_difference,
    data.determinant_eq_div⟩

end RelativeHeatMellinAnalyticDifferenceFamilyData

end
end P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
end JanusFormal
