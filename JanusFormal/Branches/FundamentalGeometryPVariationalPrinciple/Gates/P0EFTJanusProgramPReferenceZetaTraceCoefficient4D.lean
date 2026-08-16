import Mathlib.Analysis.Complex.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D

/-!
# Standalone reference zeta coefficient from finite-part trace variation

For one standalone reference family, the existing Mellin-zeta packet already
states that the real part of the connection coefficient is the negative
parameter derivative of the finite-part logarithm.

To identify the full complex coefficient with the inverse logarithmic trace it
is therefore enough to prove two real statements:

```text
finitePartLogDerivative(a) = Tr(G_a H'_a),
Im(zeta'_a(0)) = 0.
```

The second statement implies that the imaginary part of its parameter
derivative vanishes.  Thus

```text
T_reference(a) = -Tr(G_a H'_a).
```

No separate complex coefficient identity is required.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceZetaTraceCoefficient4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D

/-- Real analytic inputs sufficient to identify one standalone reference zeta
connection coefficient. -/
structure ReferenceZetaTraceCoefficientData
    (family : RelativeHeatMellinZetaFamilyData) where
  logarithmicTrace : Real → Real
  finitePartLogDerivative_eq_trace : ∀ parameter,
    family.finitePartFamily.logDerivative parameter = logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceZetaTraceCoefficientData

/-- Reality of the regularized zeta derivative forces reality of its parameter
derivative. -/
theorem parameterDerivative_im_zero
    {family : RelativeHeatMellinZetaFamilyData}
    (data : ReferenceZetaTraceCoefficientData family)
    (parameter : Real) :
    (family.parameterDerivative parameter).im = 0 := by
  have hImaginary :
      HasDerivAt
        (fun current : Real => (family.zetaPrimeAtZero current).im)
        (family.parameterDerivative parameter).im parameter := by
    change HasDerivAt
      (fun current : Real => (family.continuation current).derivativeAtZero.im)
      (family.parameterDerivative parameter).im parameter
    simpa [Function.comp_def] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt parameter
      (family.hasDerivAt_zetaPrime parameter)
  have hZero :
      HasDerivAt (fun _ : Real => (0 : Real)) 0 parameter :=
    hasDerivAt_const parameter (0 : Real)
  have hZeroAsImaginary :
      HasDerivAt
        (fun current : Real => (family.zetaPrimeAtZero current).im)
        0 parameter := by
    simpa [data.zetaPrimeAtZero_real] using hZero
  exact hImaginary.unique hZeroAsImaginary

/-- The standalone reference zeta coefficient is minus its logarithmic operator
trace. -/
theorem connectionCoefficient_eq_neg_trace
    {family : RelativeHeatMellinZetaFamilyData}
    (data : ReferenceZetaTraceCoefficientData family)
    (parameter : Real) :
    relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) := by
  change family.parameterDerivative parameter =
    -(data.logarithmicTrace parameter : Complex)
  apply Complex.ext
  · change (family.parameterDerivative parameter).re =
      -data.logarithmicTrace parameter
    linarith [family.connection_realPart parameter,
      data.finitePartLogDerivative_eq_trace parameter]
  · change (family.parameterDerivative parameter).im =
      (-(data.logarithmicTrace parameter : Complex)).im
    rw [data.parameterDerivative_im_zero parameter]
    simp

/-- Public standalone reference coefficient checkpoint. -/
theorem reference_zeta_trace_coefficient_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (data : ReferenceZetaTraceCoefficientData family) :
    (∀ parameter,
      (family.parameterDerivative parameter).im = 0) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨data.parameterDerivative_im_zero,
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceZetaTraceCoefficientData

end
end P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
end JanusFormal
