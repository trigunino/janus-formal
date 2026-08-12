import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointUniformGapFamily4D

/-!
# Differentiable uniformly-gapped Green families

Uniform gap data construct the inverse Green operator at every parameter.  For
family-index and determinant-connection arguments one must additionally know
that the operator family is differentiable and that differentiation commutes
with inversion.

The inverse derivative is not an independent arbitrary operator.  It is fixed
by the standard identity

`G'_a = - G_a H'_a G_a`.

This file records differentiability together with exactly that identity.  It
separates the ordinary Banach-algebra inverse theorem from all later nuclear
trace and zeta arguments.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open P0EFTJanusProgramPSelfAdjointUniformGapFamily4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Differentiable operator family with a uniform self-adjoint gap. -/
structure DifferentiableSelfAdjointUniformGapFamilyData
    (operator : Real → E →L[Real] E) where
  analytic : SelfAdjointUniformGapFamilyData operator
  derivative : Real → E →L[Real] E
  hasDerivAt_operator : ∀ parameter,
    HasDerivAt operator (derivative parameter) parameter

namespace DifferentiableSelfAdjointUniformGapFamilyData

/-- Canonical logarithmic derivative operator `G_a H'_a`. -/
def logarithmicDerivativeOperator
    {operator : Real → E →L[Real] E}
    (data : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (parameter : Real) : E →L[Real] E :=
  (data.analytic.green parameter).comp (data.derivative parameter)

/-- Canonical derivative forced on the Green family by differentiation of
`H_a G_a = 1`. -/
def canonicalGreenDerivative
    {operator : Real → E →L[Real] E}
    (data : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (parameter : Real) : E →L[Real] E :=
  -((data.analytic.green parameter).comp
      ((data.derivative parameter).comp
        (data.analytic.green parameter)))

@[simp]
theorem canonicalGreenDerivative_apply
    {operator : Real → E →L[Real] E}
    (data : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (parameter : Real) (vector : E) :
    data.canonicalGreenDerivative parameter vector =
      -data.analytic.green parameter
        (data.derivative parameter (data.analytic.green parameter vector)) :=
  rfl

/-- Analytic inversion packet.  The equality field prevents the derivative of
the inverse from being supplied independently of `H'_a`. -/
structure GreenDifferentiabilityData
    {operator : Real → E →L[Real] E}
    (data : DifferentiableSelfAdjointUniformGapFamilyData operator) : Prop where
  greenDerivative : Real → E →L[Real] E
  hasDerivAt_green : ∀ parameter,
    HasDerivAt data.analytic.green (greenDerivative parameter) parameter
  greenDerivative_eq : ∀ parameter,
    greenDerivative parameter = data.canonicalGreenDerivative parameter

namespace GreenDifferentiabilityData

/-- The stored inverse derivative is exactly `-G H' G`. -/
theorem derivative_formula
    {operator : Real → E →L[Real] E}
    {data : DifferentiableSelfAdjointUniformGapFamilyData operator}
    (inverse : GreenDifferentiabilityData data)
    (parameter : Real) :
    inverse.greenDerivative parameter =
      -((data.analytic.green parameter).comp
        ((data.derivative parameter).comp
          (data.analytic.green parameter))) :=
  inverse.greenDerivative_eq parameter

/-- Pointwise derivative formula. -/
theorem derivative_apply
    {operator : Real → E →L[Real] E}
    {data : DifferentiableSelfAdjointUniformGapFamilyData operator}
    (inverse : GreenDifferentiabilityData data)
    (parameter : Real) (vector : E) :
    inverse.greenDerivative parameter vector =
      -data.analytic.green parameter
        (data.derivative parameter (data.analytic.green parameter vector)) := by
  rw [inverse.greenDerivative_eq]
  rfl

/-- Differentiability of every inverse evaluation. -/
theorem hasDerivAt_green_apply
    {operator : Real → E →L[Real] E}
    {data : DifferentiableSelfAdjointUniformGapFamilyData operator}
    (inverse : GreenDifferentiabilityData data)
    (parameter : Real) (vector : E) :
    HasDerivAt
      (fun current => data.analytic.green current vector)
      (inverse.greenDerivative parameter vector) parameter :=
  (inverse.hasDerivAt_green parameter).clm_apply
    (hasDerivAt_const parameter vector)

/-- Public differentiable Green-family checkpoint. -/
theorem differentiable_self_adjoint_green_family_gate
    {operator : Real → E →L[Real] E}
    (data : DifferentiableSelfAdjointUniformGapFamilyData operator)
    (inverse : GreenDifferentiabilityData data) :
    (∀ parameter,
      HasDerivAt operator (data.derivative parameter) parameter) ∧
      (∀ parameter,
        HasDerivAt data.analytic.green
          (data.canonicalGreenDerivative parameter) parameter) ∧
      (∀ parameter vector,
        data.canonicalGreenDerivative parameter vector =
          -data.analytic.green parameter
            (data.derivative parameter
              (data.analytic.green parameter vector))) ∧
      (∀ parameter, ‖data.analytic.green parameter‖ ≤ data.analytic.gap⁻¹) := by
  refine ⟨data.hasDerivAt_operator, ?_, ?_, data.analytic.green_opNorm_le⟩
  · intro parameter
    rw [← inverse.greenDerivative_eq parameter]
    exact inverse.hasDerivAt_green parameter
  · intro parameter vector
    rfl

end GreenDifferentiabilityData
end DifferentiableSelfAdjointUniformGapFamilyData

end
end P0EFTJanusProgramPDifferentiableSelfAdjointGreenFamily4D
end JanusFormal
