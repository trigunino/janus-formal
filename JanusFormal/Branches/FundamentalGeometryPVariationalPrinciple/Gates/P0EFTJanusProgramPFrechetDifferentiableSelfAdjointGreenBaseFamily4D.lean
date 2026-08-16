import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D

/-!
# Frechet-differentiable uniformly-gapped Green families over a general base

The one-parameter identity `G' = - G H' G` is upgraded here to a genuine
Frechet derivative on an arbitrary real normed parameter space.  For

`H : Base → End(E)`

we store the actual Frechet derivative

`DH_b : Base →L[Real] End(E)`.

The Green derivative is not independent: in every tangent direction `v` it is
required to equal

`DG_b[v] = - G_b (DH_b[v]) G_b`.

This is the correct operator-theoretic input for a multidimensional
Bismut--Freed one-form.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFrechetDifferentiableSelfAdjointGreenBaseFamily4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000
noncomputable section

open P0EFTJanusProgramPSelfAdjointUniformGapBaseFamily4D

variable {Base E : Type*}
  [NormedAddCommGroup Base] [NormedSpace Real Base]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Frechet-differentiable self-adjoint uniformly-gapped operator family on a
fixed Hilbert space. -/
structure FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData
    (operator : Base → E →L[Real] E) where
  analytic : SelfAdjointUniformGapBaseFamilyData operator
  derivative : Base → Base →L[Real] (E →L[Real] E)
  hasFDerivAt_operator : ∀ base,
    HasFDerivAt operator (derivative base) base

namespace FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData

/-- Directional derivative of the operator family. -/
def directionalDerivative
    {operator : Base → E →L[Real] E}
    (data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator)
    (base direction : Base) : E →L[Real] E :=
  data.derivative base direction

/-- Canonical logarithmic derivative operator in tangent direction `v`:
`G_b DH_b[v]`. -/
def logarithmicDerivativeOperator
    {operator : Base → E →L[Real] E}
    (data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator)
    (base direction : Base) : E →L[Real] E :=
  (data.analytic.green base).comp (data.derivative base direction)

/-- Directional derivative forced on the inverse by differentiating
`H_b G_b = 1`. -/
def canonicalGreenDirectionalDerivative
    {operator : Base → E →L[Real] E}
    (data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator)
    (base direction : Base) : E →L[Real] E :=
  -((data.analytic.green base).comp
      ((data.derivative base direction).comp
        (data.analytic.green base)))

@[simp]
theorem canonicalGreenDirectionalDerivative_apply
    {operator : Base → E →L[Real] E}
    (data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator)
    (base direction : Base) (vector : E) :
    data.canonicalGreenDirectionalDerivative base direction vector =
      -data.analytic.green base
        (data.derivative base direction (data.analytic.green base vector)) :=
  rfl

/-- Frechet differentiability of the Green family.  The bundled derivative is
required pointwise in tangent directions to be exactly `-G (DH) G`. -/
structure GreenFrechetDifferentiabilityData
    {operator : Base → E →L[Real] E}
    (data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator) : Prop where
  greenDerivative : Base → Base →L[Real] (E →L[Real] E)
  hasFDerivAt_green : ∀ base,
    HasFDerivAt data.analytic.green (greenDerivative base) base
  greenDerivative_eq : ∀ base direction,
    greenDerivative base direction =
      data.canonicalGreenDirectionalDerivative base direction

namespace GreenFrechetDifferentiabilityData

/-- The stored Frechet derivative in every tangent direction is exactly the
canonical inverse derivative. -/
theorem derivative_formula
    {operator : Base → E →L[Real] E}
    {data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator}
    (inverse : GreenFrechetDifferentiabilityData data)
    (base direction : Base) :
    inverse.greenDerivative base direction =
      -((data.analytic.green base).comp
        ((data.derivative base direction).comp
          (data.analytic.green base))) :=
  inverse.greenDerivative_eq base direction

/-- Pointwise directional inverse formula. -/
theorem derivative_apply
    {operator : Base → E →L[Real] E}
    {data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator}
    (inverse : GreenFrechetDifferentiabilityData data)
    (base direction : Base) (vector : E) :
    inverse.greenDerivative base direction vector =
      -data.analytic.green base
        (data.derivative base direction (data.analytic.green base vector)) := by
  rw [inverse.greenDerivative_eq]
  rfl

/-- Frechet differentiability of every Green evaluation. -/
theorem hasFDerivAt_green_apply
    {operator : Base → E →L[Real] E}
    {data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator}
    (inverse : GreenFrechetDifferentiabilityData data)
    (base : Base) (vector : E) :
    HasFDerivAt
      (fun current => data.analytic.green current vector)
      ((ContinuousLinearMap.apply Real E vector).comp
        (inverse.greenDerivative base)) base :=
  (inverse.hasFDerivAt_green base).clm_apply
    (hasFDerivAt_const base vector)

/-- Public multidimensional differentiable Green-family checkpoint. -/
theorem frechet_differentiable_self_adjoint_green_base_family_gate
    {operator : Base → E →L[Real] E}
    (data : FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData operator)
    (inverse : GreenFrechetDifferentiabilityData data) :
    (∀ base,
      HasFDerivAt operator (data.derivative base) base) ∧
    (∀ base,
      HasFDerivAt data.analytic.green (inverse.greenDerivative base) base) ∧
    (∀ base direction,
      inverse.greenDerivative base direction =
        -((data.analytic.green base).comp
          ((data.derivative base direction).comp
            (data.analytic.green base)))) ∧
    (∀ base, ‖data.analytic.green base‖ ≤ data.analytic.gap⁻¹) :=
  ⟨data.hasFDerivAt_operator,
    inverse.hasFDerivAt_green,
    inverse.derivative_formula,
    data.analytic.green_opNorm_le⟩

end GreenFrechetDifferentiabilityData
end FrechetDifferentiableSelfAdjointUniformGapBaseFamilyData

end
end P0EFTJanusProgramPFrechetDifferentiableSelfAdjointGreenBaseFamily4D
end JanusFormal
