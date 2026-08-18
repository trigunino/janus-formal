import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Parametric variation of a finite heat counterterm

A finite UV counterterm is a finite linear combination of fixed time profiles.
Its parameter derivative is obtained by differentiating the coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteHeatCountertermVariation4D

set_option autoImplicit false
noncomputable section

variable {Index : Type*}

/-- Finite heat-counterterm coefficients and their parameter derivatives. -/
structure FiniteHeatCountertermVariationData (Index : Type*) where
  support : Finset Index
  basis : Index → Real → Real
  coefficient : Real → Index → Real
  coefficientDerivative : Real → Index → Real
  coefficient_hasDerivAt : ∀ parameter index, index ∈ support →
    HasDerivAt (fun current ↦ coefficient current index)
      (coefficientDerivative parameter index) parameter

/-- The finite scalar counterterm at a parameter and heat time. -/
def counterterm (data : FiniteHeatCountertermVariationData Index)
    (parameter time : Real) : Real :=
  ∑ index ∈ data.support,
    data.coefficient parameter index * data.basis index time

/-- The coefficientwise parameter derivative of the counterterm. -/
def countertermDerivative (data : FiniteHeatCountertermVariationData Index)
    (parameter time : Real) : Real :=
  ∑ index ∈ data.support,
    data.coefficientDerivative parameter index * data.basis index time

theorem counterterm_hasDerivAt
    (data : FiniteHeatCountertermVariationData Index)
    (parameter time : Real) :
    HasDerivAt (fun current ↦ counterterm data current time)
      (countertermDerivative data parameter time) parameter := by
  unfold counterterm countertermDerivative
  exact HasDerivAt.fun_sum fun index hIndex ↦
    (data.coefficient_hasDerivAt parameter index hIndex).mul_const
      (data.basis index time)

/-- Public gate: every finite counterterm packet has the declared parameter
derivative at every parameter and heat time. -/
theorem finiteHeatCountertermVariation_gate
    (data : FiniteHeatCountertermVariationData Index)
    (parameter time : Real) :
    HasDerivAt (fun current ↦ counterterm data current time)
      (countertermDerivative data parameter time) parameter :=
  counterterm_hasDerivAt data parameter time

end
end P0EFTJanusProgramPFiniteHeatCountertermVariation4D
end JanusFormal
