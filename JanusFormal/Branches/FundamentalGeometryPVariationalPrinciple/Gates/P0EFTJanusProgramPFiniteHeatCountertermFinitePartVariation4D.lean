import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteHeatCountertermVariation4D

/-!
# Finite-part variation of a finite heat counterterm

The finite-part contribution uses the signed finite part assigned to each
fixed time profile.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteHeatCountertermVariation4D

variable {Index : Type*}

/-- A finite heat counterterm together with the signed finite part of each
time profile. -/
structure FiniteHeatCountertermFinitePartVariationData (Index : Type*) where
  variation : FiniteHeatCountertermVariationData Index
  basisFinitePart : Index → Real

/-- The finite-part contribution of the counterterm. -/
def finitePartContribution
    (data : FiniteHeatCountertermFinitePartVariationData Index)
    (parameter : Real) : Real :=
  ∑ index ∈ data.variation.support,
    data.variation.coefficient parameter index * data.basisFinitePart index

/-- The coefficientwise parameter derivative of the finite-part
contribution. -/
def finitePartDerivative
    (data : FiniteHeatCountertermFinitePartVariationData Index)
    (parameter : Real) : Real :=
  ∑ index ∈ data.variation.support,
    data.variation.coefficientDerivative parameter index * data.basisFinitePart index

theorem finitePartContribution_hasDerivAt
    (data : FiniteHeatCountertermFinitePartVariationData Index)
    (parameter : Real) :
    HasDerivAt (finitePartContribution data)
      (finitePartDerivative data parameter) parameter := by
  unfold finitePartContribution finitePartDerivative
  exact HasDerivAt.fun_sum fun index hIndex ↦
    (data.variation.coefficient_hasDerivAt parameter index hIndex).mul_const
      (data.basisFinitePart index)

/-- Public gate: the finite-part counterterm contribution has the declared
parameter derivative. -/
theorem finiteHeatCountertermFinitePartVariation_gate
    (data : FiniteHeatCountertermFinitePartVariationData Index)
    (parameter : Real) :
    HasDerivAt (finitePartContribution data)
      (finitePartDerivative data parameter) parameter :=
  finitePartContribution_hasDerivAt data parameter

end
end P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
end JanusFormal
