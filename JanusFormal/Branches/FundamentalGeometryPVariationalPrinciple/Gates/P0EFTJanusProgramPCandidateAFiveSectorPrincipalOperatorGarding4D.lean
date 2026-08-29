import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D

/-!
# Operator lower bound from one projected Candidate-A principal Hessian

The total quadratic margin constructed from the five projected principal
sectors and the H11 physical perturbation is converted to a norm lower bound for
one displayed operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorGarding4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D
open P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Projected principal finite margin identified with one operator energy. -/
structure CandidateAFiveSectorPrincipalOperatorGardingData
    (operator : E →L[Real] E) where
  finiteMargin : CandidateAFiveSectorPrincipalPhysicalSmallnessData (E := E)
  energy_upper : ∀ vector,
    finiteMargin.totalEnergy vector ≤ ‖vector‖ * ‖operator vector‖

namespace CandidateAFiveSectorPrincipalOperatorGardingData

/-- Generic quadratic/operator packet. -/
def toQuadraticGardingOperatorData
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorPrincipalOperatorGardingData operator) :
    QuadraticGardingOperatorData operator where
  margin := data.finiteMargin.margin
  margin_pos :=
    (CandidateAFiveSectorPrincipalPhysicalSmallnessData.candidateA_five_sector_principal_physical_smallness_gate
        data.finiteMargin).1
  energy := data.finiteMargin.totalEnergy
  energy_lower :=
    (CandidateAFiveSectorPrincipalPhysicalSmallnessData.candidateA_five_sector_principal_physical_smallness_gate
        data.finiteMargin).2
  energy_upper := data.energy_upper

/-- Explicit operator lower bound. -/
theorem lowerBound
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorPrincipalOperatorGardingData operator)
    (vector : E) :
    data.finiteMargin.margin * ‖vector‖ ≤ ‖operator vector‖ :=
  data.toQuadraticGardingOperatorData.lowerBound vector

/-- Injectivity on the zero-mode complement. -/
theorem injective
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorPrincipalOperatorGardingData operator) :
    Function.Injective operator :=
  data.toQuadraticGardingOperatorData.injective

/-- Public operator checkpoint from the projected principal Hessian. -/
theorem candidateA_five_sector_principal_operator_garding_gate
    (operator : E →L[Real] E)
    (data : CandidateAFiveSectorPrincipalOperatorGardingData operator) :
    (∀ vector,
      data.finiteMargin.margin * ‖vector‖ ≤ ‖operator vector‖) ∧
      Function.Injective operator :=
  ⟨data.lowerBound, data.injective⟩

end CandidateAFiveSectorPrincipalOperatorGardingData

end
end P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorGarding4D
end JanusFormal
