import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D

/-!
# Total Candidate-A Gårding from a positive five-sector resolution

A positive projection resolution supplies the norm decomposition.  One physical
H11 quadratic bound is then subtracted from the principal projected margin.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorProjectionPhysicalSmallness4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- Positive five-sector resolution plus the retained H11 physical energy. -/
structure CandidateAFiveSectorProjectionPhysicalSmallnessData where
  principal : CandidateAFiveSectorPrincipalProjectionResolutionData (E := E)
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalForm vector vector + physicalEnergy vector

namespace CandidateAFiveSectorProjectionPhysicalSmallnessData

/-- Established principal-physical packet. -/
def toPrincipalPhysicalSmallnessData
    (data : CandidateAFiveSectorProjectionPhysicalSmallnessData (E := E)) :
    CandidateAFiveSectorPrincipalPhysicalSmallnessData (E := E) where
  principal := data.principal.toPrincipalBlockData
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Explicit total margin. -/
def margin
    (data : CandidateAFiveSectorProjectionPhysicalSmallnessData (E := E)) : Real :=
  data.principal.margin - data.physicalConstant

/-- Full quadratic Gårding from the positive projection resolution. -/
theorem candidateA_five_sector_projection_physical_smallness_gate
    (data : CandidateAFiveSectorProjectionPhysicalSmallnessData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  simpa [margin,
    CandidateAFiveSectorPrincipalPhysicalSmallnessData.margin] using
      data.toPrincipalPhysicalSmallnessData
        |>.candidateA_five_sector_principal_physical_smallness_gate

end CandidateAFiveSectorProjectionPhysicalSmallnessData

end
end P0EFTJanusProgramPCandidateAFiveSectorProjectionPhysicalSmallness4D
end JanusFormal
