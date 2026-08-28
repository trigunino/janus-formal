import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorProjectionPhysicalSmallness4D

/-!
# Candidate-A total margin from symmetric idempotent sector projections

The five projection laws generate the Pythagorean identity.  The projected
principal Hessian supplies the principal margin, and the H11 physical
perturbation is subtracted once.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPhysicalSmallness4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorProjectionPhysicalSmallness4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Symmetric idempotent five-sector resolution plus the H11 physical energy. -/
structure CandidateAFiveSectorSelfAdjointPhysicalSmallnessData where
  principal : CandidateAFiveSectorSelfAdjointPrincipalResolutionData (E := E)
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalForm vector vector + physicalEnergy vector

namespace CandidateAFiveSectorSelfAdjointPhysicalSmallnessData

/-- Positive-projection physical-smallness packet. -/
def toProjectionPhysicalSmallnessData
    (data : CandidateAFiveSectorSelfAdjointPhysicalSmallnessData (E := E)) :
    CandidateAFiveSectorProjectionPhysicalSmallnessData (E := E) where
  principal := data.principal.toProjectionResolutionData
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := by
    simpa [CandidateAFiveSectorSelfAdjointPrincipalResolutionData.margin] using
      data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Explicit total margin. -/
def margin
    (data : CandidateAFiveSectorSelfAdjointPhysicalSmallnessData (E := E)) : Real :=
  data.principal.margin - data.physicalConstant

/-- Full quadratic Gårding from symmetric idempotent sector projections. -/
theorem candidateA_five_sector_selfAdjoint_physical_smallness_gate
    (data : CandidateAFiveSectorSelfAdjointPhysicalSmallnessData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  simpa [margin,
    toProjectionPhysicalSmallnessData,
    CandidateAFiveSectorSelfAdjointPrincipalResolutionData.margin,
    CandidateAFiveSectorProjectionPhysicalSmallnessData.margin] using
      CandidateAFiveSectorProjectionPhysicalSmallnessData.candidateA_five_sector_projection_physical_smallness_gate
          data.toProjectionPhysicalSmallnessData

end CandidateAFiveSectorSelfAdjointPhysicalSmallnessData

end
end P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPhysicalSmallness4D
end JanusFormal
