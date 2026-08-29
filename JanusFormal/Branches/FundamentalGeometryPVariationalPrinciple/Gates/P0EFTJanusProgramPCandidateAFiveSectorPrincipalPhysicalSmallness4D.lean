import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorCrossFormPhysicalSmallness4D

/-!
# Total Candidate-A Gårding from one principal form and H11 smallness

Five projections decompose one principal Hessian into its diagonal and ten
cross blocks.  One physical H11 constant is then subtracted from the resulting
principal margin.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D
open P0EFTJanusProgramPCandidateAFiveSectorCrossFormPhysicalSmallness4D
open P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- One principal form with five projections, plus the retained physical
quadratic perturbation. -/
structure CandidateAFiveSectorPrincipalPhysicalSmallnessData where
  principal : CandidateAFiveSectorPrincipalBlockData (E := E)
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalForm vector vector +
      physicalEnergy vector

namespace CandidateAFiveSectorPrincipalPhysicalSmallnessData

/-- Convert to the continuous-cross-form finite-margin packet. -/
def toCrossFormPhysicalSmallnessData
    (data : CandidateAFiveSectorPrincipalPhysicalSmallnessData (E := E)) :
    CandidateAFiveSectorCrossFormPhysicalSmallnessData (E := E) where
  principal := data.principal.toCrossFormGardingData
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := by
    simpa [CandidateAFiveSectorPrincipalBlockData.margin,
      CandidateAFiveSectorPrincipalBlockData.crossForm,
      CandidateAFiveSectorPrincipalBlockData.toCrossFormGardingData,
      P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D.CandidateAFiveSectorCrossFormGardingData.margin,
      P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D.CandidateAFiveSectorCrossFormGardingData.couplingConstant]
      using data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Explicit total margin from one principal form. -/
def margin
    (data : CandidateAFiveSectorPrincipalPhysicalSmallnessData (E := E)) : Real :=
  data.principal.margin - data.physicalConstant

/-- Full Candidate-A Gårding from the projected principal Hessian and H11
smallness. -/
theorem candidateA_five_sector_principal_physical_smallness_gate
    (data : CandidateAFiveSectorPrincipalPhysicalSmallnessData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  simpa [margin,
    toCrossFormPhysicalSmallnessData,
    CandidateAFiveSectorPrincipalBlockData.margin,
    CandidateAFiveSectorPrincipalBlockData.crossForm,
    CandidateAFiveSectorPrincipalBlockData.toCrossFormGardingData,
    CandidateAFiveSectorCrossFormPhysicalSmallnessData.margin,
    P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D.CandidateAFiveSectorCrossFormGardingData.margin,
    P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D.CandidateAFiveSectorCrossFormGardingData.couplingConstant]
    using data.toCrossFormPhysicalSmallnessData
      |>.candidateA_five_sector_cross_form_physical_smallness_gate

end CandidateAFiveSectorPrincipalPhysicalSmallnessData

end
end P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D
end JanusFormal
