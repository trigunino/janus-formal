import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPhysicalSmallnessGarding4D

/-!
# Total Candidate-A Gårding from continuous cross forms and H11 smallness

The principal off-diagonal constant is the sum of the norms of the ten
continuous symmetric cross-sector forms.  One additional physical constant
controls the retained H11 form.  The total coercive margin is therefore

`sectorFloor - ∑ pair, ‖crossForm pair‖ - physicalConstant`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorCrossFormPhysicalSmallness4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPhysicalSmallnessGarding4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Canonical principal cross forms plus one bounded H11 physical energy. -/
structure CandidateAFiveSectorCrossFormPhysicalSmallnessData where
  principal : CandidateAFiveSectorCrossFormGardingData (E := E)
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalEnergy vector + physicalEnergy vector

namespace CandidateAFiveSectorCrossFormPhysicalSmallnessData

private theorem crossForm_toSymmetric_margin
    (data : CandidateAFiveSectorCrossFormGardingData (E := E)) :
    data.toSymmetricGardingData.margin = data.margin := by
  rfl

/-- Convert to the existing total finite-margin packet. -/
def toPhysicalSmallnessGardingData
    (data : CandidateAFiveSectorCrossFormPhysicalSmallnessData (E := E)) :
    CandidateAFiveSectorPhysicalSmallnessGardingData (E := E) where
  principal := data.principal.toSymmetricGardingData
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := by
    rw [crossForm_toSymmetric_margin]
    exact data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Explicit total margin. -/
def margin
    (data : CandidateAFiveSectorCrossFormPhysicalSmallnessData (E := E)) : Real :=
  data.principal.diagonalConstants.sectorFloor -
    (∑ pair : P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D.CandidateACrossSectorPair,
      ‖data.principal.crossForm pair‖) -
    data.physicalConstant

private theorem toPhysicalSmallnessGardingData_margin
    (data : CandidateAFiveSectorCrossFormPhysicalSmallnessData (E := E)) :
    data.toPhysicalSmallnessGardingData.margin = data.margin := by
  rfl

/-- Full Candidate-A Gårding directly from continuous cross blocks and the H11
physical constant. -/
theorem candidateA_five_sector_cross_form_physical_smallness_gate
    (data : CandidateAFiveSectorCrossFormPhysicalSmallnessData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  rw [← toPhysicalSmallnessGardingData_margin data]
  exact data.toPhysicalSmallnessGardingData
    |>.candidateA_five_sector_physical_smallness_garding_gate

end CandidateAFiveSectorCrossFormPhysicalSmallnessData

end
end P0EFTJanusProgramPCandidateAFiveSectorCrossFormPhysicalSmallness4D
end JanusFormal
