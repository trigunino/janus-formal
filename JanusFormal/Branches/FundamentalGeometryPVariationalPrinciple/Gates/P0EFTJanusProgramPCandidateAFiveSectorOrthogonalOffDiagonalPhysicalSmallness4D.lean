import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D

/-!
# Full Candidate-A Gårding from one off-diagonal and one physical norm

The principal Hessian is controlled by one canonical off-diagonal form.  The
retained H11 contribution is then one additional bounded quadratic
perturbation.  The total margin is

`sectorFloor - ‖B_off‖ - C_physical`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallness4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalGarding4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, NormedSpace Real (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Canonical principal diagonal/off-diagonal split plus one H11 physical
perturbation. -/
structure CandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallnessData where
  principal : CandidateAFiveSectorOrthogonalOffDiagonalGardingData
    (E := E) Component
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin Component
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalForm vector vector + physicalEnergy vector

namespace CandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallnessData

/-- Generic finite-sector physical-smallness packet. -/
def toFiniteSectorPhysicalSmallness
    (data : CandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallnessData
      (E := E) Component) :
    FiniteSectorPhysicalSmallnessGardingData
      (Sector := CandidateAZeroModeSector) (E := E) where
  principal := data.principal.toFiniteSectorGarding Component
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := by
    simpa [CandidateAFiveSectorOrthogonalOffDiagonalGardingData.margin,
      FiniteSectorQuadraticGardingData.margin] using data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Explicit total margin. -/
def margin
    (data : CandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallnessData
      (E := E) Component) : Real :=
  data.principal.margin Component - data.physicalConstant

/-- Full quadratic Gårding from one orthogonal decomposition, one off-diagonal
norm, and one H11 physical constant. -/
theorem candidateA_five_sector_orthogonal_offDiagonal_physical_smallness_gate
    (data : CandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallnessData
      (E := E) Component) :
    0 < data.margin Component ∧
      ∀ vector : E,
        data.margin Component * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  simpa [margin, FiniteSectorPhysicalSmallnessGardingData.margin,
    CandidateAFiveSectorOrthogonalOffDiagonalGardingData.margin,
    FiniteSectorQuadraticGardingData.margin] using
      data.toFiniteSectorPhysicalSmallness Component
        |>.finite_sector_physical_smallness_garding_gate

end CandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallnessData

end
end P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalPhysicalSmallness4D
end JanusFormal
