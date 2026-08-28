import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPrincipal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPhysicalSmallness4D

/-!
# Total Candidate-A Gårding from orthogonal coordinates and H11 smallness

One orthogonal coordinate decomposition generates the five natural projectors
and the complete principal block expansion.  Subtracting the one H11 physical
constant from the generated principal margin gives the total coercive margin.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPhysicalSmallness4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPrincipal4D
open P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPhysicalSmallness4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPCandidateAFiveSectorAutomaticPrincipalDecomposition4D
open P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Orthogonal principal decomposition plus the genuine H11 physical energy. -/
structure CandidateAFiveSectorOrthogonalPhysicalSmallnessData where
  principal : CandidateAFiveSectorOrthogonalPrincipalData (E := E) Component
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin Component
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalForm vector vector + physicalEnergy vector

namespace CandidateAFiveSectorOrthogonalPhysicalSmallnessData

/-- Generate the previous self-adjoint-projection packet. -/
def toSelfAdjointPhysicalSmallness
    (data : CandidateAFiveSectorOrthogonalPhysicalSmallnessData
      (E := E) Component) :
    CandidateAFiveSectorSelfAdjointPhysicalSmallnessData (E := E) where
  principal := data.principal.toAutomaticPrincipal Component
    |>.toSelfAdjointPrincipalResolution
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Explicit total margin. -/
def margin
    (data : CandidateAFiveSectorOrthogonalPhysicalSmallnessData
      (E := E) Component) : Real :=
  data.principal.margin Component - data.physicalConstant

/-- Full quadratic Gårding from orthogonal sector coordinates. -/
theorem candidateA_five_sector_orthogonal_physical_smallness_gate
    (data : CandidateAFiveSectorOrthogonalPhysicalSmallnessData
      (E := E) Component) :
    0 < data.margin Component ∧
      ∀ vector : E,
        data.margin Component * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  simpa [margin,
    toSelfAdjointPhysicalSmallness,
    CandidateAFiveSectorSelfAdjointPhysicalSmallnessData.margin,
    CandidateAFiveSectorOrthogonalPrincipalData.margin,
    CandidateAFiveSectorOrthogonalPrincipalData.toAutomaticPrincipal,
    CandidateAFiveSectorAutomaticPrincipalData.margin,
    CandidateAFiveSectorAutomaticPrincipalData.toSelfAdjointPrincipalResolution,
    CandidateAFiveSectorSelfAdjointPrincipalResolutionData.margin] using
      data.toSelfAdjointPhysicalSmallness Component
        |>.candidateA_five_sector_selfAdjoint_physical_smallness_gate

end CandidateAFiveSectorOrthogonalPhysicalSmallnessData

end
end P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPhysicalSmallness4D
end JanusFormal
