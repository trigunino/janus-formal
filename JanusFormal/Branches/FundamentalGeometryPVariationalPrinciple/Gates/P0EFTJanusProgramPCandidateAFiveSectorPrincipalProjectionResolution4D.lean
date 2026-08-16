import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteProjectionNormResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D

/-!
# Candidate-A principal block data from a five-sector projection resolution

The projected-principal frontier no longer asks separately for the Pythagorean
norm identity.  A finite positive resolution of the identity by the five
Candidate-A sector projections supplies it automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteProjectionNormResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D
open P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- One principal Hessian and a positive five-sector resolution of the identity.
The remaining fields are the genuinely analytic diagonal estimates, cross-form
smallness and principal quadratic decomposition. -/
structure CandidateAFiveSectorPrincipalProjectionResolutionData where
  principalForm : E →L[Real] E →L[Real] Real
  principal_symmetric : ∀ first second,
    principalForm first second = principalForm second first
  resolution : FiniteProjectionNormResolutionData
    (Sector := CandidateAZeroModeSector) (E := E)
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  diagonal_lower : ∀ sector vector,
    diagonalConstants.sectorConstant sector *
        ‖resolution.projection sector vector‖ ^ 2 ≤
      principalForm
        (resolution.projection sector vector)
        (resolution.projection sector vector)
  cross_sum_small :
    (∑ pair : CandidateACrossSectorPair,
      ‖candidateASectorSymmetricCrossForm principalForm resolution.projection
        pair‖) < diagonalConstants.sectorFloor
  principal_decomposition : ∀ vector,
    principalForm vector vector =
      (∑ sector : CandidateAZeroModeSector,
        principalForm
          (resolution.projection sector vector)
          (resolution.projection sector vector)) +
      ∑ pair : CandidateACrossSectorPair,
        candidateASectorSymmetricCrossForm principalForm resolution.projection
          pair vector vector

namespace CandidateAFiveSectorPrincipalProjectionResolutionData

/-- Established projected-principal packet with the norm-square identity filled
from the projection resolution. -/
def toPrincipalBlockData
    (data : CandidateAFiveSectorPrincipalProjectionResolutionData (E := E)) :
    CandidateAFiveSectorPrincipalBlockData (E := E) where
  principalForm := data.principalForm
  principal_symmetric := data.principal_symmetric
  projection := data.resolution.projection
  norm_sq_decomposition := data.resolution.norm_sq_decomposition
  diagonalConstants := data.diagonalConstants
  diagonal_lower := data.diagonal_lower
  cross_sum_small := data.cross_sum_small
  principal_decomposition := data.principal_decomposition

/-- Explicit principal margin. -/
def margin
    (data : CandidateAFiveSectorPrincipalProjectionResolutionData (E := E)) :
    Real :=
  data.toPrincipalBlockData.margin

/-- Principal Gårding from the positive five-sector projection resolution. -/
theorem candidateA_five_sector_projection_resolution_garding_gate
    (data : CandidateAFiveSectorPrincipalProjectionResolutionData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalForm vector vector := by
  exact data.toPrincipalBlockData
    |>.candidateA_five_sector_principal_block_garding_gate

end CandidateAFiveSectorPrincipalProjectionResolutionData

end
end P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D
end JanusFormal
