import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D

/-!
# Candidate-A projected principal Hessian from symmetric idempotent sectors

This file replaces the positive-projection identity by the natural projection
laws: the five bounded sector maps are symmetric, idempotent and resolve the
identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

/-- One principal Hessian and five symmetric idempotent sector projections. -/
structure CandidateAFiveSectorSelfAdjointPrincipalResolutionData where
  principalForm : E →L[Real] E →L[Real] Real
  principal_symmetric : ∀ first second,
    principalForm first second = principalForm second first
  resolution : FiniteSelfAdjointProjectionResolutionData
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

namespace CandidateAFiveSectorSelfAdjointPrincipalResolutionData

/-- Positive-projection principal packet generated from symmetry and
idempotence. -/
def toProjectionResolutionData
    (data : CandidateAFiveSectorSelfAdjointPrincipalResolutionData (E := E)) :
    CandidateAFiveSectorPrincipalProjectionResolutionData (E := E) where
  principalForm := data.principalForm
  principal_symmetric := data.principal_symmetric
  resolution := data.resolution.toNormResolution
  diagonalConstants := data.diagonalConstants
  diagonal_lower := data.diagonal_lower
  cross_sum_small := data.cross_sum_small
  principal_decomposition := data.principal_decomposition

/-- Explicit principal margin. -/
def margin
    (data : CandidateAFiveSectorSelfAdjointPrincipalResolutionData (E := E)) :
    Real :=
  data.toProjectionResolutionData.margin

/-- Principal Gårding from five symmetric idempotent projections. -/
theorem candidateA_five_sector_selfAdjoint_principal_resolution_garding_gate
    (data : CandidateAFiveSectorSelfAdjointPrincipalResolutionData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalForm vector vector :=
  data.toProjectionResolutionData
    |>.candidateA_five_sector_projection_resolution_garding_gate

end CandidateAFiveSectorSelfAdjointPrincipalResolutionData

end
end P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D
end JanusFormal
