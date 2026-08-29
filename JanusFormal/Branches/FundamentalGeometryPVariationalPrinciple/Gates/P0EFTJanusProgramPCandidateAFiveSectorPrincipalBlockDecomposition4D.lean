import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D

/-!
# Candidate-A principal block decomposition from five projections

A single continuous symmetric principal form and five bounded sector
projections determine all diagonal and cross blocks.  The ten cross forms are
constructed by symmetrizing the two ordered restrictions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPCandidateAFiveSectorCrossFormGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Restriction of one principal form to a diagonal sector. -/
def candidateASectorDiagonalForm
    (principal : E →L[Real] E →L[Real] Real)
    (projection : CandidateAZeroModeSector → E →L[Real] E)
    (sector : CandidateAZeroModeSector) :
    E →L[Real] E →L[Real] Real :=
  principal.bilinearComp (projection sector) (projection sector)

/-- Complete symmetric cross contribution of one unordered sector pair. -/
def candidateASectorSymmetricCrossForm
    (principal : E →L[Real] E →L[Real] Real)
    (projection : CandidateAZeroModeSector → E →L[Real] E)
    (pair : CandidateACrossSectorPair) :
    E →L[Real] E →L[Real] Real :=
  principal.bilinearComp (projection pair.first) (projection pair.second) +
    principal.bilinearComp (projection pair.second) (projection pair.first)

/-- One principal form, five projections and the five diagonal estimates. -/
structure CandidateAFiveSectorPrincipalBlockData where
  principalForm : E →L[Real] E →L[Real] Real
  principal_symmetric : ∀ first second,
    principalForm first second = principalForm second first
  projection : CandidateAZeroModeSector → E →L[Real] E
  norm_sq_decomposition : ∀ vector,
    ‖vector‖ ^ 2 =
      ∑ sector : CandidateAZeroModeSector,
        ‖projection sector vector‖ ^ 2
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  diagonal_lower : ∀ sector vector,
    diagonalConstants.sectorConstant sector *
        ‖projection sector vector‖ ^ 2 ≤
      principalForm (projection sector vector) (projection sector vector)
  cross_sum_small :
    (∑ pair : CandidateACrossSectorPair,
      ‖candidateASectorSymmetricCrossForm principalForm projection pair‖) <
        diagonalConstants.sectorFloor
  principal_decomposition : ∀ vector,
    principalForm vector vector =
      (∑ sector : CandidateAZeroModeSector,
        principalForm (projection sector vector) (projection sector vector)) +
      ∑ pair : CandidateACrossSectorPair,
        candidateASectorSymmetricCrossForm principalForm projection pair
          vector vector

namespace CandidateAFiveSectorPrincipalBlockData

/-- The five diagonal restrictions. -/
def diagonalForm
    (data : CandidateAFiveSectorPrincipalBlockData (E := E))
    (sector : CandidateAZeroModeSector) :
    E →L[Real] E →L[Real] Real :=
  candidateASectorDiagonalForm data.principalForm data.projection sector

/-- The ten automatically generated cross restrictions. -/
def crossForm
    (data : CandidateAFiveSectorPrincipalBlockData (E := E))
    (pair : CandidateACrossSectorPair) :
    E →L[Real] E →L[Real] Real :=
  candidateASectorSymmetricCrossForm data.principalForm data.projection pair

/-- Convert the actual principal block decomposition to the continuous
cross-form Gårding packet. -/
def toCrossFormGardingData
    (data : CandidateAFiveSectorPrincipalBlockData (E := E)) :
    CandidateAFiveSectorCrossFormGardingData (E := E) where
  diagonalConstants := data.diagonalConstants
  sectorWeight := fun sector vector => ‖data.projection sector vector‖ ^ 2
  sectorWeight_nonneg := fun _ _ => sq_nonneg _
  sectorWeight_sum := data.norm_sq_decomposition
  diagonalEnergy := fun vector =>
    ∑ sector : CandidateAZeroModeSector,
      data.principalForm
        (data.projection sector vector) (data.projection sector vector)
  diagonal_lower := by
    intro vector
    apply Finset.sum_le_sum
    intro sector _
    exact data.diagonal_lower sector vector
  crossForm := data.crossForm
  cross_sum_small := data.cross_sum_small
  principalEnergy := fun vector => data.principalForm vector vector
  principal_eq := data.principal_decomposition

/-- Explicit principal Gårding margin generated from one form and five
projections. -/
def margin
    (data : CandidateAFiveSectorPrincipalBlockData (E := E)) : Real :=
  data.diagonalConstants.sectorFloor -
    ∑ pair : CandidateACrossSectorPair, ‖data.crossForm pair‖

/-- Public five-projection principal Gårding checkpoint. -/
theorem candidateA_five_sector_principal_block_garding_gate
    (data : CandidateAFiveSectorPrincipalBlockData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalForm vector vector := by
  simpa [toCrossFormGardingData, margin, crossForm,
    CandidateAFiveSectorCrossFormGardingData.margin,
    CandidateAFiveSectorCrossFormGardingData.couplingConstant]
    using data.toCrossFormGardingData.candidateA_five_sector_cross_form_garding_gate

end CandidateAFiveSectorPrincipalBlockData

end
end P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D
end JanusFormal
