import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorPairwiseGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-!
# Candidate-A Gårding from the finite table of sector couplings

This is the five-sector spelling of the pairwise diagonal-dominance theorem.
The analytic input is a finite table of twenty-five coupling constants together
with five diagonal coercivity constants.  The resulting global Gårding margin
is computed by subtraction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteSectorPairwiseGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Five named diagonal constants and one common positive floor. -/
structure CandidateAFiveSectorDiagonalConstants where
  metricDiffeomorphism : Real
  metricDiffeomorphism_pos : 0 < metricDiffeomorphism
  abelianGauge : Real
  abelianGauge_pos : 0 < abelianGauge
  primitiveSpinCMatter : Real
  primitiveSpinCMatter_pos : 0 < primitiveSpinCMatter
  longitudinalLL : Real
  longitudinalLL_pos : 0 < longitudinalLL
  boundaryFiniteBV : Real
  boundaryFiniteBV_pos : 0 < boundaryFiniteBV
  sectorFloor : Real
  sectorFloor_pos : 0 < sectorFloor
  sectorFloor_le_metricDiffeomorphism :
    sectorFloor ≤ metricDiffeomorphism
  sectorFloor_le_abelianGauge :
    sectorFloor ≤ abelianGauge
  sectorFloor_le_primitiveSpinCMatter :
    sectorFloor ≤ primitiveSpinCMatter
  sectorFloor_le_longitudinalLL :
    sectorFloor ≤ longitudinalLL
  sectorFloor_le_boundaryFiniteBV :
    sectorFloor ≤ boundaryFiniteBV

namespace CandidateAFiveSectorDiagonalConstants

/-- Sector-indexed diagonal constant. -/
def sectorConstant
    (constants : CandidateAFiveSectorDiagonalConstants) :
    CandidateAZeroModeSector → Real
  | .metricDiffeomorphism => constants.metricDiffeomorphism
  | .abelianGauge => constants.abelianGauge
  | .primitiveSpinCMatter => constants.primitiveSpinCMatter
  | .longitudinalLL => constants.longitudinalLL
  | .boundaryFiniteBV => constants.boundaryFiniteBV

theorem sectorConstant_pos
    (constants : CandidateAFiveSectorDiagonalConstants) :
    ∀ sector, 0 < constants.sectorConstant sector := by
  intro sector
  cases sector with
  | metricDiffeomorphism => exact constants.metricDiffeomorphism_pos
  | abelianGauge => exact constants.abelianGauge_pos
  | primitiveSpinCMatter => exact constants.primitiveSpinCMatter_pos
  | longitudinalLL => exact constants.longitudinalLL_pos
  | boundaryFiniteBV => exact constants.boundaryFiniteBV_pos

theorem sectorFloor_le
    (constants : CandidateAFiveSectorDiagonalConstants) :
    ∀ sector, constants.sectorFloor ≤ constants.sectorConstant sector := by
  intro sector
  cases sector with
  | metricDiffeomorphism =>
      exact constants.sectorFloor_le_metricDiffeomorphism
  | abelianGauge =>
      exact constants.sectorFloor_le_abelianGauge
  | primitiveSpinCMatter =>
      exact constants.sectorFloor_le_primitiveSpinCMatter
  | longitudinalLL =>
      exact constants.sectorFloor_le_longitudinalLL
  | boundaryFiniteBV =>
      exact constants.sectorFloor_le_boundaryFiniteBV

end CandidateAFiveSectorDiagonalConstants

/-- Candidate-A principal energy presented as five diagonal sector energies and
a finite ordered-pair table of cross-sector couplings. -/
structure CandidateAFiveSectorPairwiseGardingData where
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  sectorWeight : CandidateAZeroModeSector → E → Real
  sectorWeight_nonneg : ∀ sector vector,
    0 ≤ sectorWeight sector vector
  sectorWeight_sum : ∀ vector,
    ‖vector‖ ^ 2 =
      ∑ sector : CandidateAZeroModeSector,
        sectorWeight sector vector
  diagonalEnergy : E → Real
  diagonal_lower : ∀ vector,
    (∑ sector : CandidateAZeroModeSector,
      diagonalConstants.sectorConstant sector * sectorWeight sector vector) ≤
        diagonalEnergy vector
  pairEnergy : CandidateAZeroModeSector × CandidateAZeroModeSector → E → Real
  pairConstant : CandidateAZeroModeSector × CandidateAZeroModeSector → Real
  pairConstant_nonneg : ∀ pair, 0 ≤ pairConstant pair
  pair_bound : ∀ pair vector,
    |pairEnergy pair vector| ≤ pairConstant pair * ‖vector‖ ^ 2
  pair_sum_small :
    (∑ pair : CandidateAZeroModeSector × CandidateAZeroModeSector,
      pairConstant pair) < diagonalConstants.sectorFloor
  principalEnergy : E → Real
  principal_eq : ∀ vector,
    principalEnergy vector = diagonalEnergy vector +
      ∑ pair : CandidateAZeroModeSector × CandidateAZeroModeSector,
        pairEnergy pair vector

namespace CandidateAFiveSectorPairwiseGardingData

/-- Generic finite-sector packet generated from the Candidate-A table. -/
def toFiniteSectorPairwiseData
    (data : CandidateAFiveSectorPairwiseGardingData (E := E)) :
    FiniteSectorPairwiseGardingData
      (Sector := CandidateAZeroModeSector) (E := E) where
  sectorWeight := data.sectorWeight
  sectorWeight_nonneg := data.sectorWeight_nonneg
  sectorWeight_sum := data.sectorWeight_sum
  sectorConstant := data.diagonalConstants.sectorConstant
  sectorConstant_pos := data.diagonalConstants.sectorConstant_pos
  sectorFloor := data.diagonalConstants.sectorFloor
  sectorFloor_pos := data.diagonalConstants.sectorFloor_pos
  sectorFloor_le := data.diagonalConstants.sectorFloor_le
  diagonalEnergy := data.diagonalEnergy
  diagonal_lower := data.diagonal_lower
  pairEnergy := data.pairEnergy
  pairConstant := data.pairConstant
  pairConstant_nonneg := data.pairConstant_nonneg
  pair_bound := data.pair_bound
  pair_sum_small := data.pair_sum_small
  principalEnergy := data.principalEnergy
  principal_eq := data.principal_eq

/-- Sum of the twenty-five finite coupling bounds. -/
def couplingConstant
    (data : CandidateAFiveSectorPairwiseGardingData (E := E)) : Real :=
  ∑ pair : CandidateAZeroModeSector × CandidateAZeroModeSector,
    data.pairConstant pair

/-- Explicit principal Gårding margin. -/
def margin
    (data : CandidateAFiveSectorPairwiseGardingData (E := E)) : Real :=
  data.diagonalConstants.sectorFloor - data.couplingConstant

/-- Five-sector pairwise Gårding checkpoint. -/
theorem candidateA_five_sector_pairwise_garding_gate
    (data : CandidateAFiveSectorPairwiseGardingData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalEnergy vector := by
  simpa [toFiniteSectorPairwiseData, margin, couplingConstant,
    FiniteSectorPairwiseGardingData.margin,
    FiniteSectorPairwiseGardingData.couplingConstant] using
      data.toFiniteSectorPairwiseData.finite_sector_pairwise_garding_gate

end CandidateAFiveSectorPairwiseGardingData

end
end P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
end JanusFormal
