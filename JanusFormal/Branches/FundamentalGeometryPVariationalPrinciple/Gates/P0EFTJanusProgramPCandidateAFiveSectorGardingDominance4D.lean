import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-!
# Candidate-A five-sector Gårding by finite diagonal dominance

This file specializes the generic finite-sector argument to the five D10-free
Candidate-A sectors.  Each sector carries its own positive diagonal constant,
while one finite coupling constant controls all cross-sector terms.

The global principal Gårding constant is the explicit margin

`sectorFloor - couplingConstant`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorGardingDominance4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Named diagonal constants for the five physical Candidate-A sectors and one
aggregate off-diagonal coupling bound. -/
structure CandidateAFiveSectorGardingConstants where
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
  couplingConstant : Real
  couplingConstant_nonneg : 0 ≤ couplingConstant
  coupling_small : couplingConstant < sectorFloor

namespace CandidateAFiveSectorGardingConstants

/-- Sector-indexed spelling of the five named constants. -/
def sectorConstant
    (constants : CandidateAFiveSectorGardingConstants) :
    CandidateAZeroModeSector → Real
  | .metricDiffeomorphism => constants.metricDiffeomorphism
  | .abelianGauge => constants.abelianGauge
  | .primitiveSpinCMatter => constants.primitiveSpinCMatter
  | .longitudinalLL => constants.longitudinalLL
  | .boundaryFiniteBV => constants.boundaryFiniteBV

/-- Every named sector constant is positive. -/
theorem sectorConstant_pos
    (constants : CandidateAFiveSectorGardingConstants) :
    ∀ sector, 0 < constants.sectorConstant sector := by
  intro sector
  cases sector with
  | metricDiffeomorphism => exact constants.metricDiffeomorphism_pos
  | abelianGauge => exact constants.abelianGauge_pos
  | primitiveSpinCMatter => exact constants.primitiveSpinCMatter_pos
  | longitudinalLL => exact constants.longitudinalLL_pos
  | boundaryFiniteBV => exact constants.boundaryFiniteBV_pos

/-- The selected finite floor is below every sector constant. -/
theorem sectorFloor_le
    (constants : CandidateAFiveSectorGardingConstants) :
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

/-- Assemble the generic finite-sector quadratic Gårding packet. -/
def toFiniteSectorData
    (constants : CandidateAFiveSectorGardingConstants)
    (sectorWeight : CandidateAZeroModeSector → E → Real)
    (sectorWeight_nonneg : ∀ sector vector,
      0 ≤ sectorWeight sector vector)
    (sectorWeight_sum : ∀ vector,
      ‖vector‖ ^ 2 =
        ∑ sector : CandidateAZeroModeSector,
          sectorWeight sector vector)
    (diagonalEnergy : E → Real)
    (diagonal_lower : ∀ vector,
      (∑ sector : CandidateAZeroModeSector,
        constants.sectorConstant sector * sectorWeight sector vector) ≤
          diagonalEnergy vector)
    (couplingEnergy : E → Real)
    (coupling_bound : ∀ vector,
      |couplingEnergy vector| ≤
        constants.couplingConstant * ‖vector‖ ^ 2)
    (principalEnergy : E → Real)
    (principal_eq : ∀ vector,
      principalEnergy vector = diagonalEnergy vector + couplingEnergy vector) :
    FiniteSectorQuadraticGardingData
      (Sector := CandidateAZeroModeSector) (E := E) where
  sectorWeight := sectorWeight
  sectorWeight_nonneg := sectorWeight_nonneg
  sectorWeight_sum := sectorWeight_sum
  sectorConstant := constants.sectorConstant
  sectorConstant_pos := constants.sectorConstant_pos
  sectorFloor := constants.sectorFloor
  sectorFloor_pos := constants.sectorFloor_pos
  sectorFloor_le := constants.sectorFloor_le
  diagonalEnergy := diagonalEnergy
  diagonal_lower := diagonal_lower
  couplingEnergy := couplingEnergy
  couplingConstant := constants.couplingConstant
  couplingConstant_nonneg := constants.couplingConstant_nonneg
  coupling_bound := coupling_bound
  coupling_small := constants.coupling_small
  principalEnergy := principalEnergy
  principal_eq := principal_eq

/-- Candidate-A five-sector Gårding with the explicit positive margin. -/
theorem candidateA_five_sector_garding_gate
    (constants : CandidateAFiveSectorGardingConstants)
    (sectorWeight : CandidateAZeroModeSector → E → Real)
    (sectorWeight_nonneg : ∀ sector vector,
      0 ≤ sectorWeight sector vector)
    (sectorWeight_sum : ∀ vector,
      ‖vector‖ ^ 2 =
        ∑ sector : CandidateAZeroModeSector,
          sectorWeight sector vector)
    (diagonalEnergy : E → Real)
    (diagonal_lower : ∀ vector,
      (∑ sector : CandidateAZeroModeSector,
        constants.sectorConstant sector * sectorWeight sector vector) ≤
          diagonalEnergy vector)
    (couplingEnergy : E → Real)
    (coupling_bound : ∀ vector,
      |couplingEnergy vector| ≤
        constants.couplingConstant * ‖vector‖ ^ 2)
    (principalEnergy : E → Real)
    (principal_eq : ∀ vector,
      principalEnergy vector = diagonalEnergy vector + couplingEnergy vector) :
    0 < constants.sectorFloor - constants.couplingConstant ∧
      ∀ vector : E,
        (constants.sectorFloor - constants.couplingConstant) * ‖vector‖ ^ 2 ≤
          principalEnergy vector := by
  let data := constants.toFiniteSectorData sectorWeight sectorWeight_nonneg
    sectorWeight_sum diagonalEnergy diagonal_lower couplingEnergy coupling_bound
      principalEnergy principal_eq
  simpa [FiniteSectorQuadraticGardingData.margin, data, toFiniteSectorData] using
    data.finite_sector_quadratic_garding_gate

end CandidateAFiveSectorGardingConstants

end
end P0EFTJanusProgramPCandidateAFiveSectorGardingDominance4D
end JanusFormal
