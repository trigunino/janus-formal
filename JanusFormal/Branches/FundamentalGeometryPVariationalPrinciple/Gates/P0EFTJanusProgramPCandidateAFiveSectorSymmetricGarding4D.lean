import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D

/-!
# Candidate-A Gårding from ten symmetric cross-sector blocks

Because the principal Hessian is symmetric, the ordered twenty-five-entry
coupling table can be replaced by the ten unordered cross-sector blocks.  Each
cross energy is understood to contain the complete symmetric contribution of
its two sectors.

The principal Gårding margin is

`sectorFloor - ∑ crossPair, crossConstant crossPair`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- The ten unordered pairs among the five Candidate-A sectors. -/
inductive CandidateACrossSectorPair
  | metricAbelian
  | metricSpinC
  | metricLL
  | metricBoundary
  | abelianSpinC
  | abelianLL
  | abelianBoundary
  | spinCLL
  | spinCBoundary
  | llBoundary
  deriving DecidableEq, Fintype

namespace CandidateACrossSectorPair

/-- First sector of one canonical unordered pair. -/
def first : CandidateACrossSectorPair → CandidateAZeroModeSector
  | .metricAbelian => .metricDiffeomorphism
  | .metricSpinC => .metricDiffeomorphism
  | .metricLL => .metricDiffeomorphism
  | .metricBoundary => .metricDiffeomorphism
  | .abelianSpinC => .abelianGauge
  | .abelianLL => .abelianGauge
  | .abelianBoundary => .abelianGauge
  | .spinCLL => .primitiveSpinCMatter
  | .spinCBoundary => .primitiveSpinCMatter
  | .llBoundary => .longitudinalLL

/-- Second sector of one canonical unordered pair. -/
def second : CandidateACrossSectorPair → CandidateAZeroModeSector
  | .metricAbelian => .abelianGauge
  | .metricSpinC => .primitiveSpinCMatter
  | .metricLL => .longitudinalLL
  | .metricBoundary => .boundaryFiniteBV
  | .abelianSpinC => .primitiveSpinCMatter
  | .abelianLL => .longitudinalLL
  | .abelianBoundary => .boundaryFiniteBV
  | .spinCLL => .longitudinalLL
  | .spinCBoundary => .boundaryFiniteBV
  | .llBoundary => .boundaryFiniteBV

/-- The two entries of a cross pair are distinct. -/
theorem first_ne_second : ∀ pair : CandidateACrossSectorPair,
    pair.first ≠ pair.second := by
  intro pair
  cases pair <;> decide

end CandidateACrossSectorPair

/-- Five diagonal sector estimates and ten complete symmetric cross-sector
energies. -/
structure CandidateAFiveSectorSymmetricGardingData where
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
  crossEnergy : CandidateACrossSectorPair → E → Real
  crossConstant : CandidateACrossSectorPair → Real
  crossConstant_nonneg : ∀ pair, 0 ≤ crossConstant pair
  cross_bound : ∀ pair vector,
    |crossEnergy pair vector| ≤ crossConstant pair * ‖vector‖ ^ 2
  cross_sum_small :
    (∑ pair : CandidateACrossSectorPair, crossConstant pair) <
      diagonalConstants.sectorFloor
  principalEnergy : E → Real
  principal_eq : ∀ vector,
    principalEnergy vector = diagonalEnergy vector +
      ∑ pair : CandidateACrossSectorPair, crossEnergy pair vector

namespace CandidateAFiveSectorSymmetricGardingData

/-- Sum of the ten symmetric cross-sector constants. -/
def couplingConstant
    (data : CandidateAFiveSectorSymmetricGardingData (E := E)) : Real :=
  ∑ pair : CandidateACrossSectorPair, data.crossConstant pair

/-- Sum of the ten symmetric cross-sector energies. -/
def couplingEnergy
    (data : CandidateAFiveSectorSymmetricGardingData (E := E))
    (vector : E) : Real :=
  ∑ pair : CandidateACrossSectorPair, data.crossEnergy pair vector

/-- The ten finite estimates control the complete symmetric coupling energy. -/
theorem couplingEnergy_bound
    (data : CandidateAFiveSectorSymmetricGardingData (E := E))
    (vector : E) :
    |data.couplingEnergy vector| ≤
      data.couplingConstant * ‖vector‖ ^ 2 := by
  calc
    |data.couplingEnergy vector| =
        |∑ pair : CandidateACrossSectorPair,
          data.crossEnergy pair vector| := rfl
    _ ≤ ∑ pair : CandidateACrossSectorPair,
          |data.crossEnergy pair vector| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ pair : CandidateACrossSectorPair,
          data.crossConstant pair * ‖vector‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro pair _
      exact data.cross_bound pair vector
    _ = data.couplingConstant * ‖vector‖ ^ 2 := by
      unfold couplingConstant
      rw [Finset.sum_mul]

/-- Generic finite-sector packet generated from the symmetric table. -/
def toQuadraticGardingData
    (data : CandidateAFiveSectorSymmetricGardingData (E := E)) :
    FiniteSectorQuadraticGardingData
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
  couplingEnergy := data.couplingEnergy
  couplingConstant := data.couplingConstant
  couplingConstant_nonneg :=
    Finset.sum_nonneg fun pair _ => data.crossConstant_nonneg pair
  coupling_bound := data.couplingEnergy_bound
  coupling_small := data.cross_sum_small
  principalEnergy := data.principalEnergy
  principal_eq := data.principal_eq

/-- Explicit five-sector symmetric Gårding margin. -/
def margin
    (data : CandidateAFiveSectorSymmetricGardingData (E := E)) : Real :=
  data.diagonalConstants.sectorFloor - data.couplingConstant

/-- Preferred ten-cross-block Candidate-A Gårding theorem. -/
theorem candidateA_five_sector_symmetric_garding_gate
    (data : CandidateAFiveSectorSymmetricGardingData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalEnergy vector := by
  simpa [toQuadraticGardingData, margin, couplingConstant,
    FiniteSectorQuadraticGardingData.margin] using
      data.toQuadraticGardingData.finite_sector_quadratic_garding_gate

end CandidateAFiveSectorSymmetricGardingData

end
end P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
end JanusFormal
