import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorQuadraticGarding4D

/-!
# Finite-sector Gårding from pairwise coupling bounds

The aggregate off-diagonal coupling constant of the finite-sector Gårding
argument can itself be constructed.  Give one scalar quadratic contribution and
one nonnegative bound for each ordered pair of sectors.  Their finite sum is the
complete coupling energy, and the sum of their constants controls it.

The global coercive margin is therefore

`sectorFloor - ∑ pair, pairConstant pair`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteSectorPairwiseGarding4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteSectorQuadraticGarding4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Sectorwise diagonal energies and pairwise finite couplings. -/
structure FiniteSectorPairwiseGardingData where
  sectorWeight : Sector → E → Real
  sectorWeight_nonneg : ∀ sector vector,
    0 ≤ sectorWeight sector vector
  sectorWeight_sum : ∀ vector,
    ‖vector‖ ^ 2 = ∑ sector : Sector, sectorWeight sector vector
  sectorConstant : Sector → Real
  sectorConstant_pos : ∀ sector, 0 < sectorConstant sector
  sectorFloor : Real
  sectorFloor_pos : 0 < sectorFloor
  sectorFloor_le : ∀ sector, sectorFloor ≤ sectorConstant sector
  diagonalEnergy : E → Real
  diagonal_lower : ∀ vector,
    (∑ sector : Sector,
      sectorConstant sector * sectorWeight sector vector) ≤
        diagonalEnergy vector
  pairEnergy : Sector × Sector → E → Real
  pairConstant : Sector × Sector → Real
  pairConstant_nonneg : ∀ pair, 0 ≤ pairConstant pair
  pair_bound : ∀ pair vector,
    |pairEnergy pair vector| ≤ pairConstant pair * ‖vector‖ ^ 2
  pair_sum_small :
    (∑ pair : Sector × Sector, pairConstant pair) < sectorFloor
  principalEnergy : E → Real
  principal_eq : ∀ vector,
    principalEnergy vector = diagonalEnergy vector +
      ∑ pair : Sector × Sector, pairEnergy pair vector

namespace FiniteSectorPairwiseGardingData

/-- Aggregate finite coupling constant. -/
def couplingConstant
    (data : FiniteSectorPairwiseGardingData
      (Sector := Sector) (E := E)) : Real :=
  ∑ pair : Sector × Sector, data.pairConstant pair

/-- Aggregate finite coupling energy. -/
def couplingEnergy
    (data : FiniteSectorPairwiseGardingData
      (Sector := Sector) (E := E))
    (vector : E) : Real :=
  ∑ pair : Sector × Sector, data.pairEnergy pair vector

/-- The aggregate coupling constant is nonnegative. -/
theorem couplingConstant_nonneg
    (data : FiniteSectorPairwiseGardingData
      (Sector := Sector) (E := E)) :
    0 ≤ data.couplingConstant :=
  Finset.sum_nonneg fun pair _ => data.pairConstant_nonneg pair

/-- Pairwise estimates sum to the aggregate quadratic coupling estimate. -/
theorem couplingEnergy_bound
    (data : FiniteSectorPairwiseGardingData
      (Sector := Sector) (E := E))
    (vector : E) :
    |data.couplingEnergy vector| ≤
      data.couplingConstant * ‖vector‖ ^ 2 := by
  calc
    |data.couplingEnergy vector| =
        |∑ pair : Sector × Sector, data.pairEnergy pair vector| := rfl
    _ ≤ ∑ pair : Sector × Sector,
          |data.pairEnergy pair vector| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ pair : Sector × Sector,
          data.pairConstant pair * ‖vector‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro pair _
      exact data.pair_bound pair vector
    _ = data.couplingConstant * ‖vector‖ ^ 2 := by
      unfold couplingConstant
      rw [Finset.sum_mul]

/-- Forget the pairwise presentation and obtain the aggregate finite-sector
Gårding packet. -/
def toQuadraticGardingData
    (data : FiniteSectorPairwiseGardingData
      (Sector := Sector) (E := E)) :
    FiniteSectorQuadraticGardingData (Sector := Sector) (E := E) where
  sectorWeight := data.sectorWeight
  sectorWeight_nonneg := data.sectorWeight_nonneg
  sectorWeight_sum := data.sectorWeight_sum
  sectorConstant := data.sectorConstant
  sectorConstant_pos := data.sectorConstant_pos
  sectorFloor := data.sectorFloor
  sectorFloor_pos := data.sectorFloor_pos
  sectorFloor_le := data.sectorFloor_le
  diagonalEnergy := data.diagonalEnergy
  diagonal_lower := data.diagonal_lower
  couplingEnergy := data.couplingEnergy
  couplingConstant := data.couplingConstant
  couplingConstant_nonneg := data.couplingConstant_nonneg
  coupling_bound := data.couplingEnergy_bound
  coupling_small := data.pair_sum_small
  principalEnergy := data.principalEnergy
  principal_eq := data.principal_eq

/-- Explicit pairwise diagonal-dominance margin. -/
def margin
    (data : FiniteSectorPairwiseGardingData
      (Sector := Sector) (E := E)) : Real :=
  data.sectorFloor - data.couplingConstant

/-- Pairwise finite-sector Gårding theorem. -/
theorem finite_sector_pairwise_garding_gate
    (data : FiniteSectorPairwiseGardingData
      (Sector := Sector) (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalEnergy vector := by
  simpa [margin, FiniteSectorQuadraticGardingData.margin] using
    data.toQuadraticGardingData.finite_sector_quadratic_garding_gate

end FiniteSectorPairwiseGardingData

end
end P0EFTJanusProgramPFiniteSectorPairwiseGarding4D
end JanusFormal
