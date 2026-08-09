import Mathlib

/-!
# Finite-sector quadratic Gårding by diagonal dominance

A coupled quadratic form is often controlled by first proving a positive lower
bound in every physical sector and then estimating all off-diagonal couplings.
This file isolates that finite argument.

The global coercive constant is not supplied independently.  It is the explicit
margin

`sectorFloor - couplingConstant`.

Thus a sectorwise diagonal estimate and a strictly smaller finite coupling bound
produce the full quadratic Gårding inequality.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteSectorQuadraticGarding4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Finite sector decomposition of a principal quadratic energy together with
one bound for all off-diagonal couplings. -/
structure FiniteSectorQuadraticGardingData where
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
  couplingEnergy : E → Real
  couplingConstant : Real
  couplingConstant_nonneg : 0 ≤ couplingConstant
  coupling_bound : ∀ vector,
    |couplingEnergy vector| ≤ couplingConstant * ‖vector‖ ^ 2
  coupling_small : couplingConstant < sectorFloor
  principalEnergy : E → Real
  principal_eq : ∀ vector,
    principalEnergy vector = diagonalEnergy vector + couplingEnergy vector

namespace FiniteSectorQuadraticGardingData

/-- The explicit positive Gårding margin. -/
def margin (data : FiniteSectorQuadraticGardingData
    (Sector := Sector) (E := E)) : Real :=
  data.sectorFloor - data.couplingConstant

/-- Strict positivity of the diagonal-dominance margin. -/
theorem margin_pos
    (data : FiniteSectorQuadraticGardingData
      (Sector := Sector) (E := E)) :
    0 < data.margin :=
  sub_pos.mpr data.coupling_small

/-- Sectorwise diagonal coercivity controls the full norm squared. -/
theorem sectorFloor_norm_sq_le_diagonalEnergy
    (data : FiniteSectorQuadraticGardingData
      (Sector := Sector) (E := E))
    (vector : E) :
    data.sectorFloor * ‖vector‖ ^ 2 ≤ data.diagonalEnergy vector := by
  calc
    data.sectorFloor * ‖vector‖ ^ 2 =
        ∑ sector : Sector,
          data.sectorFloor * data.sectorWeight sector vector := by
      rw [data.sectorWeight_sum vector, Finset.mul_sum]
    _ ≤ ∑ sector : Sector,
          data.sectorConstant sector * data.sectorWeight sector vector := by
      apply Finset.sum_le_sum
      intro sector _
      exact mul_le_mul_of_nonneg_right
        (data.sectorFloor_le sector)
        (data.sectorWeight_nonneg sector vector)
    _ ≤ data.diagonalEnergy vector :=
      data.diagonal_lower vector

/-- The finite coupling estimate and sectorwise diagonal coercivity give the
full principal Gårding inequality with the explicit positive margin. -/
theorem margin_norm_sq_le_principalEnergy
    (data : FiniteSectorQuadraticGardingData
      (Sector := Sector) (E := E))
    (vector : E) :
    data.margin * ‖vector‖ ^ 2 ≤ data.principalEnergy vector := by
  have hDiagonal := data.sectorFloor_norm_sq_le_diagonalEnergy vector
  have hCoupling :
      -(data.couplingConstant * ‖vector‖ ^ 2) ≤
        data.couplingEnergy vector :=
    (abs_le.mp (data.coupling_bound vector)).1
  rw [data.principal_eq vector]
  unfold margin
  nlinarith

/-- Public finite-sector diagonal-dominance checkpoint. -/
theorem finite_sector_quadratic_garding_gate
    (data : FiniteSectorQuadraticGardingData
      (Sector := Sector) (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalEnergy vector :=
  ⟨data.margin_pos, data.margin_norm_sq_le_principalEnergy⟩

end FiniteSectorQuadraticGardingData

end
end P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
end JanusFormal
