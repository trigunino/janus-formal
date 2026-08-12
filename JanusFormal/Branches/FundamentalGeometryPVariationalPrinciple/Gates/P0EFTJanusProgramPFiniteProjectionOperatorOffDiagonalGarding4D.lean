import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorProductOperatorOffDiagonalGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D

/-!
# Operator Gårding for an inherited finite projection resolution

The actual kernel complement inherits its sector projectors from the one
full-space commuting decomposition.  It need not be equipped with a second
product-coordinate equivalence.

For any finite self-adjoint projection resolution on a Hilbert space and any
bounded self-adjoint operator `A`, this file defines

`A_diag = Σ_s P_s A P_s`,
`A_off  = A - A_diag`,

and proves that `‖A_off‖ < c_floor`, together with the diagonal quadratic
estimates, implies Gårding.  This is the operator-level form used directly on
`(ker H_actual)ᗮ`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteProjectionOperatorOffDiagonalGarding4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorProductOperatorOffDiagonalGarding4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Finite inherited sector resolution with operator-level diagonal dominance. -/
structure FiniteProjectionOperatorOffDiagonalGardingData
    (operator : E →L[Real] E) where
  operator_selfAdjoint : IsSelfAdjoint operator
  resolution : FiniteSelfAdjointProjectionResolutionData
    (Sector := Sector) (E := E)
  sectorConstant : Sector → Real
  sectorConstant_pos : ∀ sector, 0 < sectorConstant sector
  sectorFloor : Real
  sectorFloor_pos : 0 < sectorFloor
  sectorFloor_le : ∀ sector, sectorFloor ≤ sectorConstant sector
  diagonal_lower : ∀ sector vector,
    sectorConstant sector * ‖resolution.projection sector vector‖ ^ 2 ≤
      inner Real
        (operator (resolution.projection sector vector))
        (resolution.projection sector vector)
  offDiagonalOperator_small :
    ‖operator -
      ∑ sector : Sector,
        (resolution.projection sector).comp
          (operator.comp (resolution.projection sector))‖ <
      sectorFloor

namespace FiniteProjectionOperatorOffDiagonalGardingData

/-- Sum of the inherited diagonal operator blocks. -/
def diagonalOperator
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) : E →L[Real] E :=
  ∑ sector : Sector,
    (data.resolution.projection sector).comp
      (operator.comp (data.resolution.projection sector))

/-- Complete off-diagonal operator remainder. -/
def offDiagonalOperator
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) : E →L[Real] E :=
  operator - data.diagonalOperator

/-- The represented diagonal form is exactly the sum of the restricted
principal forms. -/
theorem diagonalOperator_form
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) :
    operatorBilinearForm data.diagonalOperator =
      ∑ sector : Sector,
        (operatorBilinearForm operator).bilinearComp
          (data.resolution.projection sector)
          (data.resolution.projection sector) := by
  ext first second
  simp only [diagonalOperator, operatorBilinearForm_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.bilinearComp_apply, inner_sum_left]
  apply Finset.sum_congr rfl
  intro sector _
  exact data.resolution.projection_symmetric sector
    (operator (data.resolution.projection sector first)) second

/-- The form remainder is represented by `A_off`. -/
theorem offDiagonalOperator_form
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) :
    operatorBilinearForm operator -
        ∑ sector : Sector,
          (operatorBilinearForm operator).bilinearComp
            (data.resolution.projection sector)
            (data.resolution.projection sector) =
      operatorBilinearForm data.offDiagonalOperator := by
  rw [← data.diagonalOperator_form]
  ext first second
  rfl

/-- Operator smallness implies the canonical form smallness. -/
theorem offDiagonalForm_small
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) :
    ‖operatorBilinearForm operator -
      ∑ sector : Sector,
        (operatorBilinearForm operator).bilinearComp
          (data.resolution.projection sector)
          (data.resolution.projection sector)‖ < data.sectorFloor := by
  rw [data.offDiagonalOperator_form]
  exact lt_of_le_of_lt
    (operatorBilinearForm_norm_le data.offDiagonalOperator)
    (by simpa [offDiagonalOperator, diagonalOperator] using
      data.offDiagonalOperator_small)

/-- Finite-sector quadratic Gårding packet generated from the operator blocks. -/
def toFiniteSectorGarding
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) :
    FiniteSectorQuadraticGardingData (Sector := Sector) (E := E) where
  sectorWeight := fun sector vector =>
    ‖data.resolution.projection sector vector‖ ^ 2
  sectorWeight_nonneg := fun _ _ => sq_nonneg _
  sectorWeight_sum := data.resolution.norm_sq_decomposition
  sectorConstant := data.sectorConstant
  sectorConstant_pos := data.sectorConstant_pos
  sectorFloor := data.sectorFloor
  sectorFloor_pos := data.sectorFloor_pos
  sectorFloor_le := data.sectorFloor_le
  diagonalEnergy := fun vector =>
    (∑ sector : Sector,
      (operatorBilinearForm operator).bilinearComp
        (data.resolution.projection sector)
        (data.resolution.projection sector)) vector vector
  diagonal_lower := by
    intro vector
    simp only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.bilinearComp_apply, operatorBilinearForm_apply]
    apply Finset.sum_le_sum
    intro sector _
    exact data.diagonal_lower sector vector
  couplingEnergy := fun vector =>
    operatorBilinearForm data.offDiagonalOperator vector vector
  couplingConstant := ‖data.offDiagonalOperator‖
  couplingConstant_nonneg := norm_nonneg _
  coupling_bound := by
    intro vector
    calc
      |operatorBilinearForm data.offDiagonalOperator vector vector| =
          ‖inner Real (data.offDiagonalOperator vector) vector‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖data.offDiagonalOperator vector‖ * ‖vector‖ :=
        norm_inner_le_norm (𝕜 := Real) (data.offDiagonalOperator vector) vector
      _ ≤ (‖data.offDiagonalOperator‖ * ‖vector‖) * ‖vector‖ :=
        mul_le_mul_of_nonneg_right
          (data.offDiagonalOperator.le_opNorm vector) (norm_nonneg vector)
      _ = ‖data.offDiagonalOperator‖ * ‖vector‖ ^ 2 := by ring
  coupling_small := by
    simpa [offDiagonalOperator, diagonalOperator] using
      data.offDiagonalOperator_small
  principalEnergy := fun vector => inner Real (operator vector) vector
  principal_eq := by
    intro vector
    have hForm := congrArg
      (fun form : E →L[Real] E →L[Real] Real => form vector vector)
      data.offDiagonalOperator_form
    simpa [operatorBilinearForm_apply, offDiagonalOperator] using hForm.symm

/-- Explicit principal margin. -/
def margin
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) : Real :=
  data.sectorFloor - ‖data.offDiagonalOperator‖

/-- Public operator-block Gårding checkpoint. -/
theorem finite_projection_operator_offDiagonal_garding_gate
    {operator : E →L[Real] E}
    (data : FiniteProjectionOperatorOffDiagonalGardingData
      (Sector := Sector) operator) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ inner Real (operator vector) vector := by
  simpa [margin, FiniteSectorQuadraticGardingData.margin] using
    data.toFiniteSectorGarding.finite_sector_quadratic_garding_gate

end FiniteProjectionOperatorOffDiagonalGardingData

end
end P0EFTJanusProgramPFiniteProjectionOperatorOffDiagonalGarding4D
end JanusFormal
