import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D

/-!
# Commutation from vanishing projected off-diagonal blocks

For a finite resolution of the identity, commutation of an operator with every
sector projector need not be assumed independently.  It follows from the exact
block statement

`P_row H P_column = 0` whenever `row ≠ column`.

Indeed, decomposing the output of `H P_s` leaves only its `s` row, while
decomposing the input of `P_s H` leaves only its `s` column.  Both expressions
therefore equal the same diagonal block `P_s H P_s`.

This file packages that reduction in the precise form consumed by the
actual-kernel-complement construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteProjectedOffDiagonalCommutation4D

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 1100000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {Sector E : Type*}
  [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- A finite self-adjoint projection resolution whose genuine operator blocks
outside the diagonal vanish. -/
structure FiniteProjectedOffDiagonalZeroData
    (operator : E →L[Real] E) where
  resolution : FiniteSelfAdjointProjectionResolutionData
    (Sector := Sector) (E := E)
  offDiagonal_zero : ∀ row column, row ≠ column → ∀ vector,
    resolution.projection row
      (operator (resolution.projection column vector)) = 0

namespace FiniteProjectedOffDiagonalZeroData

/-- After applying the operator to one sector, the output still lies in that
same sector. -/
theorem operator_projection_eq_diagonal
    {operator : E →L[Real] E}
    (data : FiniteProjectedOffDiagonalZeroData
      (Sector := Sector) operator)
    (sector : Sector) (vector : E) :
    operator (data.resolution.projection sector vector) =
      data.resolution.projection sector
        (operator (data.resolution.projection sector vector)) := by
  calc
    operator (data.resolution.projection sector vector) =
        ∑ row : Sector,
          data.resolution.projection row
            (operator (data.resolution.projection sector vector)) :=
      (data.resolution.sum_projection
        (operator (data.resolution.projection sector vector))).symm
    _ = data.resolution.projection sector
          (operator (data.resolution.projection sector vector)) := by
      apply Finset.sum_eq_single sector
      · intro row _ hRow
        exact data.offDiagonal_zero row sector hRow vector
      · intro hMissing
        simp at hMissing

/-- Projecting the full operator output to one sector depends only on the input
component in that sector. -/
theorem projection_operator_eq_diagonal
    {operator : E →L[Real] E}
    (data : FiniteProjectedOffDiagonalZeroData
      (Sector := Sector) operator)
    (sector : Sector) (vector : E) :
    data.resolution.projection sector (operator vector) =
      data.resolution.projection sector
        (operator (data.resolution.projection sector vector)) := by
  calc
    data.resolution.projection sector (operator vector) =
        data.resolution.projection sector
          (operator
            (∑ column : Sector,
              data.resolution.projection column vector)) := by
      rw [data.resolution.sum_projection vector]
    _ = ∑ column : Sector,
          data.resolution.projection sector
            (operator (data.resolution.projection column vector)) := by
      simp
    _ = data.resolution.projection sector
          (operator (data.resolution.projection sector vector)) := by
      apply Finset.sum_eq_single sector
      · intro column _ hColumn
        exact data.offDiagonal_zero sector column hColumn.symm vector
      · intro hMissing
        simp at hMissing

/-- Vanishing of all off-diagonal projected blocks proves the desired
commutation relation. -/
theorem commute
    {operator : E →L[Real] E}
    (data : FiniteProjectedOffDiagonalZeroData
      (Sector := Sector) operator)
    (sector : Sector) (vector : E) :
    operator (data.resolution.projection sector vector) =
      data.resolution.projection sector (operator vector) := by
  calc
    operator (data.resolution.projection sector vector) =
        data.resolution.projection sector
          (operator (data.resolution.projection sector vector)) :=
      data.operator_projection_eq_diagonal sector vector
    _ = data.resolution.projection sector (operator vector) :=
      (data.projection_operator_eq_diagonal sector vector).symm

/-- Feed the derived commutation directly into the established restriction to
`(ker H)ᗮ`. -/
def toCommutingResolution
    {operator : E →L[Real] E}
    (data : FiniteProjectedOffDiagonalZeroData
      (Sector := Sector) operator) :
    FiniteCommutingProjectionResolutionData
      (Sector := Sector) operator where
  resolution := data.resolution
  commute := data.commute

/-- Public checkpoint: one exact off-diagonal block statement supplies all
commutation and kernel-complement projection data. -/
theorem finite_projected_offDiagonal_commutation_gate
    (operator : E →L[Real] E)
    (data : FiniteProjectedOffDiagonalZeroData
      (Sector := Sector) operator) :
    (∀ sector vector,
      operator (data.resolution.projection sector vector) =
        data.resolution.projection sector (operator vector)) ∧
    (∀ vector : SelfAdjointKernelComplement operator,
      ∑ sector : Sector,
        data.toCommutingResolution.complementProjection sector vector =
      vector) :=
  ⟨data.commute,
    data.toCommutingResolution.sum_complementProjection⟩

end FiniteProjectedOffDiagonalZeroData

end
end P0EFTJanusProgramPFiniteProjectedOffDiagonalCommutation4D
end JanusFormal
