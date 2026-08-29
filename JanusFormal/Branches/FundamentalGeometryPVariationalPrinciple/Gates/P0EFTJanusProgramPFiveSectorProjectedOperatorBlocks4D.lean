import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D

/-!
# Operator blocks from an orthogonal five-sector resolution

Once the five physical projectors are generated from one orthogonal product
coordinate system, the sector blocks of any bounded operator are canonical:

`A_st = P_s A P_t`.

This file proves the exact block reconstruction

`A = Σ_s Σ_t A_st`.

For a self-adjoint operator it also proves the expected adjoint symmetry between
opposite blocks.  Hence diagonal and cross-sector quadratic estimates can be
attached to the genuine operator blocks rather than to ten independently
chosen bilinear forms.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorProjectedOperatorBlocks4D

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 1100000

noncomputable section

open Set Topology
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D

local syntax "⟪" term "," term "," "Real⟫" : term
local macro_rules | `(⟪$x, $y, Real⟫) => `(inner Real $x $y)

variable
  {E MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter LongitudinalLL
    BoundaryFiniteBV : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup MetricDiffeomorphism]
  [InnerProductSpace Real MetricDiffeomorphism]
  [NormedAddCommGroup AbelianGauge]
  [InnerProductSpace Real AbelianGauge]
  [NormedAddCommGroup PrimitiveSpinCMatter]
  [InnerProductSpace Real PrimitiveSpinCMatter]
  [NormedAddCommGroup LongitudinalLL]
  [InnerProductSpace Real LongitudinalLL]
  [NormedAddCommGroup BoundaryFiniteBV]
  [InnerProductSpace Real BoundaryFiniteBV]

local notation "Resolution" =>
  FiveSectorOrthogonalProductDecomposition
    (E := E)
    (MetricDiffeomorphism := MetricDiffeomorphism)
    (AbelianGauge := AbelianGauge)
    (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
    (LongitudinalLL := LongitudinalLL)
    (BoundaryFiniteBV := BoundaryFiniteBV)

/-- Canonical `(row,column)` block `P_row A P_column`. -/
def fiveSectorProjectedOperatorBlock
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (row column : FiveSectorSlot) : E →L[Real] E :=
  (resolution.projection row).comp
    (operator.comp (resolution.projection column))

@[simp]
theorem fiveSectorProjectedOperatorBlock_apply
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (row column : FiveSectorSlot) (state : E) :
    fiveSectorProjectedOperatorBlock resolution operator row column state =
      resolution.projection row
        (operator (resolution.projection column state)) :=
  rfl

/-- Summing the row blocks at fixed input sector recovers the operator on that
sector. -/
theorem fiveSectorProjectedOperatorBlock_sum_row
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (column : FiveSectorSlot) (state : E) :
    (∑ row : FiveSectorSlot,
      fiveSectorProjectedOperatorBlock resolution operator row column state) =
      operator (resolution.projection column state) := by
  simpa [fiveSectorProjectedOperatorBlock] using
    resolution.sum_projection_apply
      (operator (resolution.projection column state))

/-- Exact 25-block reconstruction of the bounded operator. -/
theorem fiveSectorProjectedOperatorBlock_sum
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (state : E) :
    (∑ row : FiveSectorSlot, ∑ column : FiveSectorSlot,
      fiveSectorProjectedOperatorBlock resolution operator row column state) =
      operator state := by
  rw [Finset.sum_comm]
  calc
    (∑ column : FiveSectorSlot, ∑ row : FiveSectorSlot,
      fiveSectorProjectedOperatorBlock resolution operator row column state) =
        ∑ column : FiveSectorSlot,
          operator (resolution.projection column state) := by
      apply Finset.sum_congr rfl
      intro column _
      exact fiveSectorProjectedOperatorBlock_sum_row resolution operator column
        state
    _ = operator
        (∑ column : FiveSectorSlot, resolution.projection column state) := by
      rw [map_sum]
    _ = operator state := by
      rw [resolution.sum_projection_apply]

/-- Equality of continuous linear maps with the sum of all projected blocks. -/
theorem fiveSectorProjectedOperator_eq_sum_blocks
    (resolution : Resolution)
    (operator : E →L[Real] E) :
    operator =
      ∑ row : FiveSectorSlot, ∑ column : FiveSectorSlot,
        fiveSectorProjectedOperatorBlock resolution operator row column := by
  ext state
  symm
  exact fiveSectorProjectedOperatorBlock_sum resolution operator state

/-- Diagonal sector block. -/
def fiveSectorProjectedDiagonalBlock
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (sector : FiveSectorSlot) : E →L[Real] E :=
  fiveSectorProjectedOperatorBlock resolution operator sector sector

/-- Symmetric cross-sector operator attached to an unordered pair. -/
def fiveSectorProjectedCrossBlock
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (first second : FiveSectorSlot) : E →L[Real] E :=
  fiveSectorProjectedOperatorBlock resolution operator first second +
    fiveSectorProjectedOperatorBlock resolution operator second first

/-- Bilinear matrix coefficient of one projected block. -/
def fiveSectorProjectedBlockForm
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (row column : FiveSectorSlot)
    (first second : E) : Real :=
  ⟪first,
    fiveSectorProjectedOperatorBlock resolution operator row column second,
    Real⟫

/-- Quadratic contribution of one diagonal block. -/
def fiveSectorProjectedDiagonalQuadratic
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (sector : FiveSectorSlot)
    (state : E) : Real :=
  ⟪state, fiveSectorProjectedDiagonalBlock resolution operator sector state,
    Real⟫

/-- Quadratic contribution of one symmetric cross block. -/
def fiveSectorProjectedCrossQuadratic
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (first second : FiveSectorSlot)
    (state : E) : Real :=
  ⟪state, fiveSectorProjectedCrossBlock resolution operator first second state,
    Real⟫

/-- Opposite blocks are adjoint to each other when the full operator is
self-adjoint. -/
theorem fiveSectorProjectedBlock_adjoint_pairing
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (hSelfAdjoint : ∀ first second : E,
      ⟪operator first, second, Real⟫ =
        ⟪first, operator second, Real⟫)
    (row column : FiveSectorSlot)
    (first second : E) :
    ⟪fiveSectorProjectedOperatorBlock resolution operator row column first,
        second, Real⟫ =
      ⟪first,
        fiveSectorProjectedOperatorBlock resolution operator column row second,
        Real⟫ := by
  calc
    ⟪fiveSectorProjectedOperatorBlock resolution operator row column first,
        second, Real⟫ =
      ⟪operator (resolution.projection column first),
        resolution.projection row second, Real⟫ := by
      rw [fiveSectorProjectedOperatorBlock_apply,
        resolution.projection_selfAdjoint]
    _ = ⟪resolution.projection column first,
        operator (resolution.projection row second), Real⟫ :=
      hSelfAdjoint _ _
    _ = ⟪first,
        resolution.projection column
          (operator (resolution.projection row second)), Real⟫ := by
      rw [resolution.projection_selfAdjoint]
    _ = ⟪first,
        fiveSectorProjectedOperatorBlock resolution operator column row second,
        Real⟫ := rfl

/-- Each diagonal block of a self-adjoint operator is self-adjoint. -/
theorem fiveSectorProjectedDiagonalBlock_selfAdjoint
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (hSelfAdjoint : ∀ first second : E,
      ⟪operator first, second, Real⟫ =
        ⟪first, operator second, Real⟫)
    (sector : FiveSectorSlot)
    (first second : E) :
    ⟪fiveSectorProjectedDiagonalBlock resolution operator sector first,
        second, Real⟫ =
      ⟪first,
        fiveSectorProjectedDiagonalBlock resolution operator sector second,
        Real⟫ :=
  fiveSectorProjectedBlock_adjoint_pairing resolution operator hSelfAdjoint
    sector sector first second

/-- Each symmetric cross block is self-adjoint. -/
theorem fiveSectorProjectedCrossBlock_selfAdjoint
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (hSelfAdjoint : ∀ first second : E,
      ⟪operator first, second, Real⟫ =
        ⟪first, operator second, Real⟫)
    (firstSector secondSector : FiveSectorSlot)
    (first second : E) :
    ⟪fiveSectorProjectedCrossBlock resolution operator firstSector secondSector
        first, second, Real⟫ =
      ⟪first,
        fiveSectorProjectedCrossBlock resolution operator firstSector
          secondSector second, Real⟫ := by
  simp only [fiveSectorProjectedCrossBlock, ContinuousLinearMap.add_apply,
    inner_add_left, inner_add_right]
  rw [fiveSectorProjectedBlock_adjoint_pairing resolution operator hSelfAdjoint
      firstSector secondSector first second,
    fiveSectorProjectedBlock_adjoint_pairing resolution operator hSelfAdjoint
      secondSector firstSector first second]
  ac_rfl

/-- Public projected-operator checkpoint. -/
theorem five_sector_projected_operator_blocks_gate
    (resolution : Resolution)
    (operator : E →L[Real] E)
    (hSelfAdjoint : ∀ first second : E,
      ⟪operator first, second, Real⟫ =
        ⟪first, operator second, Real⟫) :
    operator =
        ∑ row : FiveSectorSlot, ∑ column : FiveSectorSlot,
          fiveSectorProjectedOperatorBlock resolution operator row column ∧
      (∀ sector first second,
        ⟪fiveSectorProjectedDiagonalBlock resolution operator sector first,
            second, Real⟫ =
          ⟪first,
            fiveSectorProjectedDiagonalBlock resolution operator sector second,
            Real⟫) ∧
      (∀ firstSector secondSector first second,
        ⟪fiveSectorProjectedCrossBlock resolution operator firstSector
            secondSector first, second, Real⟫ =
          ⟪first,
            fiveSectorProjectedCrossBlock resolution operator firstSector
              secondSector second, Real⟫) :=
  ⟨fiveSectorProjectedOperator_eq_sum_blocks resolution operator,
    fiveSectorProjectedDiagonalBlock_selfAdjoint resolution operator
      hSelfAdjoint,
    fiveSectorProjectedCrossBlock_selfAdjoint resolution operator hSelfAdjoint⟩

end
end P0EFTJanusProgramPFiveSectorProjectedOperatorBlocks4D
end JanusFormal
