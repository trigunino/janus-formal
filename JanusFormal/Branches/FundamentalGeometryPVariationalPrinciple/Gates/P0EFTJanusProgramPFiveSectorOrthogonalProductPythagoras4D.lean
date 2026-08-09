import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D

/-!
# Pythagoras for the five-sector orthogonal product resolution

The sector projectors are self-adjoint, idempotent, mutually orthogonal and
resolve the identity.  Therefore the Hilbert norm decomposes exactly as the sum
of the five projected norm squares.  In particular every projector is a
contraction.

These statements are consequences of the effective orthogonal product
coordinates and need not be repeated in any Gårding packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Topology
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D

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

private abbrev Resolution :=
  FiveSectorOrthogonalProductDecomposition
    (E := E)
    (MetricDiffeomorphism := MetricDiffeomorphism)
    (AbelianGauge := AbelianGauge)
    (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
    (LongitudinalLL := LongitudinalLL)
    (BoundaryFiniteBV := BoundaryFiniteBV)

/-- Exact Pythagorean identity for the five generated projectors. -/
theorem fiveSectorProjection_norm_sq_sum
    (resolution : Resolution) (state : E) :
    ‖state‖ ^ 2 =
      ∑ sector : FiveSectorSlot,
        ‖resolution.projection sector state‖ ^ 2 := by
  calc
    ‖state‖ ^ 2 = ⟪state, state, Real⟫ :=
      real_inner_self_eq_norm_sq.symm
    _ = ⟪∑ sector : FiveSectorSlot,
          resolution.projection sector state, state, Real⟫ := by
      rw [resolution.sum_projection_apply]
    _ = ∑ sector : FiveSectorSlot,
          ⟪resolution.projection sector state, state, Real⟫ := by
      simp
    _ = ∑ sector : FiveSectorSlot,
          ⟪resolution.projection sector state,
            resolution.projection sector state, Real⟫ := by
      apply Finset.sum_congr rfl
      intro sector _
      calc
        ⟪resolution.projection sector state, state, Real⟫ =
            ⟪resolution.projection sector
                (resolution.projection sector state), state, Real⟫ := by
          rw [resolution.projection_idempotent]
        _ = ⟪resolution.projection sector state,
              resolution.projection sector state, Real⟫ :=
          resolution.projection_selfAdjoint sector
            (resolution.projection sector state) state
    _ = ∑ sector : FiveSectorSlot,
          ‖resolution.projection sector state‖ ^ 2 := by
      simp [real_inner_self_eq_norm_sq]

/-- Every generated sector projector decreases the norm. -/
theorem fiveSectorProjection_norm_le
    (resolution : Resolution) (sector : FiveSectorSlot) (state : E) :
    ‖resolution.projection sector state‖ ≤ ‖state‖ := by
  have hTerm :
      ‖resolution.projection sector state‖ ^ 2 ≤
        ∑ current : FiveSectorSlot,
          ‖resolution.projection current state‖ ^ 2 := by
    apply Finset.single_le_sum
    · intro current _ hCurrent
      exact sq_nonneg ‖resolution.projection current state‖
    · exact Finset.mem_univ sector
  rw [← fiveSectorProjection_norm_sq_sum resolution state] at hTerm
  nlinarith [norm_nonneg (resolution.projection sector state),
    norm_nonneg state]

/-- Operator norm of every generated projection is at most one. -/
theorem fiveSectorProjection_opNorm_le_one
    (resolution : Resolution) (sector : FiveSectorSlot) :
    ‖resolution.projection sector‖ ≤ 1 := by
  apply (resolution.projection sector).opNorm_le_bound zero_le_one
  intro state
  simpa using fiveSectorProjection_norm_le resolution sector state

/-- Pairwise projected sums satisfy the expected orthogonal norm formula. -/
theorem fiveSectorProjection_pair_norm_sq
    (resolution : Resolution)
    (first second : FiveSectorSlot) (hDistinct : first ≠ second)
    (state : E) :
    ‖resolution.projection first state +
        resolution.projection second state‖ ^ 2 =
      ‖resolution.projection first state‖ ^ 2 +
        ‖resolution.projection second state‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right]
  rw [resolution.projection_orthogonal first second hDistinct state state]
  rw [real_inner_comm]
  rw [resolution.projection_orthogonal first second hDistinct state state]
  simp [real_inner_self_eq_norm_sq]

/-- Public Pythagorean checkpoint. -/
theorem five_sector_orthogonal_product_pythagoras_gate
    (resolution : Resolution) :
    (∀ state,
      ‖state‖ ^ 2 =
        ∑ sector : FiveSectorSlot,
          ‖resolution.projection sector state‖ ^ 2) ∧
      (∀ sector state,
        ‖resolution.projection sector state‖ ≤ ‖state‖) ∧
      (∀ sector, ‖resolution.projection sector‖ ≤ 1) :=
  ⟨fiveSectorProjection_norm_sq_sum resolution,
    fiveSectorProjection_norm_le resolution,
    fiveSectorProjection_opNorm_le_one resolution⟩

end
end P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D
end JanusFormal
