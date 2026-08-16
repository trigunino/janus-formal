import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorProjectedOperatorBlocks4D

/-!
# Five-sector resolution from one linear isometry equivalence

The most economical orthogonal-coordinate input is a single linear isometry

`E ≃ₗᵢ[ℝ] M × A × S × L × B`.

Its continuity and preservation of the real inner product are automatic.  This
file converts such an isometry into the complete orthogonal product resolution,
including projectors, Pythagoras and projected operator blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorLinearIsometryResolution4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D
open P0EFTJanusProgramPFiveSectorProjectedOperatorBlocks4D

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

/-- Convert one isometric five-sector coordinate map into the generic
orthogonal product decomposition. -/
def fiveSectorOrthogonalProductDecompositionOfIsometry
    (decomposition : E ≃ₗᵢ[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV) :
    FiveSectorOrthogonalProductDecomposition
      (E := E)
      (MetricDiffeomorphism := MetricDiffeomorphism)
      (AbelianGauge := AbelianGauge)
      (PrimitiveSpinCMatter := PrimitiveSpinCMatter)
      (LongitudinalLL := LongitudinalLL)
      (BoundaryFiniteBV := BoundaryFiniteBV) where
  decomposition := decomposition.toContinuousLinearEquiv
  inner_map := by
    intro first second
    exact decomposition.inner_map_map first second

/-- Public one-isometry checkpoint. -/
theorem five_sector_linear_isometry_resolution_gate
    (decomposition : E ≃ₗᵢ[Real]
      FiveSectorProduct MetricDiffeomorphism AbelianGauge PrimitiveSpinCMatter
        LongitudinalLL BoundaryFiniteBV) :
    let resolution :=
      fiveSectorOrthogonalProductDecompositionOfIsometry decomposition
    (∀ sector state,
      resolution.projection sector (resolution.projection sector state) =
        resolution.projection sector state) ∧
      (∀ sector first second,
        ⟪resolution.projection sector first, second, Real⟫ =
          ⟪first, resolution.projection sector second, Real⟫) ∧
      (∀ state,
        ‖state‖ ^ 2 =
          ∑ sector : FiveSectorSlot,
            ‖resolution.projection sector state‖ ^ 2) := by
  dsimp only
  let resolution :=
    fiveSectorOrthogonalProductDecompositionOfIsometry decomposition
  exact
    ⟨resolution.projection_idempotent,
      resolution.projection_selfAdjoint,
      fiveSectorProjection_norm_sq_sum resolution⟩

end
end P0EFTJanusProgramPFiveSectorLinearIsometryResolution4D
end JanusFormal
