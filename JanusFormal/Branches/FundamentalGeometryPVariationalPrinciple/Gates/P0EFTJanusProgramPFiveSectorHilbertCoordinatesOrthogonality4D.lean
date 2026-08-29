import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

/-!
# Orthogonality of the five canonical Hilbert coordinate sectors

The five projectors induced by one linear isometric product decomposition do
more than annihilate one another algebraically: their ranges are pairwise
orthogonal for the ambient Hilbert inner product.

This is the exact ingredient needed to identify the projected physical Gram
matrix as a five-block diagonal matrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorHilbertCoordinatesOrthogonality4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace BigOperators
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D

variable
  {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- Images of two distinct canonical sector projectors are orthogonal. -/
theorem sectorProjector_inner_sectorProjector_eq_zero
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    {first second : FivePhysicalSector} (hSector : first ≠ second)
    (x y : E) :
    inner Real (coordinates.sectorProjector first x)
        (coordinates.sectorProjector second y) = 0 := by
  let u := coordinates.sectorProjector first x
  let v := coordinates.sectorProjector second y
  have hNorm : ‖u + v‖ = ‖u - v‖ := by
    rw [← coordinates.decomposition.norm_map (u + v),
      ← coordinates.decomposition.norm_map (u - v)]
    rw [map_add, map_sub]
    dsimp [u, v]
    cases first <;> cases second <;>
      simp [FiveSectorHilbertCoordinates.sectorProjector,
        fiveSectorMetricAxis, fiveSectorAbelianAxis, fiveSectorMatterAxis,
        fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis,
        fiveSectorMetricCoordinate, fiveSectorAbelianCoordinate,
        fiveSectorMatterCoordinate, fiveSectorLongitudinalCoordinate,
        fiveSectorBoundaryCoordinate] at hSector ⊢
  have hPolarization :=
    re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four
      (𝕜 := Real) u v
  rw [hNorm] at hPolarization
  simpa [u, v] using hPolarization

/-- Any vectors fixed by two distinct sector projectors are orthogonal. -/
theorem inner_eq_zero_of_sectorProjector_fixed
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    {first second : FivePhysicalSector} (hSector : first ≠ second)
    {x y : E}
    (hFirst : coordinates.sectorProjector first x = x)
    (hSecond : coordinates.sectorProjector second y = y) :
    inner Real x y = 0 := by
  rw [← hFirst, ← hSecond]
  exact sectorProjector_inner_sectorProjector_eq_zero coordinates hSector x y

/-- Public orthogonal-sector checkpoint. -/
theorem five_sector_hilbert_coordinates_orthogonality_gate
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)) :
    ∀ first second, first ≠ second → ∀ x y,
      inner Real (coordinates.sectorProjector first x)
          (coordinates.sectorProjector second y) = 0 :=
  fun _ _ hSector =>
    sectorProjector_inner_sectorProjector_eq_zero coordinates hSector

end
end P0EFTJanusProgramPFiveSectorHilbertCoordinatesOrthogonality4D
end JanusFormal
