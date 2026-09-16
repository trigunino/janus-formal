import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D

/-!
# Four-sector identity and fifth-boundary no-go on the current Candidate-A graph

The completed diagonal Candidate-A graph has four actual Hilbert factors:
diffeomorphism, Abelian, matter and LL. Their canonical projectors already
reconstruct every state. Therefore any additional continuous boundary
projector that reconstructs the same graph together with these four is zero.
This concerns the present four-factor graph, not a future enlarged Hilbert
space with an independent boundary/BV factor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalExtendedFourSectorBoundaryNoGo4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D
open P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D

variable {D A M L : Type*}
variable [NormedAddCommGroup D] [InnerProductSpace Real D]
variable [NormedAddCommGroup A] [InnerProductSpace Real A]
variable [NormedAddCommGroup M] [InnerProductSpace Real M]
variable [NormedAddCommGroup L] [InnerProductSpace Real L]

private abbrev Tail2 := WithLp 2 (M × L)
private abbrev Tail1 := WithLp 2 (A × Tail2 (M := M) (L := L))
private abbrev Graph := WithLp 2 (D × Tail1 (A := A) (M := M) (L := L))

/-- The four canonical completed sector projectors exhaust the graph. -/
theorem fourSectorProjectors_reconstruct
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    diffeomorphismProjector x + abelianProjector x + matterProjector x +
      llProjector x = x := by
  calc
    _ = bulkProjector x + matterProjector x + llProjector x := by
      rw [diffeomorphismProjector_add_abelianProjector]
    _ = x := projectors_reconstruct x

/-- A fifth boundary projector cannot contribute to a resolution that already
uses all four canonical projectors of this graph. -/
theorem boundaryProjector_eq_zero
    (boundary : Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
      Graph (D := D) (A := A) (M := M) (L := L))
    (reconstruct : ∀ x,
      diffeomorphismProjector x + abelianProjector x + matterProjector x +
        llProjector x + boundary x = x) :
    boundary = 0 := by
  ext x
  have h := reconstruct x
  rw [fourSectorProjectors_reconstruct] at h
  have h' : x + boundary x = x + 0 := by simpa using h
  exact add_left_cancel h'

/-- A nonzero fifth-boundary mode contradicts reconstruction on this graph. -/
theorem no_nonzero_boundary_mode
    (boundary : Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
      Graph (D := D) (A := A) (M := M) (L := L))
    (reconstruct : ∀ x,
      diffeomorphismProjector x + abelianProjector x + matterProjector x +
        llProjector x + boundary x = x)
    (x : Graph (D := D) (A := A) (M := M) (L := L))
    (nonzero : boundary x ≠ 0) : False := by
  rw [boundaryProjector_eq_zero boundary reconstruct] at nonzero
  exact nonzero rfl

end
end P0EFTJanusProgramPT12DiagonalExtendedFourSectorBoundaryNoGo4D
end JanusFormal
