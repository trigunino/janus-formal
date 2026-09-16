import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalExtendedFourSectorBoundaryNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D

/-!
# Canonical self-adjoint resolution of the completed four-factor graph

The existing diagonal Candidate-A graph has four completed Hilbert factors.
Its four coordinate projectors give an exact self-adjoint resolution and a
Pythagorean norm identity. No independent boundary/BV factor is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalExtendedFourSectorSelfAdjointResolution4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D
open P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D
open P0EFTJanusProgramPT12DiagonalExtendedFourSectorBoundaryNoGo4D
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D

variable {D A M L : Type*}
variable [NormedAddCommGroup D] [InnerProductSpace Real D]
variable [NormedAddCommGroup A] [InnerProductSpace Real A]
variable [NormedAddCommGroup M] [InnerProductSpace Real M]
variable [NormedAddCommGroup L] [InnerProductSpace Real L]

private abbrev Tail2 := WithLp 2 (M × L)
private abbrev Tail1 := WithLp 2 (A × Tail2 (M := M) (L := L))
private abbrev Graph := WithLp 2 (D × Tail1 (A := A) (M := M) (L := L))

/-- The four genuinely completed diagonal graph factors. -/
inductive FourSectorSlot
  | diffeomorphism
  | abelian
  | matter
  | ll
  deriving DecidableEq, Fintype

/-- Canonical coordinate projector in each completed sector. -/
def sectorProjector (sector : FourSectorSlot) :
    Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
      Graph (D := D) (A := A) (M := M) (L := L) :=
  match sector with
  | .diffeomorphism => diffeomorphismProjector
  | .abelian => abelianProjector
  | .matter => matterProjector
  | .ll => llProjector

private theorem diffeomorphismProjector_apply
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    diffeomorphismProjector x =
      WithLp.toLp 2 (x.fst, (0 : Tail1 (A := A) (M := M) (L := L))) := by
  apply graphCoordinates.injective
  simp [diffeomorphismProjector, graphCoordinates_apply]
  rfl

private theorem abelianProjector_apply
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    abelianProjector x =
      WithLp.toLp 2 (0,
        WithLp.toLp 2 (x.snd.fst, (0 : Tail2 (M := M) (L := L)))) := by
  apply graphCoordinates.injective
  simp [abelianProjector, graphCoordinates_apply]
  rfl

private theorem matterProjector_apply
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    matterProjector x =
      WithLp.toLp 2 (0,
        WithLp.toLp 2 (0,
          WithLp.toLp 2 (x.snd.snd.fst, (0 : L)))) := by
  apply graphCoordinates.injective
  simp [matterProjector, graphCoordinates_apply]
  rfl

private theorem llProjector_apply
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    llProjector x =
      WithLp.toLp 2 (0,
        WithLp.toLp 2 (0,
          WithLp.toLp 2 (0, x.snd.snd.snd))) := by
  apply graphCoordinates.injective
  simp [llProjector, graphCoordinates_apply]
  rfl

private theorem diffeomorphismProjector_symmetric
    (x y : Graph (D := D) (A := A) (M := M) (L := L)) :
    inner Real (diffeomorphismProjector x) y =
      inner Real x (diffeomorphismProjector y) := by
  rw [diffeomorphismProjector_apply, diffeomorphismProjector_apply]
  simp [WithLp.prod_inner_apply]

private theorem abelianProjector_symmetric
    (x y : Graph (D := D) (A := A) (M := M) (L := L)) :
    inner Real (abelianProjector x) y =
      inner Real x (abelianProjector y) := by
  rw [abelianProjector_apply, abelianProjector_apply]
  simp [WithLp.prod_inner_apply]

private theorem matterProjector_symmetric
    (x y : Graph (D := D) (A := A) (M := M) (L := L)) :
    inner Real (matterProjector x) y =
      inner Real x (matterProjector y) := by
  rw [matterProjector_apply, matterProjector_apply]
  simp [WithLp.prod_inner_apply]

private theorem llProjector_symmetric
    (x y : Graph (D := D) (A := A) (M := M) (L := L)) :
    inner Real (llProjector x) y =
      inner Real x (llProjector y) := by
  rw [llProjector_apply, llProjector_apply]
  simp [WithLp.prod_inner_apply]

private theorem matterProjector_idempotent
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    matterProjector (matterProjector x) = matterProjector x := by
  rw [matterProjector_apply, matterProjector_apply]
  rfl

private theorem llProjector_idempotent
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    llProjector (llProjector x) = llProjector x := by
  rw [llProjector_apply, llProjector_apply]
  rfl

private theorem four_sector_univ :
    (Finset.univ : Finset FourSectorSlot) =
      { .diffeomorphism, .abelian, .matter, .ll } := by
  decide

/-- Exact self-adjoint projection resolution on the existing four-factor graph. -/
def fourSectorSelfAdjointResolution :
    FiniteSelfAdjointProjectionResolutionData
      (Sector := FourSectorSlot)
      (E := Graph (D := D) (A := A) (M := M) (L := L)) where
  projection := sectorProjector
  sum_projection := by
    intro x
    rw [four_sector_univ]
    simpa [sectorProjector, add_assoc] using fourSectorProjectors_reconstruct x
  projection_idempotent := by
    intro sector x
    cases sector with
    | diffeomorphism => exact diffeomorphismProjector_idempotent x
    | abelian => exact abelianProjector_idempotent x
    | matter => exact matterProjector_idempotent x
    | ll => exact llProjector_idempotent x
  projection_symmetric := by
    intro sector x y
    cases sector with
    | diffeomorphism => exact diffeomorphismProjector_symmetric x y
    | abelian => exact abelianProjector_symmetric x y
    | matter => exact matterProjector_symmetric x y
    | ll => exact llProjector_symmetric x y

/-- The actual four graph factors satisfy Pythagoras. -/
theorem fourSector_norm_sq_decomposition
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    ‖x‖ ^ 2 =
      ∑ sector : FourSectorSlot,
        ‖(fourSectorSelfAdjointResolution (D := D) (A := A) (M := M)
          (L := L)).projection sector x‖ ^ 2 :=
  (fourSectorSelfAdjointResolution (D := D) (A := A) (M := M)
    (L := L)).norm_sq_decomposition x

end
end P0EFTJanusProgramPT12DiagonalExtendedFourSectorSelfAdjointResolution4D
end JanusFormal
