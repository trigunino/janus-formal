import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D

/-!
# The two genuine completed Candidate-A bulk factors

The diagonal Candidate-A graph already has completed diffeomorphism, Abelian,
matter and LL factors.  Its canonical bulk projector is the sum of the first
two coordinate projectors.  This does not construct an independent boundary/BV
factor or assert that either projector commutes with the Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D

variable {D A M L : Type*}
variable [NormedAddCommGroup D] [InnerProductSpace Real D]
variable [NormedAddCommGroup A] [InnerProductSpace Real A]
variable [NormedAddCommGroup M] [InnerProductSpace Real M]
variable [NormedAddCommGroup L] [InnerProductSpace Real L]

private abbrev Tail2 := WithLp 2 (M × L)
private abbrev Tail1 := WithLp 2 (A × Tail2 (M := M) (L := L))
private abbrev Graph := WithLp 2 (D × Tail1 (A := A) (M := M) (L := L))
private abbrev Raw := D × (A × (M × L))

private def rawD : Raw (D := D) (A := A) (M := M) (L := L) →L[Real]
    Raw (D := D) (A := A) (M := M) (L := L) :=
  (ContinuousLinearMap.fst Real D (A × (M × L))).prod 0

private def rawA : Raw (D := D) (A := A) (M := M) (L := L) →L[Real]
    Raw (D := D) (A := A) (M := M) (L := L) :=
  (0 : Raw (D := D) (A := A) (M := M) (L := L) →L[Real] D).prod
    (((ContinuousLinearMap.fst Real A (M × L)).comp
      (ContinuousLinearMap.snd Real D (A × (M × L)))).prod 0)

/-- Projection onto the existing completed diagonal diffeomorphism graph. -/
def diffeomorphismProjector : Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
    Graph (D := D) (A := A) (M := M) (L := L) :=
  graphCoordinates.symm.toContinuousLinearMap.comp
    (rawD.comp graphCoordinates.toContinuousLinearMap)

/-- Projection onto the existing completed paired-Abelian graph. -/
def abelianProjector : Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
    Graph (D := D) (A := A) (M := M) (L := L) :=
  graphCoordinates.symm.toContinuousLinearMap.comp
    (rawA.comp graphCoordinates.toContinuousLinearMap)

private theorem coordinates_diffeomorphismProjector
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    graphCoordinates (diffeomorphismProjector x) =
      ((graphCoordinates x).1, (0, (0, 0))) := by
  simp [diffeomorphismProjector, rawD] <;> rfl

private theorem coordinates_abelianProjector
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    graphCoordinates (abelianProjector x) =
      (0, ((graphCoordinates x).2.1, (0, 0))) := by
  simp [abelianProjector, rawA] <;> rfl

private theorem diffeomorphismProjector_apply
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    diffeomorphismProjector x =
      WithLp.toLp 2 (x.fst, (0 : Tail1 (A := A) (M := M) (L := L))) := by
  apply graphCoordinates.injective
  rw [coordinates_diffeomorphismProjector]
  simp [graphCoordinates_apply] <;> rfl

private theorem abelianProjector_apply
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    abelianProjector x =
      WithLp.toLp 2 (0,
        WithLp.toLp 2 (x.snd.fst, (0 : Tail2 (M := M) (L := L)))) := by
  apply graphCoordinates.injective
  rw [coordinates_abelianProjector]
  simp [graphCoordinates_apply] <;> rfl

theorem diffeomorphismProjector_idempotent
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    diffeomorphismProjector (diffeomorphismProjector x) =
      diffeomorphismProjector x := by
  apply graphCoordinates.injective
  simp only [coordinates_diffeomorphismProjector] <;> rfl

theorem abelianProjector_idempotent
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    abelianProjector (abelianProjector x) = abelianProjector x := by
  apply graphCoordinates.injective
  simp only [coordinates_abelianProjector] <;> rfl

theorem diffeomorphismProjector_abelianProjector_zero
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    diffeomorphismProjector (abelianProjector x) = 0 := by
  apply graphCoordinates.injective
  simp only [coordinates_diffeomorphismProjector,
    coordinates_abelianProjector, map_zero] <;> rfl

theorem abelianProjector_diffeomorphismProjector_zero
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    abelianProjector (diffeomorphismProjector x) = 0 := by
  apply graphCoordinates.injective
  simp only [coordinates_diffeomorphismProjector,
    coordinates_abelianProjector, map_zero] <;> rfl

theorem diffeomorphismProjector_abelianProjector_inner_zero
    (x y : Graph (D := D) (A := A) (M := M) (L := L)) :
    inner Real (diffeomorphismProjector x) (abelianProjector y) = 0 := by
  rw [diffeomorphismProjector_apply, abelianProjector_apply]
  rw [WithLp.prod_inner_apply]
  simp

/-- The two genuine completed coordinate projectors recover precisely the
canonical bulk projector. -/
theorem diffeomorphismProjector_add_abelianProjector
    (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    diffeomorphismProjector x + abelianProjector x = bulkProjector x := by
  apply graphCoordinates.injective
  rw [map_add, coordinates_diffeomorphismProjector,
    coordinates_abelianProjector]
  change _ = ((graphCoordinates x).1, ((graphCoordinates x).2.1, (0, 0)))
  simp

end
end P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D
end JanusFormal
