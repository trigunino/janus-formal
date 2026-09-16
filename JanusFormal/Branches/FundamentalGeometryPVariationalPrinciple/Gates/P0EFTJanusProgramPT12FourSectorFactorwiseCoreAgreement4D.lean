import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D

/-!
# Four-sector projectors preserve factorwise smooth-core embeddings

This generic algebraic lemma isolates the four coordinate calculations from the
physical graph embeddings.  Each factor may have a different linear embedding.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FourSectorFactorwiseCoreAgreement4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D
open P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D

variable {D₀ A₀ M₀ L₀ D A M L : Type*}
variable [AddCommMonoid D₀] [Module Real D₀]
variable [AddCommMonoid A₀] [Module Real A₀]
variable [AddCommMonoid M₀] [Module Real M₀]
variable [AddCommMonoid L₀] [Module Real L₀]
variable [NormedAddCommGroup D] [InnerProductSpace Real D]
variable [NormedAddCommGroup A] [InnerProductSpace Real A]
variable [NormedAddCommGroup M] [InnerProductSpace Real M]
variable [NormedAddCommGroup L] [InnerProductSpace Real L]

private abbrev Core := (D₀ × A₀) × (M₀ × L₀)
private abbrev Tail2 := WithLp 2 (M × L)
private abbrev Tail1 := WithLp 2 (A × Tail2 (M := M) (L := L))
private abbrev Graph := WithLp 2 (D × Tail1 (A := A) (M := M) (L := L))

/-- A coordinatewise linear core embedding into the genuine L² graph. -/
def factorwiseEmbedding
    (eD : D₀ →ₗ[Real] D) (eA : A₀ →ₗ[Real] A)
    (eM : M₀ →ₗ[Real] M) (eL : L₀ →ₗ[Real] L)
    (core : Core (D₀ := D₀) (A₀ := A₀) (M₀ := M₀) (L₀ := L₀)) :
    Graph (D := D) (A := A) (M := M) (L := L) :=
  WithLp.toLp 2 (eD core.1.1,
    WithLp.toLp 2 (eA core.1.2,
      WithLp.toLp 2 (eM core.2.1, eL core.2.2)))

theorem diffeomorphismProjector_factorwiseEmbedding
    (eD : D₀ →ₗ[Real] D) (eA : A₀ →ₗ[Real] A)
    (eM : M₀ →ₗ[Real] M) (eL : L₀ →ₗ[Real] L)
    (core : Core (D₀ := D₀) (A₀ := A₀) (M₀ := M₀) (L₀ := L₀)) :
    diffeomorphismProjector (factorwiseEmbedding eD eA eM eL core) =
      factorwiseEmbedding eD eA eM eL ((core.1.1, 0), (0, 0)) := by
  apply graphCoordinates.injective
  change (eD core.1.1, (0, (0, 0))) =
    (eD core.1.1, (eA 0, (eM 0, eL 0)))
  simp only [map_zero]

theorem abelianProjector_factorwiseEmbedding
    (eD : D₀ →ₗ[Real] D) (eA : A₀ →ₗ[Real] A)
    (eM : M₀ →ₗ[Real] M) (eL : L₀ →ₗ[Real] L)
    (core : Core (D₀ := D₀) (A₀ := A₀) (M₀ := M₀) (L₀ := L₀)) :
    abelianProjector (factorwiseEmbedding eD eA eM eL core) =
      factorwiseEmbedding eD eA eM eL ((0, core.1.2), (0, 0)) := by
  apply graphCoordinates.injective
  change (0, (eA core.1.2, (0, 0))) =
    (eD 0, (eA core.1.2, (eM 0, eL 0)))
  simp only [map_zero]

theorem matterProjector_factorwiseEmbedding
    (eD : D₀ →ₗ[Real] D) (eA : A₀ →ₗ[Real] A)
    (eM : M₀ →ₗ[Real] M) (eL : L₀ →ₗ[Real] L)
    (core : Core (D₀ := D₀) (A₀ := A₀) (M₀ := M₀) (L₀ := L₀)) :
    matterProjector (factorwiseEmbedding eD eA eM eL core) =
      factorwiseEmbedding eD eA eM eL ((0, 0), (core.2.1, 0)) := by
  apply graphCoordinates.injective
  change (0, (0, (eM core.2.1, 0))) =
    (eD 0, (eA 0, (eM core.2.1, eL 0)))
  simp only [map_zero]

theorem llProjector_factorwiseEmbedding
    (eD : D₀ →ₗ[Real] D) (eA : A₀ →ₗ[Real] A)
    (eM : M₀ →ₗ[Real] M) (eL : L₀ →ₗ[Real] L)
    (core : Core (D₀ := D₀) (A₀ := A₀) (M₀ := M₀) (L₀ := L₀)) :
    llProjector (factorwiseEmbedding eD eA eM eL core) =
      factorwiseEmbedding eD eA eM eL ((0, 0), (0, core.2.2)) := by
  apply graphCoordinates.injective
  change (0, (0, (0, eL core.2.2))) =
    (eD 0, (eA 0, (eM 0, eL core.2.2)))
  simp only [map_zero]

end
end P0EFTJanusProgramPT12FourSectorFactorwiseCoreAgreement4D
end JanusFormal
