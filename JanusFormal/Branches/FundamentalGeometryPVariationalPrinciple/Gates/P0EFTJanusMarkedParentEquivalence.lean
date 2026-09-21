import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkBoundaryShearEquivalence
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkSpectralResponseSeparation

/-!
# Bulk rescaling, boundary shears and marked observables

For positive scalar bulk coefficients, equality of the static Schur potential
classifies parents under all invertible linear bulk changes fixing the boundary.
A fixed unit spectral quadratic form restricts these changes to a bulk sign;
a fixed linear bulk source removes even that sign. These are explicit algebraic
categories, not a derivation of the physical markings or a Janus selector.
-/

namespace JanusFormal
namespace P0EFTJanusMarkedParentEquivalence

set_option autoImplicit false

open P0EFTJanusParentBulkHelmholtzReciprocity
open P0EFTJanusParentBulkMicroscopicFingerprintSelection
open P0EFTJanusParentBulkBoundaryShearEquivalence
open P0EFTJanusParentBulkSpectralResponseSeparation

noncomputable def rescaleParent (parent : ParentBulkTwoSectorData)
    (r : ℝ) (hr : r ≠ 0) : ParentBulkTwoSectorData where
  bulkCoefficient := parent.bulkCoefficient * r ^ 2
  bulkToNormal := parent.bulkToNormal * r
  bulkToTrace := parent.bulkToTrace * r
  boundaryNormal := parent.boundaryNormal
  boundaryMixing := parent.boundaryMixing
  boundaryTrace := parent.boundaryTrace
  bulkCoefficientNonzero := mul_ne_zero parent.bulkCoefficientNonzero (pow_ne_zero 2 hr)

theorem rescale_parent_action (parent : ParentBulkTwoSectorData)
    (r : ℝ) (hr : r ≠ 0) (x n t : ℝ) :
    parentAction (rescaleParent parent r hr) x n t =
      parentAction parent (r * x) n t := by
  simp only [parentAction, rescaleParent]
  ring

theorem rescale_parent_reduced_potential (parent : ParentBulkTwoSectorData)
    (r : ℝ) (hr : r ≠ 0) :
    reducedPotential (rescaleParent parent r hr) = reducedPotential parent := by
  ext <;>
    simp only [reducedPotential, reducedNormalCoefficient, reducedMixingCoefficient,
      reducedTraceCoefficient, rescaleParent] <;>
    field_simp [parent.bulkCoefficientNonzero, hr]

/-- The general invertible linear bulk coordinate at fixed boundary. -/
noncomputable def bulkCoordinate (r u v : ℝ) (hr : r ≠ 0)
    (n t : ℝ) : ℝ ≃ ℝ where
  toFun x := r * (x + u * n + v * t)
  invFun x := x / r - u * n - v * t
  left_inv x := by dsimp; field_simp; ring
  right_inv x := by dsimp; field_simp; ring

noncomputable def transformedParent (parent : ParentBulkTwoSectorData)
    (r u v : ℝ) (hr : r ≠ 0) : ParentBulkTwoSectorData :=
  shearParent (rescaleParent parent r hr) u v

theorem transformed_parent_action (parent : ParentBulkTwoSectorData)
    (r u v : ℝ) (hr : r ≠ 0) (x n t : ℝ) :
    parentAction (transformedParent parent r u v hr) x n t =
      parentAction parent (bulkCoordinate r u v hr n t x) n t := by
  rw [transformedParent, shear_parent_action, rescale_parent_action]
  rfl

def BoundaryLinearEquivalent (first second : ParentBulkTwoSectorData) : Prop :=
  ∃ (r u v : ℝ) (hr : r ≠ 0), second = transformedParent first r u v hr

/-- Allowing bulk rescaling removes the bulk coefficient as an invariant on
the positive branch. No spectral inner product is kept fixed here. -/
theorem positive_boundary_linear_equivalent_iff
    (first second : ParentBulkTwoSectorData)
    (hFirst : 0 < first.bulkCoefficient) (hSecond : 0 < second.bulkCoefficient) :
    BoundaryLinearEquivalent first second ↔
      reducedPotential first = reducedPotential second := by
  constructor
  · rintro ⟨r, u, v, hr, rfl⟩
    rw [transformedParent, shear_parent_reduced_potential,
      rescale_parent_reduced_potential]
  · intro hReduced
    let r := Real.sqrt (second.bulkCoefficient / first.bulkCoefficient)
    have hRatio : 0 < second.bulkCoefficient / first.bulkCoefficient := div_pos hSecond hFirst
    have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hRatio)
    have hrSq : r ^ 2 = second.bulkCoefficient / first.bulkCoefficient :=
      Real.sq_sqrt (le_of_lt hRatio)
    have hBulk : (rescaleParent first r hr).bulkCoefficient = second.bulkCoefficient := by
      simp only [rescaleParent, hrSq]
      field_simp
    have hEquiv : BoundaryShearEquivalent (rescaleParent first r hr) second :=
      (boundary_shear_equivalent_iff _ _).2
        ⟨hBulk, (rescale_parent_reduced_potential first r hr).trans hReduced⟩
    rcases hEquiv with ⟨u, v, h⟩
    exact ⟨r, u, v, hr, h⟩

/-- Keeping the normalized spectral term `-z*x²/2` means preserving `x²`
for every bulk and boundary input. -/
def PreservesSpectralMark (r u v : ℝ) : Prop :=
  ∀ x n t : ℝ, (r * (x + u * n + v * t)) ^ 2 = x ^ 2

theorem preserves_spectral_mark_iff (r u v : ℝ) :
    PreservesSpectralMark r u v ↔ (r = 1 ∨ r = -1) ∧ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hr := h 1 0 0
    have hu := h 0 1 0
    have hv := h 0 0 1
    norm_num at hr hu hv
    have hrSign : r = 1 ∨ r = -1 :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using hr)
    refine ⟨hrSign, ?_, ?_⟩
    · rcases hrSign with rfl | rfl <;> norm_num at hu <;> nlinarith [sq_nonneg u]
    · rcases hrSign with rfl | rfl <;> norm_num at hv <;> nlinarith [sq_nonneg v]
  · rintro ⟨rfl | rfl, rfl, rfl⟩ <;>
      intro x n t <;> simp

/-- A fixed marked source couples as `-J*x` for every independent source J. -/
def PreservesBulkSource (r u v : ℝ) : Prop :=
  ∀ J x n t : ℝ, J * (r * (x + u * n + v * t)) = J * x

theorem preserves_bulk_source_iff (r u v : ℝ) :
    PreservesBulkSource r u v ↔ r = 1 ∧ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hr := h 1 1 0 0
    have hu := h 1 0 1 0
    have hv := h 1 0 0 1
    norm_num at hr
    subst r
    exact ⟨rfl, by simpa using hu, by simpa using hv⟩
  · rintro ⟨rfl, rfl, rfl⟩
    intro J x n t
    simp

/-- The restricted equivalence becomes equality when the source marking is
held fixed. This does not supply the missing physical source from Janus data. -/
theorem source_preserving_transformed_parent_eq
    (parent : ParentBulkTwoSectorData) (r u v : ℝ) (hr : r ≠ 0)
    (hSource : PreservesBulkSource r u v) :
    transformedParent parent r u v hr = parent := by
  rcases (preserves_bulk_source_iff r u v).1 hSource with ⟨rfl, rfl, rfl⟩
  apply same_fingerprint_and_reduced_potential_select_parent
  · simp [SameMicroscopicBulkFingerprint, transformedParent, shearParent, rescaleParent]
  · rw [transformedParent, shear_parent_reduced_potential, rescale_parent_reduced_potential]

/-- The positive coupled examples are equivalent if the spectral marking is
forgotten: their distinct normalized responses are not unmarked invariants. -/
theorem coupled_examples_unmarked_equivalent (k : ℝ) :
    BoundaryLinearEquivalent (unitBulkParent k) (doubleBulkParent k) := by
  apply (positive_boundary_linear_equivalent_iff _ _
    (by norm_num [unitBulkParent]) (by norm_num [doubleBulkParent])).2
  exact (both_parents_have_same_static_schur_data k).1

/-- With the normalized bulk spectral form retained, the same pair cannot be
related by any of the declared boundary-preserving linear field changes. -/
theorem coupled_examples_not_spectral_marked_equivalent (k : ℝ) :
    ¬ ∃ (r u v : ℝ) (hr : r ≠ 0), PreservesSpectralMark r u v ∧
      doubleBulkParent k = transformedParent (unitBulkParent k) r u v hr := by
  rintro ⟨r, u, v, hr, hMark, hParent⟩
  have hBulk := congrArg ParentBulkTwoSectorData.bulkCoefficient hParent
  rcases (preserves_spectral_mark_iff r u v).1 hMark with ⟨hSign, rfl, rfl⟩
  rcases hSign with rfl | rfl <;>
    norm_num [doubleBulkParent, unitBulkParent, transformedParent,
      shearParent, rescaleParent] at hBulk

end P0EFTJanusMarkedParentEquivalence
end JanusFormal
