import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkMicroscopicFingerprintSelection

/-!
# Quadratic parents modulo boundary-preserving bulk shears

In the unmarked scalar model, `x ↦ x + u n + v t` is an invertible change
of bulk coordinate at fixed boundary data. Its orbits are classified by the
bulk quadratic coefficient and the reduced potential. In particular, the
reference/shifted fingerprint counterexample is one orbit, not two inequivalent
physical theories. This category does not fix a bulk observable or its source,
nor claim to preserve geometric traces, locality or a quantum measure.
No microscopic selector or terminal T08 closure is constructed here.
-/

namespace JanusFormal
namespace P0EFTJanusParentBulkBoundaryShearEquivalence

set_option autoImplicit false

open P0EFTJanusCoupledSectorHelmholtzSelection
open P0EFTJanusParentBulkHelmholtzReciprocity
open P0EFTJanusParentBulkMicroscopicFingerprintSelection

/-- An invertible bulk coordinate change with both boundary coordinates fixed. -/
noncomputable def bulkShear (u v normal trace : ℝ) : ℝ ≃ ℝ where
  toFun x := x + u * normal + v * trace
  invFun x := x - u * normal - v * trace
  left_inv x := by dsimp; ring
  right_inv x := by dsimp; ring

/-- Pull back the parent action by the declared bulk shear. -/
noncomputable def shearParent (parent : ParentBulkTwoSectorData)
    (u v : ℝ) : ParentBulkTwoSectorData where
  bulkCoefficient := parent.bulkCoefficient
  bulkToNormal := parent.bulkToNormal + parent.bulkCoefficient * u
  bulkToTrace := parent.bulkToTrace + parent.bulkCoefficient * v
  boundaryNormal := parent.boundaryNormal + 2 * parent.bulkToNormal * u +
    parent.bulkCoefficient * u ^ 2
  boundaryMixing := parent.boundaryMixing + parent.bulkToNormal * v +
    parent.bulkToTrace * u + parent.bulkCoefficient * u * v
  boundaryTrace := parent.boundaryTrace + 2 * parent.bulkToTrace * v +
    parent.bulkCoefficient * v ^ 2
  bulkCoefficientNonzero := parent.bulkCoefficientNonzero

theorem shear_parent_action (parent : ParentBulkTwoSectorData)
    (u v x normal trace : ℝ) :
    parentAction (shearParent parent u v) x normal trace =
      parentAction parent (bulkShear u v normal trace x) normal trace := by
  simp only [parentAction, shearParent, bulkShear, Equiv.coe_fn_mk]
  ring

theorem shear_parent_reduced_potential (parent : ParentBulkTwoSectorData)
    (u v : ℝ) :
    reducedPotential (shearParent parent u v) = reducedPotential parent := by
  ext <;>
    simp only [reducedPotential, reducedNormalCoefficient,
      reducedMixingCoefficient, reducedTraceCoefficient, shearParent] <;>
    field_simp [parent.bulkCoefficientNonzero] <;> ring

/-- Only the explicitly declared shears are admitted, with no bulk rescaling. -/
def BoundaryShearEquivalent (first second : ParentBulkTwoSectorData) : Prop :=
  ∃ u v : ℝ, second = shearParent first u v

/-- Complete orbit invariants for the declared algebraic category. -/
theorem boundary_shear_equivalent_iff (first second : ParentBulkTwoSectorData) :
    BoundaryShearEquivalent first second ↔
      first.bulkCoefficient = second.bulkCoefficient ∧
      reducedPotential first = reducedPotential second := by
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨rfl, (shear_parent_reduced_potential first u v).symm⟩
  · rintro ⟨hBulk, hReduced⟩
    refine ⟨(second.bulkToNormal - first.bulkToNormal) / first.bulkCoefficient,
      (second.bulkToTrace - first.bulkToTrace) / first.bulkCoefficient, ?_⟩
    apply same_fingerprint_and_reduced_potential_select_parent
    · refine ⟨hBulk.symm, ?_, ?_⟩ <;>
        simp only [shearParent] <;>
        field_simp [first.bulkCoefficientNonzero] <;> ring
    · rw [shear_parent_reduced_potential]
      exact hReduced.symm

theorem boundary_shear_equivalence : Equivalence BoundaryShearEquivalent where
  refl first := (boundary_shear_equivalent_iff first first).2 ⟨rfl, rfl⟩
  symm := by
    intro first second h
    rcases (boundary_shear_equivalent_iff first second).1 h with ⟨ha, hk⟩
    exact (boundary_shear_equivalent_iff second first).2 ⟨ha.symm, hk.symm⟩
  trans := by
    intro first second third h12 h23
    rcases (boundary_shear_equivalent_iff first second).1 h12 with ⟨ha, hk⟩
    rcases (boundary_shear_equivalent_iff second third).1 h23 with ⟨hb, hl⟩
    exact (boundary_shear_equivalent_iff first third).2 ⟨ha.trans hb, hk.trans hl⟩

/-- The existing distinct-coefficient witness is exactly the shear `x ↦ x+n`. -/
theorem shifted_completion_is_shear (target : ReducedTwoSectorTarget) :
    parentCompletion shiftedFingerprint target =
      shearParent (parentCompletion referenceFingerprint target) 1 0 := by
  apply same_fingerprint_and_reduced_potential_select_parent
  · norm_num [SameMicroscopicBulkFingerprint, parentCompletion,
      referenceFingerprint, shiftedFingerprint, shearParent]
  · rw [shear_parent_reduced_potential, parent_completion_reduces_exactly,
      parent_completion_reduces_exactly]

theorem shifted_completion_action (target : ReducedTwoSectorTarget)
    (x normal trace : ℝ) :
    parentAction (parentCompletion shiftedFingerprint target) x normal trace =
      parentAction (parentCompletion referenceFingerprint target)
        (x + normal) normal trace := by
  rw [shifted_completion_is_shear, shear_parent_action]
  simp [bulkShear]

/-- A source for the *marked* bulk coordinate must also be transported.
Keeping the source term `-J*x` fixed leaves the displayed boundary term. -/
theorem shear_with_fixed_bulk_source (parent : ParentBulkTwoSectorData)
    (u v J x normal trace : ℝ) :
    parentAction (shearParent parent u v) x normal trace - J * x =
      (parentAction parent (bulkShear u v normal trace x) normal trace -
        J * bulkShear u v normal trace x) + J * (u * normal + v * trace) := by
  rw [shear_parent_action]
  simp only [bulkShear, Equiv.coe_fn_mk]
  ring

end P0EFTJanusParentBulkBoundaryShearEquivalence
end JanusFormal
