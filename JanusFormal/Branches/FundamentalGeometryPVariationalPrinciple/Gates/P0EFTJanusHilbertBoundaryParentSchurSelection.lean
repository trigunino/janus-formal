import Mathlib

/-!
# Hilbert-boundary parent Schur selection

An infinite-dimensional bounded boundary space replaces the finite coordinate
family.  A scalar bulk mode couples through a continuous functional, while a
continuous symmetric bilinear form supplies the bare boundary Hessian.  The
stationary reduction is exact, preserves reciprocity, and has a unique parent
completion once the bulk fingerprint and reduced pairing are supplied.

This is a bounded Hilbert-space bridge toward a genuine bulk PDE and
Dirichlet-to-Neumann operator; it is not that PDE construction.
-/

namespace JanusFormal
namespace P0EFTJanusHilbertBoundaryParentSchurSelection

set_option autoImplicit false
noncomputable section

variable {Boundary : Type*}
  [NormedAddCommGroup Boundary]
  [InnerProductSpace ℝ Boundary]

structure HilbertBoundaryParentData (Boundary : Type*)
    [NormedAddCommGroup Boundary]
    [InnerProductSpace ℝ Boundary] where
  bulkCoefficient : ℝ
  bulkCoupling : Boundary →L[ℝ] ℝ
  boundaryPairing : Boundary →L[ℝ] Boundary →L[ℝ] ℝ
  boundaryPairing_symmetric :
    ∀ left right, boundaryPairing left right = boundaryPairing right left
  bulkCoefficientNonzero : bulkCoefficient ≠ 0

def parentAction
    (data : HilbertBoundaryParentData Boundary)
    (bulk : ℝ) (boundary : Boundary) : ℝ :=
  data.bulkCoefficient * bulk ^ 2 / 2 +
    bulk * data.bulkCoupling boundary +
    data.boundaryPairing boundary boundary / 2

def bulkEulerDerivative
    (data : HilbertBoundaryParentData Boundary)
    (bulk : ℝ) (boundary : Boundary) : ℝ :=
  data.bulkCoefficient * bulk + data.bulkCoupling boundary

def stationaryBulk
    (data : HilbertBoundaryParentData Boundary)
    (boundary : Boundary) : ℝ :=
  -data.bulkCoupling boundary / data.bulkCoefficient

theorem stationary_bulk_solves_euler
    (data : HilbertBoundaryParentData Boundary)
    (boundary : Boundary) :
    bulkEulerDerivative data (stationaryBulk data boundary) boundary = 0 := by
  unfold bulkEulerDerivative stationaryBulk
  field_simp [data.bulkCoefficientNonzero]
  ring

/-- Rank-one pairing induced by the bulk-to-boundary coupling. -/
def couplingRankOne
    (coupling : Boundary →L[ℝ] ℝ) :
    Boundary →L[ℝ] Boundary →L[ℝ] ℝ :=
  coupling.smulRight coupling

/-- Bounded Hilbert-space Schur complement. -/
def reducedBoundaryPairing
    (data : HilbertBoundaryParentData Boundary) :
    Boundary →L[ℝ] Boundary →L[ℝ] ℝ :=
  data.boundaryPairing -
    (data.bulkCoefficient⁻¹ : ℝ) • couplingRankOne data.bulkCoupling

theorem reduced_boundary_pairing_apply
    (data : HilbertBoundaryParentData Boundary)
    (left right : Boundary) :
    reducedBoundaryPairing data left right =
      data.boundaryPairing left right -
        data.bulkCoupling left * data.bulkCoupling right /
          data.bulkCoefficient := by
  simp [reducedBoundaryPairing, couplingRankOne,
    div_eq_mul_inv]
  ring

theorem reduced_boundary_pairing_symmetric
    (data : HilbertBoundaryParentData Boundary)
    (left right : Boundary) :
    reducedBoundaryPairing data left right =
      reducedBoundaryPairing data right left := by
  rw [reduced_boundary_pairing_apply,
    reduced_boundary_pairing_apply,
    data.boundaryPairing_symmetric left right]
  ring

def reducedAction
    (data : HilbertBoundaryParentData Boundary)
    (boundary : Boundary) : ℝ :=
  parentAction data (stationaryBulk data boundary) boundary

theorem reduced_action_formula
    (data : HilbertBoundaryParentData Boundary)
    (boundary : Boundary) :
    reducedAction data boundary =
      reducedBoundaryPairing data boundary boundary / 2 := by
  unfold reducedAction parentAction stationaryBulk
  rw [reduced_boundary_pairing_apply]
  field_simp [data.bulkCoefficientNonzero]
  ring

structure HilbertBulkFingerprint (Boundary : Type*)
    [NormedAddCommGroup Boundary]
    [InnerProductSpace ℝ Boundary] where
  bulkCoefficient : ℝ
  bulkCoupling : Boundary →L[ℝ] ℝ
  bulkCoefficientNonzero : bulkCoefficient ≠ 0

structure HilbertReducedTarget (Boundary : Type*)
    [NormedAddCommGroup Boundary]
    [InnerProductSpace ℝ Boundary] where
  pairing : Boundary →L[ℝ] Boundary →L[ℝ] ℝ
  pairing_symmetric :
    ∀ left right, pairing left right = pairing right left

def ParentHasHilbertBulkFingerprint
    (data : HilbertBoundaryParentData Boundary)
    (fingerprint : HilbertBulkFingerprint Boundary) : Prop :=
  data.bulkCoefficient = fingerprint.bulkCoefficient /\
    data.bulkCoupling = fingerprint.bulkCoupling

def hilbertParentCompletion
    (fingerprint : HilbertBulkFingerprint Boundary)
    (target : HilbertReducedTarget Boundary) :
    HilbertBoundaryParentData Boundary :=
  { bulkCoefficient := fingerprint.bulkCoefficient
    bulkCoupling := fingerprint.bulkCoupling
    boundaryPairing := target.pairing +
      (fingerprint.bulkCoefficient⁻¹ : ℝ) •
        couplingRankOne fingerprint.bulkCoupling
    boundaryPairing_symmetric := by
      intro left right
      simp [couplingRankOne]
      rw [target.pairing_symmetric left right]
      ring
    bulkCoefficientNonzero := fingerprint.bulkCoefficientNonzero }

theorem hilbert_parent_completion_has_fingerprint
    (fingerprint : HilbertBulkFingerprint Boundary)
    (target : HilbertReducedTarget Boundary) :
    ParentHasHilbertBulkFingerprint
      (hilbertParentCompletion fingerprint target) fingerprint := by
  simp [ParentHasHilbertBulkFingerprint, hilbertParentCompletion]

theorem hilbert_parent_completion_reduces_exactly
    (fingerprint : HilbertBulkFingerprint Boundary)
    (target : HilbertReducedTarget Boundary) :
    reducedBoundaryPairing
        (hilbertParentCompletion fingerprint target) = target.pairing := by
  ext left right
  simp [hilbertParentCompletion, reduced_boundary_pairing_apply,
    couplingRankOne, div_eq_mul_inv]
  ring

theorem same_hilbert_fingerprint_and_reduced_pairing_select_parent
    (first second : HilbertBoundaryParentData Boundary)
    (hBulk : first.bulkCoefficient = second.bulkCoefficient)
    (hCoupling : first.bulkCoupling = second.bulkCoupling)
    (hReduced : reducedBoundaryPairing first = reducedBoundaryPairing second) :
    first = second := by
  have hBoundary : first.boundaryPairing = second.boundaryPairing := by
    ext left right
    have hEntry := congrArg (fun pairing => pairing left right) hReduced
    rw [reduced_boundary_pairing_apply,
      reduced_boundary_pairing_apply] at hEntry
    rw [hBulk, hCoupling] at hEntry
    exact sub_left_injective hEntry
  cases first
  cases second
  simp_all

def ConditionalHilbertMicroscopicParentCompletion : Prop :=
  ∀ (Boundary : Type*)
      [NormedAddCommGroup Boundary]
      [InnerProductSpace ℝ Boundary]
      [CompleteSpace Boundary]
      (fingerprint : HilbertBulkFingerprint Boundary)
      (target : HilbertReducedTarget Boundary),
    ∃! data : HilbertBoundaryParentData Boundary,
      ParentHasHilbertBulkFingerprint data fingerprint /\
        reducedBoundaryPairing data = target.pairing

theorem conditional_hilbert_microscopic_parent_completion :
    ConditionalHilbertMicroscopicParentCompletion := by
  intro Boundary _ _ _ fingerprint target
  refine ⟨hilbertParentCompletion fingerprint target, ?_, ?_⟩
  · exact ⟨hilbert_parent_completion_has_fingerprint fingerprint target,
      hilbert_parent_completion_reduces_exactly fingerprint target⟩
  · intro data hData
    apply same_hilbert_fingerprint_and_reduced_pairing_select_parent
    · exact hData.1.1
    · exact hData.1.2
    · calc
        reducedBoundaryPairing data = target.pairing := hData.2
        _ = reducedBoundaryPairing
            (hilbertParentCompletion fingerprint target) :=
          (hilbert_parent_completion_reduces_exactly
            fingerprint target).symm

end
end P0EFTJanusHilbertBoundaryParentSchurSelection
end JanusFormal
