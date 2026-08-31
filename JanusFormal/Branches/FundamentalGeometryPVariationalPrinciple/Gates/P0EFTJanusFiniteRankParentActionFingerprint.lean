import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteRankParentSchurHelmholtz

/-!
# Microscopic fingerprint extracted from a finite-rank parent action

Exact finite differences of the unreduced quadratic action recover its bulk
coefficient and every bulk-to-boundary coupling.  Thus these microscopic data
are observables of a supplied parent action, not additional choices once that
action has been derived.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteRankParentActionFingerprint

set_option autoImplicit false

open P0EFTJanusFiniteRankParentSchurHelmholtz

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def zeroBoundary : ι → ℝ := fun _ => 0

def unitBoundary (i : ι) : ι → ℝ :=
  fun j => if j = i then 1 else 0

omit [DecidableEq ι] in
@[simp]
theorem couplingPairing_zeroBoundary
    (data : FiniteRankParentData ι) :
    couplingPairing data zeroBoundary = 0 := by
  simp [couplingPairing, zeroBoundary]

@[simp]
theorem couplingPairing_unitBoundary
    (data : FiniteRankParentData ι) (i : ι) :
    couplingPairing data (unitBoundary i) = data.coupling i := by
  simp [couplingPairing, unitBoundary]

/-- Centered action evaluation recovering the quadratic bulk coefficient. -/
noncomputable def bulkCoefficientObservable
    (data : FiniteRankParentData ι) : ℝ :=
  parentAction data 1 zeroBoundary +
    parentAction data (-1) zeroBoundary -
    2 * parentAction data 0 zeroBoundary

omit [DecidableEq ι] in
theorem bulk_coefficient_observable_exact
    (data : FiniteRankParentData ι) :
    bulkCoefficientObservable data = data.bulkCoefficient := by
  simp [bulkCoefficientObservable, parentAction,
    boundaryQuadratic, zeroBoundary]

/-- Mixed bulk/boundary polarization recovering one microscopic coupling. -/
noncomputable def bulkBoundaryCouplingObservable
    (data : FiniteRankParentData ι) (i : ι) : ℝ :=
  parentAction data 1 (unitBoundary i) -
    parentAction data 1 zeroBoundary -
    parentAction data 0 (unitBoundary i) +
    parentAction data 0 zeroBoundary

theorem bulk_boundary_coupling_observable_exact
    (data : FiniteRankParentData ι) (i : ι) :
    bulkBoundaryCouplingObservable data i = data.coupling i := by
  simp [bulkBoundaryCouplingObservable, parentAction,
    couplingPairing_unitBoundary, boundaryQuadratic, zeroBoundary]
  ring

/-- Pointwise equality of unreduced parent actions fixes the complete bulk
microscopic fingerprint: the bulk coefficient and every boundary coupling. -/
theorem equal_parent_actions_fix_bulk_fingerprint
    (first second : FiniteRankParentData ι)
    (hAction : ∀ bulk boundary,
      parentAction first bulk boundary =
        parentAction second bulk boundary) :
    first.bulkCoefficient = second.bulkCoefficient /\
      ∀ i, first.coupling i = second.coupling i := by
  constructor
  · calc
      first.bulkCoefficient = bulkCoefficientObservable first :=
        (bulk_coefficient_observable_exact first).symm
      _ = bulkCoefficientObservable second := by
        unfold bulkCoefficientObservable
        rw [hAction, hAction, hAction]
      _ = second.bulkCoefficient :=
        bulk_coefficient_observable_exact second
  · intro i
    calc
      first.coupling i = bulkBoundaryCouplingObservable first i :=
        (bulk_boundary_coupling_observable_exact first i).symm
      _ = bulkBoundaryCouplingObservable second i := by
        unfold bulkBoundaryCouplingObservable
        rw [hAction, hAction, hAction, hAction]
      _ = second.coupling i :=
        bulk_boundary_coupling_observable_exact second i

def FiniteRankParentActionFixesBulkFingerprint : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]
      (first second : FiniteRankParentData ι),
    (∀ bulk boundary,
      parentAction first bulk boundary =
        parentAction second bulk boundary) →
    first.bulkCoefficient = second.bulkCoefficient /\
      ∀ i, first.coupling i = second.coupling i

theorem finite_rank_parent_action_fixes_bulk_fingerprint :
    FiniteRankParentActionFixesBulkFingerprint := by
  intro ι _ _ _ first second hAction
  exact equal_parent_actions_fix_bulk_fingerprint first second hAction

/-- Microscopic information not contained in the reduced finite-rank
boundary Hessian. -/
structure FiniteRankMicroscopicBulkFingerprint
    (ι : Type*) [Fintype ι] [Nonempty ι] where
  bulkCoefficient : ℝ
  coupling : ι → ℝ
  bulkCoefficientNonzero : bulkCoefficient ≠ 0

/-- A reciprocal reduced boundary Hessian to be reproduced by the parent. -/
structure FiniteRankReducedTarget
    (ι : Type*) [Fintype ι] [Nonempty ι] where
  kernel : ι → ι → ℝ
  kernel_symmetric : ∀ i j, kernel i j = kernel j i

def FiniteRankParentHasBulkFingerprint
    (data : FiniteRankParentData ι)
    (fingerprint : FiniteRankMicroscopicBulkFingerprint ι) : Prop :=
  data.bulkCoefficient = fingerprint.bulkCoefficient /\
    ∀ i, data.coupling i = fingerprint.coupling i

/-- Unique bare boundary Hessian completing the prescribed microscopic bulk
fingerprint to the prescribed reduced Hessian. -/
noncomputable def finiteRankParentCompletion
    (fingerprint : FiniteRankMicroscopicBulkFingerprint ι)
    (target : FiniteRankReducedTarget ι) : FiniteRankParentData ι :=
  { bulkCoefficient := fingerprint.bulkCoefficient
    coupling := fingerprint.coupling
    boundaryHessian := fun i j =>
      target.kernel i j +
        fingerprint.coupling i * fingerprint.coupling j /
          fingerprint.bulkCoefficient
    boundaryHessian_symmetric := by
      intro i j
      rw [target.kernel_symmetric i j]
      ring
    bulkCoefficientNonzero := fingerprint.bulkCoefficientNonzero }

omit [DecidableEq ι] in
theorem finite_rank_parent_completion_has_fingerprint
    (fingerprint : FiniteRankMicroscopicBulkFingerprint ι)
    (target : FiniteRankReducedTarget ι) :
    FiniteRankParentHasBulkFingerprint
      (finiteRankParentCompletion fingerprint target) fingerprint := by
  simp [FiniteRankParentHasBulkFingerprint, finiteRankParentCompletion]

omit [DecidableEq ι] in
theorem finite_rank_parent_completion_reduces_exactly
    (fingerprint : FiniteRankMicroscopicBulkFingerprint ι)
    (target : FiniteRankReducedTarget ι)
    (i j : ι) :
    reducedBoundaryHessian
        (finiteRankParentCompletion fingerprint target) i j =
      target.kernel i j := by
  unfold reducedBoundaryHessian finiteRankParentCompletion
  ring

omit [DecidableEq ι] in
/-- At arbitrary finite rank, fixed bulk microscopic data and a fixed reduced
Hessian select the complete parent uniquely. -/
theorem finite_rank_same_fingerprint_and_reduced_hessian_select_parent
    (first second : FiniteRankParentData ι)
    (hFingerprint :
      first.bulkCoefficient = second.bulkCoefficient /\
        ∀ i, first.coupling i = second.coupling i)
    (hReduced : ∀ i j,
      reducedBoundaryHessian first i j =
        reducedBoundaryHessian second i j) :
    first = second := by
  rcases hFingerprint with ⟨hBulk, hCoupling⟩
  have hBoundary :
      first.boundaryHessian = second.boundaryHessian := by
    funext i j
    have hEntry := hReduced i j
    unfold reducedBoundaryHessian at hEntry
    rw [hBulk, hCoupling i, hCoupling j] at hEntry
    exact sub_left_injective hEntry
  have hCouplingFunction : first.coupling = second.coupling :=
    funext hCoupling
  cases first
  cases second
  simp_all

def ConditionalFiniteRankMicroscopicParentCompletion : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι]
      (fingerprint : FiniteRankMicroscopicBulkFingerprint ι)
      (target : FiniteRankReducedTarget ι),
    ∃! data : FiniteRankParentData ι,
      FiniteRankParentHasBulkFingerprint data fingerprint /\
        ∀ i j, reducedBoundaryHessian data i j = target.kernel i j

theorem conditional_finite_rank_microscopic_parent_completion :
    ConditionalFiniteRankMicroscopicParentCompletion := by
  intro ι _ _ fingerprint target
  refine ⟨finiteRankParentCompletion fingerprint target, ?_, ?_⟩
  · exact ⟨finite_rank_parent_completion_has_fingerprint fingerprint target,
      finite_rank_parent_completion_reduces_exactly fingerprint target⟩
  · intro data hData
    apply finite_rank_same_fingerprint_and_reduced_hessian_select_parent
    · rcases hData.1 with ⟨hBulk, hCoupling⟩
      exact ⟨hBulk, fun i => by
        simpa [finiteRankParentCompletion] using hCoupling i⟩
    · intro i j
      calc
        reducedBoundaryHessian data i j = target.kernel i j :=
          hData.2 i j
        _ = reducedBoundaryHessian
            (finiteRankParentCompletion fingerprint target) i j :=
          (finite_rank_parent_completion_reduces_exactly
            fingerprint target i j).symm

end P0EFTJanusFiniteRankParentActionFingerprint
end JanusFormal
