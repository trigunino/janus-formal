import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkHelmholtzReciprocity

/-!
# Conditional parent selection from a microscopic bulk fingerprint

The quadratic Schur parent is not selected by Helmholtz or PT invariance alone.
This gate isolates the additional microscopic information that removes its
remaining ambiguity: the bulk quadratic coefficient and its two boundary
couplings.  Once these three quantities and the reduced potential agree, all
bare boundary and junction coefficients are forced.

This is a conditional injectivity theorem, not a derivation of the Janus
microscopic fingerprint and therefore not terminal `T08`.
-/

namespace JanusFormal
namespace P0EFTJanusParentBulkMicroscopicFingerprintSelection

set_option autoImplicit false

open P0EFTJanusCoupledSectorHelmholtzSelection
open P0EFTJanusParentBulkHelmholtzReciprocity

/-- Three bulk coefficients that cannot be reconstructed from the reduced
boundary potential alone. -/
structure MicroscopicBulkFingerprint where
  bulkCoefficient : ℝ
  bulkToNormal : ℝ
  bulkToTrace : ℝ
  bulkCoefficientNonzero : bulkCoefficient ≠ 0

/-- The three PT-even coefficients visible in the quadratic reduced model. -/
structure ReducedTwoSectorTarget where
  normalCoefficient : ℝ
  mixingCoefficient : ℝ
  traceCoefficient : ℝ

def reducedTwoSectorTargetPotential
    (target : ReducedTwoSectorTarget) : QuadraticPotential3 :=
  { nn := target.normalCoefficient
    tt := target.traceCoefficient
    oo := 0
    nt := target.mixingCoefficient
    no := 0
    trOdd := 0 }

def ParentHasMicroscopicBulkFingerprint
    (parent : ParentBulkTwoSectorData)
    (fingerprint : MicroscopicBulkFingerprint) : Prop :=
  parent.bulkCoefficient = fingerprint.bulkCoefficient /\
  parent.bulkToNormal = fingerprint.bulkToNormal /\
  parent.bulkToTrace = fingerprint.bulkToTrace

/-- The unique bare boundary completion suggested by the Schur formula. -/
noncomputable def parentCompletion
    (fingerprint : MicroscopicBulkFingerprint)
    (target : ReducedTwoSectorTarget) : ParentBulkTwoSectorData :=
  { bulkCoefficient := fingerprint.bulkCoefficient
    bulkToNormal := fingerprint.bulkToNormal
    bulkToTrace := fingerprint.bulkToTrace
    boundaryNormal :=
      target.normalCoefficient +
        fingerprint.bulkToNormal ^ 2 / fingerprint.bulkCoefficient
    boundaryMixing :=
      target.mixingCoefficient +
        fingerprint.bulkToNormal * fingerprint.bulkToTrace /
          fingerprint.bulkCoefficient
    boundaryTrace :=
      target.traceCoefficient +
        fingerprint.bulkToTrace ^ 2 / fingerprint.bulkCoefficient
    bulkCoefficientNonzero := fingerprint.bulkCoefficientNonzero }

theorem parent_completion_has_fingerprint
    (fingerprint : MicroscopicBulkFingerprint)
    (target : ReducedTwoSectorTarget) :
    ParentHasMicroscopicBulkFingerprint
      (parentCompletion fingerprint target) fingerprint := by
  simp [ParentHasMicroscopicBulkFingerprint, parentCompletion]

theorem parent_completion_reduces_exactly
    (fingerprint : MicroscopicBulkFingerprint)
    (target : ReducedTwoSectorTarget) :
    reducedPotential (parentCompletion fingerprint target) =
      reducedTwoSectorTargetPotential target := by
  ext <;>
    simp [parentCompletion, reducedPotential,
      reducedNormalCoefficient, reducedMixingCoefficient,
      reducedTraceCoefficient, reducedTwoSectorTargetPotential]

/-- The part of the parent action that must be supplied by bulk microscopic
dynamics rather than inferred from its reduced boundary action. -/
def SameMicroscopicBulkFingerprint
    (first second : ParentBulkTwoSectorData) : Prop :=
  first.bulkCoefficient = second.bulkCoefficient /\
  first.bulkToNormal = second.bulkToNormal /\
  first.bulkToTrace = second.bulkToTrace

/-- Matching a specified reduced potential fixes the three bare boundary
coefficients explicitly once the microscopic bulk fingerprint is known. -/
theorem reduced_potential_matching_forces_boundary_coefficients
    (parent : ParentBulkTwoSectorData)
    (target : QuadraticPotential3)
    (hReduced : reducedPotential parent = target) :
    parent.boundaryNormal =
        target.nn + parent.bulkToNormal ^ 2 / parent.bulkCoefficient /\
    parent.boundaryMixing =
        target.nt +
          parent.bulkToNormal * parent.bulkToTrace /
            parent.bulkCoefficient /\
    parent.boundaryTrace =
        target.tt + parent.bulkToTrace ^ 2 / parent.bulkCoefficient := by
  have hNN := congrArg QuadraticPotential3.nn hReduced
  have hNT := congrArg QuadraticPotential3.nt hReduced
  have hTT := congrArg QuadraticPotential3.tt hReduced
  simp only [reducedPotential, reducedNormalCoefficient] at hNN
  simp only [reducedPotential, reducedMixingCoefficient] at hNT
  simp only [reducedPotential, reducedTraceCoefficient] at hTT
  constructor
  · linarith
  constructor <;> linarith

/-- Fixed microscopic bulk data and a fixed reduced potential determine every
bare quadratic boundary and junction coefficient, hence the whole parent. -/
theorem same_fingerprint_and_reduced_potential_select_parent
    (first second : ParentBulkTwoSectorData)
    (hFingerprint : SameMicroscopicBulkFingerprint first second)
    (hReduced : reducedPotential first = reducedPotential second) :
    first = second := by
  rcases hFingerprint with ⟨hBulk, hNormal, hTrace⟩
  have hNN := congrArg QuadraticPotential3.nn hReduced
  have hNT := congrArg QuadraticPotential3.nt hReduced
  have hTT := congrArg QuadraticPotential3.tt hReduced
  simp only [reducedPotential, reducedNormalCoefficient] at hNN
  simp only [reducedPotential, reducedMixingCoefficient] at hNT
  simp only [reducedPotential, reducedTraceCoefficient] at hTT
  have hBoundaryNormal :
      first.boundaryNormal = second.boundaryNormal := by
    rw [hBulk, hNormal] at hNN
    exact sub_left_injective hNN
  have hBoundaryMixing :
      first.boundaryMixing = second.boundaryMixing := by
    rw [hBulk, hNormal, hTrace] at hNT
    exact sub_left_injective hNT
  have hBoundaryTrace :
      first.boundaryTrace = second.boundaryTrace := by
    rw [hBulk, hTrace] at hTT
    exact sub_left_injective hTT
  cases first
  cases second
  simp_all

/-- The exact conditional selection statement exposed to the global
microscopic frontier. -/
def ConditionalMicroscopicFingerprintSelection4D : Prop :=
  ∀ first second : ParentBulkTwoSectorData,
    SameMicroscopicBulkFingerprint first second →
    reducedPotential first = reducedPotential second →
    first = second

theorem conditional_microscopic_fingerprint_selection :
    ConditionalMicroscopicFingerprintSelection4D :=
  same_fingerprint_and_reduced_potential_select_parent

/-- For every supplied microscopic fingerprint and reduced target there is
exactly one quadratic parent realizing both. -/
def ConditionalMicroscopicParentCompletion4D : Prop :=
  ∀ (fingerprint : MicroscopicBulkFingerprint)
      (target : ReducedTwoSectorTarget),
    ∃! parent : ParentBulkTwoSectorData,
      ParentHasMicroscopicBulkFingerprint parent fingerprint /\
      reducedPotential parent = reducedTwoSectorTargetPotential target

theorem conditional_microscopic_parent_completion :
    ConditionalMicroscopicParentCompletion4D := by
  intro fingerprint target
  refine ⟨parentCompletion fingerprint target, ?_, ?_⟩
  · exact ⟨parent_completion_has_fingerprint fingerprint target,
      parent_completion_reduces_exactly fingerprint target⟩
  · intro parent hParent
    apply same_fingerprint_and_reduced_potential_select_parent
    · unfold SameMicroscopicBulkFingerprint
      rcases hParent.1 with ⟨hBulk, hNormal, hTrace⟩
      simp only [parentCompletion]
      exact ⟨hBulk, hNormal, hTrace⟩
    · calc
        reducedPotential parent =
            reducedTwoSectorTargetPotential target := hParent.2
        _ = reducedPotential (parentCompletion fingerprint target) :=
          (parent_completion_reduces_exactly fingerprint target).symm

def referenceFingerprint : MicroscopicBulkFingerprint :=
  { bulkCoefficient := 1
    bulkToNormal := 0
    bulkToTrace := 0
    bulkCoefficientNonzero := by norm_num }

def shiftedFingerprint : MicroscopicBulkFingerprint :=
  { bulkCoefficient := 1
    bulkToNormal := 1
    bulkToTrace := 0
    bulkCoefficientNonzero := by norm_num }

/-- Even an exactly known reduced target does not reconstruct its microscopic
bulk fingerprint: distinct fingerprints have distinct parent completions with
the same reduced potential. -/
theorem reduced_target_alone_does_not_identify_fingerprint
    (target : ReducedTwoSectorTarget) :
    parentCompletion referenceFingerprint target ≠
        parentCompletion shiftedFingerprint target /\
    reducedPotential (parentCompletion referenceFingerprint target) =
        reducedPotential (parentCompletion shiftedFingerprint target) := by
  constructor
  · intro hParents
    have hNormal :=
      congrArg ParentBulkTwoSectorData.bulkToNormal hParents
    norm_num [parentCompletion, referenceFingerprint, shiftedFingerprint]
      at hNormal
  · rw [parent_completion_reduces_exactly,
      parent_completion_reduces_exactly]

end P0EFTJanusParentBulkMicroscopicFingerprintSelection
end JanusFormal
