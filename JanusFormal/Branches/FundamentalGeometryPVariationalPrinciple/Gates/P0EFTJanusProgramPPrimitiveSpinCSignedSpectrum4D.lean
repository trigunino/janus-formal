import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatDiracSignScope4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D

/-!
# Signed abstract primitive SpinC spectrum

`Fold` records the external PT sheet.  As documented by the product-throat
sign-scope gate, it cannot also label the two first-order spectral branches
inside one fixed fold.  This module therefore adds an independent `±` label
to every nonzero sphere level while leaving the primitive zero-sphere tower
unchanged.

This is only an algebraic refinement of the existing abstract mode labels and
eigenvalues.  It does not assert a geometric eigensection realization,
exhaustion of an eigenspace, or spectral completeness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusPrimitiveMonopoleZ4Spectrum
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open P0EFTJanusProgramPPrimitiveSpinCSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCFullSpectralCompletion4D
open P0EFTJanusProgramPPrimitiveSpinCModeDecomposition4D

/-- The two first-order Dirac branches inside one fixed PT fold. -/
inductive PrimitiveSpinCDiracBranch where
  | positive
  | negative
  deriving DecidableEq, Repr, Fintype

/-- Real sign represented by a primitive first-order branch. -/
def primitiveSpinCDiracBranchSign : PrimitiveSpinCDiracBranch → Real
  | .positive => 1
  | .negative => -1

@[simp]
theorem primitiveSpinCDiracBranchSign_positive :
    primitiveSpinCDiracBranchSign .positive = 1 := rfl

@[simp]
theorem primitiveSpinCDiracBranchSign_negative :
    primitiveSpinCDiracBranchSign .negative = -1 := rfl

@[simp]
theorem primitiveSpinCDiracBranchSign_sq
    (branch : PrimitiveSpinCDiracBranch) :
    primitiveSpinCDiracBranchSign branch ^ 2 = 1 := by
  cases branch <;> norm_num

/-- Exchange the two internal Dirac branches. -/
def primitiveSpinCOppositeDiracBranch :
    PrimitiveSpinCDiracBranch → PrimitiveSpinCDiracBranch
  | .positive => .negative
  | .negative => .positive

@[simp]
theorem primitiveSpinCOppositeDiracBranch_involutive
    (branch : PrimitiveSpinCDiracBranch) :
    primitiveSpinCOppositeDiracBranch
        (primitiveSpinCOppositeDiracBranch branch) =
      branch := by
  cases branch <;> rfl

@[simp]
theorem primitiveSpinCOppositeDiracBranch_ne
    (branch : PrimitiveSpinCDiracBranch) :
    primitiveSpinCOppositeDiracBranch branch ≠ branch := by
  cases branch <;> decide

@[simp]
theorem primitiveSpinCDiracBranchSign_opposite
    (branch : PrimitiveSpinCDiracBranch) :
    primitiveSpinCDiracBranchSign
        (primitiveSpinCOppositeDiracBranch branch) =
      -primitiveSpinCDiracBranchSign branch := by
  cases branch <;>
    norm_num [primitiveSpinCOppositeDiracBranch]

/-- Nonnegative frequency already determined by the existing squared
primitive spectrum. -/
def primitiveSpinCFullDiracFrequency
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) : Real :=
  Real.sqrt
    (primitiveSpinCFullDiracSquaredEigenvalue fold twist mode)

theorem primitiveSpinCFullDiracFrequency_nonnegative
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    0 ≤ primitiveSpinCFullDiracFrequency fold twist mode :=
  Real.sqrt_nonneg _

theorem primitiveSpinCFullDiracFrequency_sq
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    primitiveSpinCFullDiracFrequency fold twist mode ^ 2 =
      primitiveSpinCFullDiracSquaredEigenvalue fold twist mode := by
  exact Real.sq_sqrt
    (primitiveSpinCFullDiracSquaredEigenvalue_nonnegative
      fold twist mode)

/-- Existing fold sign together with an independent internal `±` branch. -/
def primitiveSpinCBranchedDiracEigenvalue
    (branch : PrimitiveSpinCDiracBranch)
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) : Real :=
  primitiveSpinCDiracBranchSign branch *
    primitiveSpinCFullDiracEigenvalue fold twist mode

@[simp]
theorem primitiveSpinCBranchedDiracEigenvalue_positive
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    primitiveSpinCBranchedDiracEigenvalue .positive fold twist mode =
      primitiveSpinCFullDiracEigenvalue fold twist mode := by
  simp [primitiveSpinCBranchedDiracEigenvalue]

@[simp]
theorem primitiveSpinCBranchedDiracEigenvalue_negative
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    primitiveSpinCBranchedDiracEigenvalue .negative fold twist mode =
      -primitiveSpinCFullDiracEigenvalue fold twist mode := by
  simp [primitiveSpinCBranchedDiracEigenvalue]

theorem primitiveSpinCBranchedDiracEigenvalue_sq
    (branch : PrimitiveSpinCDiracBranch)
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    primitiveSpinCBranchedDiracEigenvalue branch fold twist mode ^ 2 =
      primitiveSpinCFullDiracSquaredEigenvalue fold twist mode := by
  rw [primitiveSpinCBranchedDiracEigenvalue, mul_pow,
    primitiveSpinCDiracBranchSign_sq, one_mul,
    primitiveSpinCFullDiracEigenvalue_sq]

theorem primitiveSpinCBranchedDiracEigenvalue_opposite
    (branch : PrimitiveSpinCDiracBranch)
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode) :
    primitiveSpinCBranchedDiracEigenvalue
        (primitiveSpinCOppositeDiracBranch branch) fold twist mode =
      -primitiveSpinCBranchedDiracEigenvalue branch fold twist mode := by
  simp [primitiveSpinCBranchedDiracEigenvalue]

theorem primitiveSpinCBranchedDiracEigenvalue_positive_ne_negative
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode)
    (hFrequency :
      0 < primitiveSpinCFullDiracFrequency fold twist mode) :
    primitiveSpinCBranchedDiracEigenvalue .positive fold twist mode ≠
      primitiveSpinCBranchedDiracEigenvalue .negative fold twist mode := by
  have hFoldSign : fold.spectralSign ≠ 0 := by
    cases fold <;> norm_num [Fold.spectralSign]
  have hOldEigenvalue :
      primitiveSpinCFullDiracEigenvalue fold twist mode ≠ 0 := by
    unfold primitiveSpinCFullDiracEigenvalue
    exact mul_ne_zero hFoldSign (ne_of_gt hFrequency)
  simp only [primitiveSpinCBranchedDiracEigenvalue_positive,
    primitiveSpinCBranchedDiracEigenvalue_negative]
  intro hEqual
  apply hOldEigenvalue
  linarith

theorem primitiveSpinCBranchedDiracEigenvalue_ne_opposite
    (branch : PrimitiveSpinCDiracBranch)
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCFullMode)
    (hFrequency :
      0 < primitiveSpinCFullDiracFrequency fold twist mode) :
    primitiveSpinCBranchedDiracEigenvalue branch fold twist mode ≠
      primitiveSpinCBranchedDiracEigenvalue
        (primitiveSpinCOppositeDiracBranch branch) fold twist mode := by
  cases branch with
  | positive =>
      exact primitiveSpinCBranchedDiracEigenvalue_positive_ne_negative
        fold twist mode hFrequency
  | negative =>
      exact (primitiveSpinCBranchedDiracEigenvalue_positive_ne_negative
        fold twist mode hFrequency).symm

/-- Existing multiplicity fiber, now explicitly attached to one branch.
The branch is a label only and does not duplicate multiplicity within that
branch. -/
abbrev PrimitiveSpinCSignedNonzeroMultiplicity
    (_branch : PrimitiveSpinCDiracBranch) (level : Nat) : Type :=
  Fin (primitiveSphereModeDegeneracy (level + 1))

/-- Exact identification with the pre-existing positive-level multiplicity
fiber for each branch separately. -/
def primitiveSpinCSignedNonzeroMultiplicityEquiv
    (period : Real) (hPeriod : period ≠ 0)
    (branch : PrimitiveSpinCDiracBranch) (level : Nat) :
    PrimitiveSpinCSignedNonzeroMultiplicity branch level ≃
      Fin (sphereMultiplicity
        (PrimitiveSpinCSpectralData period hPeriod) level) :=
  primitiveSpinCPositiveMultiplicityEquiv period hPeriod level

@[simp]
theorem primitiveSpinCSignedNonzeroMultiplicity_card
    (branch : PrimitiveSpinCDiracBranch) (level : Nat) :
    Fintype.card
        (PrimitiveSpinCSignedNonzeroMultiplicity branch level) =
      primitiveSphereModeDegeneracy (level + 1) := by
  simp [PrimitiveSpinCSignedNonzeroMultiplicity]

theorem primitiveSpinCSignedNonzeroMultiplicity_card_agrees
    (period : Real) (hPeriod : period ≠ 0)
    (branch : PrimitiveSpinCDiracBranch) (level : Nat) :
    Fintype.card
        (PrimitiveSpinCSignedNonzeroMultiplicity branch level) =
      sphereMultiplicity
        (PrimitiveSpinCSpectralData period hPeriod) level := by
  rw [primitiveSpinCSignedNonzeroMultiplicity_card,
    primitiveSpinCFull_positiveSphereMultiplicity_agrees
      period hPeriod level]

/-- A nonzero sphere level carrying its independent branch and the unchanged
multiplicity and circle labels. -/
structure PrimitiveSpinCSignedNonzeroMode where
  branch : PrimitiveSpinCDiracBranch
  level : Nat
  multiplicity :
    PrimitiveSpinCSignedNonzeroMultiplicity branch level
  circleMode : Int

/-- Forget only the new branch label and recover the old full primitive mode. -/
def primitiveSpinCSignedNonzeroModeToFullMode
    (mode : PrimitiveSpinCSignedNonzeroMode) :
    PrimitiveSpinCFullMode :=
  (⟨mode.level + 1, mode.multiplicity⟩, mode.circleMode)

/-- The zero-sphere tower is deliberately not doubled by a branch label. -/
abbrev PrimitiveSpinCUnsignedZeroMode :=
  Fin (primitiveSphereModeDegeneracy 0) × Int

/-- Full corrected label set: unchanged zero tower plus signed nonzero
sphere levels. -/
abbrev PrimitiveSpinCSignedMode :=
  PrimitiveSpinCUnsignedZeroMode ⊕ PrimitiveSpinCSignedNonzeroMode

/-- Forget the internal branch in the corrected full mode label. -/
def primitiveSpinCSignedModeToFullMode :
    PrimitiveSpinCSignedMode → PrimitiveSpinCFullMode
  | .inl mode => (⟨0, mode.1⟩, mode.2)
  | .inr mode => primitiveSpinCSignedNonzeroModeToFullMode mode

/-- Signed first-order value on the corrected label set.  The zero tower
keeps the old fold convention; only nonzero sphere levels receive `±`. -/
def primitiveSpinCSignedDiracEigenvalue
    (fold : Fold) (twist : CircleTwist) :
    PrimitiveSpinCSignedMode → Real
  | .inl mode =>
      primitiveSpinCFullDiracEigenvalue fold twist
        (primitiveSpinCSignedModeToFullMode (.inl mode))
  | .inr mode =>
      primitiveSpinCBranchedDiracEigenvalue mode.branch fold twist
        (primitiveSpinCSignedNonzeroModeToFullMode mode)

/-- The corrected signed value has exactly the old squared eigenvalue after
forgetting only the new branch label. -/
theorem primitiveSpinCSignedDiracEigenvalue_sq
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCSignedMode) :
    primitiveSpinCSignedDiracEigenvalue fold twist mode ^ 2 =
      primitiveSpinCFullDiracSquaredEigenvalue fold twist
        (primitiveSpinCSignedModeToFullMode mode) := by
  cases mode with
  | inl mode =>
      exact primitiveSpinCFullDiracEigenvalue_sq fold twist
        (primitiveSpinCSignedModeToFullMode (.inl mode))
  | inr mode =>
      exact primitiveSpinCBranchedDiracEigenvalue_sq mode.branch
        fold twist (primitiveSpinCSignedNonzeroModeToFullMode mode)

theorem primitiveSpinCSignedNonzero_squaredEigenvalue_pos
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCSignedNonzeroMode) :
    0 <
      primitiveSpinCFullDiracSquaredEigenvalue fold twist
        (primitiveSpinCSignedNonzeroModeToFullMode mode) := by
  rcases mode with ⟨branch, level, multiplicity, circleMode⟩
  unfold primitiveSpinCSignedNonzeroModeToFullMode
    primitiveSpinCFullDiracSquaredEigenvalue
  exact add_pos_of_pos_of_nonneg
    (by
      unfold primitiveSpinCFullSphereEigenvalueSquared
      positivity)
    (by
      rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
      exact eigenvalueSq_nonnegative fold twist circleMode)

theorem primitiveSpinCSignedNonzero_frequency_pos
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCSignedNonzeroMode) :
    0 <
      primitiveSpinCFullDiracFrequency fold twist
        (primitiveSpinCSignedNonzeroModeToFullMode mode) := by
  exact Real.sqrt_pos.2
    (primitiveSpinCSignedNonzero_squaredEigenvalue_pos fold twist mode)

theorem primitiveSpinCSignedNonzero_branches_distinct
    (fold : Fold) (twist : CircleTwist)
    (mode : PrimitiveSpinCSignedNonzeroMode) :
    primitiveSpinCBranchedDiracEigenvalue mode.branch fold twist
        (primitiveSpinCSignedNonzeroModeToFullMode mode) ≠
      primitiveSpinCBranchedDiracEigenvalue
        (primitiveSpinCOppositeDiracBranch mode.branch) fold twist
        (primitiveSpinCSignedNonzeroModeToFullMode mode) := by
  exact primitiveSpinCBranchedDiracEigenvalue_ne_opposite
    mode.branch fold twist
    (primitiveSpinCSignedNonzeroModeToFullMode mode)
    (primitiveSpinCSignedNonzero_frequency_pos fold twist mode)

end
end P0EFTJanusProgramPPrimitiveSpinCSignedSpectrum4D
end JanusFormal
