import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06TruncatedIndexSuccessorEquiv4D

/-!
# Signed telescoping for truncated spatial indices

This gate isolates the finite combinatorics behind the order-three to
order-four Euler cancellation.  Lower-order indices retain their sign, while
successor indices acquire the opposite sign.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SignedTruncatedIndexTelescoping4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06TruncatedShiftCoordinateInjection4D
open P0EFTJanusProgramPT06TruncatedIndexSuccessorEquiv4D

universe u

variable {A : Type u} [AddCommGroup A] [Module Real A]

/-- Retyping the lower-order part of the order-four sum gives the signed
order-three sum. -/
theorem programPT06SignedLowerOrderSum_eq
    (term : ThroatSpatialTruncatedIndex 3 → A) :
    (∑ index : ThroatSpatialTruncatedIndex 4,
      if hLower : throatSpatialMultiIndexOrder index.1 ≤ 3 then
        ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
          term ⟨index.1, hLower⟩
      else 0) =
      ∑ index : ThroatSpatialTruncatedIndex 3,
        ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) • term index := by
  classical
  let lowerSummand :
      { index : ThroatSpatialTruncatedIndex 4 //
        throatSpatialMultiIndexOrder index.1 ≤ 3 } → A :=
    fun index =>
      ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1.1) •
        term ⟨index.1.1, index.2⟩
  have hSubtype :
      (∑ index : ThroatSpatialTruncatedIndex 4,
        if hLower : throatSpatialMultiIndexOrder index.1 ≤ 3 then
          ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
            term ⟨index.1, hLower⟩
        else 0) =
        ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
          throatSpatialMultiIndexOrder index.1 ≤ 3 },
          lowerSummand index := by
    let lowerExtended : ThroatSpatialTruncatedIndex 4 → A :=
      fun index =>
        if hLower : throatSpatialMultiIndexOrder index.1 ≤ 3 then
          ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
            term ⟨index.1, hLower⟩
        else 0
    have hSplit := Fintype.sum_subtype_add_sum_subtype
      (fun index : ThroatSpatialTruncatedIndex 4 =>
        throatSpatialMultiIndexOrder index.1 ≤ 3)
      lowerExtended
    have hComplement :
        (∑ index : { index : ThroatSpatialTruncatedIndex 4 //
          ¬ throatSpatialMultiIndexOrder index.1 ≤ 3 },
          lowerExtended index) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      simp [lowerExtended, index.2]
    calc
      _ = ∑ index : ThroatSpatialTruncatedIndex 4,
          lowerExtended index := rfl
      _ = ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
            throatSpatialMultiIndexOrder index.1 ≤ 3 },
            lowerExtended index := by
        rw [← hSplit, hComplement, add_zero]
      _ = ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
            throatSpatialMultiIndexOrder index.1 ≤ 3 },
            lowerSummand index := by
        apply Finset.sum_congr rfl
        intro index _
        simp [lowerExtended, lowerSummand, index.2]
  calc
    _ = ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
          throatSpatialMultiIndexOrder index.1 ≤ 3 },
          lowerSummand index := hSubtype
    _ = ∑ index : ThroatSpatialTruncatedIndex 3,
          lowerSummand
            (programPT06TruncatedIndexLowerOrderEquiv 3 index) :=
      (programPT06TruncatedIndexLowerOrderEquiv_sum_comp
        (M := A) 3 lowerSummand).symm
    _ = ∑ index : ThroatSpatialTruncatedIndex 3,
          ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) • term index := by
      simp [lowerSummand, programPT06TruncatedIndexLowerOrderEmbedding]

/-- Reindexing the positive-coordinate part by predecessors reverses every
sign because successor increases total order by one. -/
theorem programPT06SignedSuccessorSum_eq_neg
    (direction : Fin 3)
    (term : ThroatSpatialTruncatedIndex 3 → A) :
    (∑ index : ThroatSpatialTruncatedIndex 4,
      if hPositive : index.1 direction ≠ 0 then
        ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
          term (programPT06TruncatedIndexSuccessorPredecessor
            3 direction ⟨index, hPositive⟩)
      else 0) =
      -∑ index : ThroatSpatialTruncatedIndex 3,
        ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) • term index := by
  classical
  let positiveSummand :
      { index : ThroatSpatialTruncatedIndex 4 //
        index.1 direction ≠ 0 } → A :=
    fun index =>
      ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1.1) •
        term (programPT06TruncatedIndexSuccessorPredecessor
          3 direction index)
  have hSubtype :
      (∑ index : ThroatSpatialTruncatedIndex 4,
        if hPositive : index.1 direction ≠ 0 then
          ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
            term (programPT06TruncatedIndexSuccessorPredecessor
              3 direction ⟨index, hPositive⟩)
        else 0) =
        ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
          index.1 direction ≠ 0 }, positiveSummand index := by
    let positiveExtended : ThroatSpatialTruncatedIndex 4 → A :=
      fun index =>
        if hPositive : index.1 direction ≠ 0 then
          ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
            term (programPT06TruncatedIndexSuccessorPredecessor
              3 direction ⟨index, hPositive⟩)
        else 0
    have hSplit := Fintype.sum_subtype_add_sum_subtype
      (fun index : ThroatSpatialTruncatedIndex 4 =>
        index.1 direction ≠ 0)
      positiveExtended
    have hComplement :
        (∑ index : { index : ThroatSpatialTruncatedIndex 4 //
          ¬ index.1 direction ≠ 0 }, positiveExtended index) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      simp [positiveExtended, index.2]
    calc
      _ = ∑ index : ThroatSpatialTruncatedIndex 4,
          positiveExtended index := rfl
      _ = ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
            index.1 direction ≠ 0 }, positiveExtended index := by
        rw [← hSplit, hComplement, add_zero]
      _ = ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
            index.1 direction ≠ 0 }, positiveSummand index := by
        apply Finset.sum_congr rfl
        intro index _
        simp [positiveExtended, positiveSummand, index.2]
  calc
    _ = ∑ index : { index : ThroatSpatialTruncatedIndex 4 //
          index.1 direction ≠ 0 }, positiveSummand index := hSubtype
    _ = ∑ index : ThroatSpatialTruncatedIndex 3,
          positiveSummand
            (programPT06TruncatedIndexSuccessorEquiv 3 direction index) :=
      (programPT06TruncatedIndexSuccessorEquiv_sum_comp
        (M := A) 3 direction positiveSummand).symm
    _ = ∑ index : ThroatSpatialTruncatedIndex 3,
          -(((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
            term index) := by
      apply Finset.sum_congr rfl
      intro index _
      change
        ((-1 : Real) ^ throatSpatialMultiIndexOrder
          (index.1 + throatSpatialCoordinateMultiIndex direction)) •
            term (programPT06TruncatedIndexSuccessorPredecessor
              3 direction
                (programPT06TruncatedIndexSuccessor 3 direction index)) =
          -(((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) • term index)
      rw [programPT06TruncatedIndexSuccessorPredecessor_left,
        throatSpatialMultiIndexOrder_add_coordinateMultiIndex,
        pow_succ, mul_neg, mul_one, neg_smul]
    _ = -∑ index : ThroatSpatialTruncatedIndex 3,
          ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) • term index :=
      by simp only [Finset.sum_neg_distrib]

/-- The lower-order and positive-successor contributions cancel. -/
theorem programPT06SignedTruncatedIndexTelescoping_eq_zero
    (direction : Fin 3)
    (term : ThroatSpatialTruncatedIndex 3 → A) :
    (∑ index : ThroatSpatialTruncatedIndex 4,
      if hLower : throatSpatialMultiIndexOrder index.1 ≤ 3 then
        ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
          term ⟨index.1, hLower⟩
      else 0) +
      (∑ index : ThroatSpatialTruncatedIndex 4,
        if hPositive : index.1 direction ≠ 0 then
          ((-1 : Real) ^ throatSpatialMultiIndexOrder index.1) •
            term (programPT06TruncatedIndexSuccessorPredecessor
              3 direction ⟨index, hPositive⟩)
        else 0) = 0 := by
  rw [programPT06SignedLowerOrderSum_eq,
    programPT06SignedSuccessorSum_eq_neg, add_neg_cancel]

end
end P0EFTJanusProgramPT06SignedTruncatedIndexTelescoping4D
end JanusFormal
