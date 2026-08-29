import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteDefectReducedResolvent4D

/-!
# Resolvent identity on the finite-defect complement

Inside the coercive real gap, the reduced resolvents satisfy the first
resolvent identity

`R(lambda) - R(mu) = (lambda - mu) R(lambda) R(mu)`.

Combining this identity with the gap estimates gives the quantitative
operator-norm bound

`‖R(lambda) - R(mu)‖
  ≤ |lambda - mu| (c - |lambda|)⁻¹ (c - |mu|)⁻¹`.

This is the continuity estimate needed before any determinant or parametric
Quillen construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteDefectReducedResolventIdentity4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteDefectCoerciveShift4D
open P0EFTJanusProgramPFiniteDefectReducedOperator4D
open P0EFTJanusProgramPFiniteDefectReducedResolvent4D
open scoped InnerProductSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

local instance finiteDefectReducedResolventIdentityCompleteSpace
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator) :
    CompleteSpace data.projection.ker :=
  inferInstance

/-- Change of real spectral parameter for the reduced shifted operator. -/
theorem finiteDefectReducedShiftedOperator_change_parameter
    (operator : E →L[Real] E)
    (data : FiniteDefectCoerciveShiftData operator)
    (firstParameter secondParameter : Real)
    (vector : data.projection.ker) :
    finiteDefectReducedShiftedOperator operator data secondParameter vector =
      finiteDefectReducedShiftedOperator operator data firstParameter vector +
        (firstParameter - secondParameter) • vector := by
  rw [finiteDefectReducedShiftedOperator_apply,
    finiteDefectReducedShiftedOperator_apply]
  module

/-- First real resolvent identity on the exact zero-mode complement. -/
theorem finiteDefectReducedRealResolvent_identity
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (firstParameter secondParameter : Real)
    (hFirst : |firstParameter| < data.coercivityConstant)
    (hSecond : |secondParameter| < data.coercivityConstant) :
    finiteDefectReducedRealResolvent operator hSelfAdjoint data firstParameter
        hFirst -
      finiteDefectReducedRealResolvent operator hSelfAdjoint data secondParameter
        hSecond =
      (firstParameter - secondParameter) •
        ((finiteDefectReducedRealResolvent operator hSelfAdjoint data
            firstParameter hFirst).comp
          (finiteDefectReducedRealResolvent operator hSelfAdjoint data
            secondParameter hSecond)) := by
  apply ContinuousLinearMap.ext
  intro vector
  let firstResolvent := finiteDefectReducedRealResolvent operator hSelfAdjoint
    data firstParameter hFirst
  let secondResolvent := finiteDefectReducedRealResolvent operator hSelfAdjoint
    data secondParameter hSecond
  let firstShift := finiteDefectReducedShiftedOperator operator data
    firstParameter
  let secondShift := finiteDefectReducedShiftedOperator operator data
    secondParameter
  have hSecondInverse : secondShift (secondResolvent vector) = vector := by
    exact finiteDefectReducedShiftedOperator_resolvent operator hSelfAdjoint data
      secondParameter hSecond vector
  have hFirstInverse :
      firstResolvent (firstShift (secondResolvent vector)) =
        secondResolvent vector := by
    exact finiteDefectReducedResolvent_shiftedOperator operator hSelfAdjoint data
      firstParameter hFirst (secondResolvent vector)
  change firstResolvent vector - secondResolvent vector =
    (firstParameter - secondParameter) •
      firstResolvent (secondResolvent vector)
  calc
    firstResolvent vector - secondResolvent vector =
        firstResolvent (secondShift (secondResolvent vector)) -
          secondResolvent vector := by rw [hSecondInverse]
    _ = firstResolvent
          (firstShift (secondResolvent vector) +
            (firstParameter - secondParameter) • secondResolvent vector) -
          secondResolvent vector := by
      rw [finiteDefectReducedShiftedOperator_change_parameter operator data
        firstParameter secondParameter]
    _ = (firstParameter - secondParameter) •
        firstResolvent (secondResolvent vector) := by
      rw [map_add, map_smul, hFirstInverse]
      module

/-- Pointwise quantitative continuity of the reduced resolvent. -/
theorem finiteDefectReducedRealResolvent_sub_norm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (firstParameter secondParameter : Real)
    (hFirst : |firstParameter| < data.coercivityConstant)
    (hSecond : |secondParameter| < data.coercivityConstant)
    (vector : data.projection.ker) :
    ‖(finiteDefectReducedRealResolvent operator hSelfAdjoint data firstParameter
          hFirst -
        finiteDefectReducedRealResolvent operator hSelfAdjoint data
          secondParameter hSecond) vector‖ ≤
      |firstParameter - secondParameter| *
        (data.coercivityConstant - |firstParameter|)⁻¹ *
        (data.coercivityConstant - |secondParameter|)⁻¹ * ‖vector‖ := by
  have hIdentity := congrArg
    (fun map : data.projection.ker →L[Real] data.projection.ker => map vector)
    (finiteDefectReducedRealResolvent_identity operator hSelfAdjoint data
      firstParameter secondParameter hFirst hSecond)
  change
    (finiteDefectReducedRealResolvent operator hSelfAdjoint data firstParameter
          hFirst -
        finiteDefectReducedRealResolvent operator hSelfAdjoint data
          secondParameter hSecond) vector =
      (firstParameter - secondParameter) •
        finiteDefectReducedRealResolvent operator hSelfAdjoint data firstParameter
          hFirst
          (finiteDefectReducedRealResolvent operator hSelfAdjoint data
            secondParameter hSecond vector) at hIdentity
  rw [hIdentity, norm_smul, Real.norm_eq_abs]
  have hFirstBound := finiteDefectReducedRealResolvent_norm_le operator
    hSelfAdjoint data firstParameter hFirst
      (finiteDefectReducedRealResolvent operator hSelfAdjoint data
        secondParameter hSecond vector)
  have hSecondBound := finiteDefectReducedRealResolvent_norm_le operator
    hSelfAdjoint data secondParameter hSecond vector
  have hFirstInverseNonneg :
      0 ≤ (data.coercivityConstant - |firstParameter|)⁻¹ :=
    inv_nonneg.mpr (by linarith)
  calc
    |firstParameter - secondParameter| *
        ‖finiteDefectReducedRealResolvent operator hSelfAdjoint data
          firstParameter hFirst
          (finiteDefectReducedRealResolvent operator hSelfAdjoint data
            secondParameter hSecond vector)‖
        ≤ |firstParameter - secondParameter| *
          ((data.coercivityConstant - |firstParameter|)⁻¹ *
            ‖finiteDefectReducedRealResolvent operator hSelfAdjoint data
              secondParameter hSecond vector‖) :=
      mul_le_mul_of_nonneg_left hFirstBound (abs_nonneg _)
    _ ≤ |firstParameter - secondParameter| *
          ((data.coercivityConstant - |firstParameter|)⁻¹ *
            ((data.coercivityConstant - |secondParameter|)⁻¹ * ‖vector‖)) := by
      apply mul_le_mul_of_nonneg_left
      exact mul_le_mul_of_nonneg_left hSecondBound hFirstInverseNonneg
      exact abs_nonneg _
    _ = |firstParameter - secondParameter| *
        (data.coercivityConstant - |firstParameter|)⁻¹ *
        (data.coercivityConstant - |secondParameter|)⁻¹ * ‖vector‖ := by
      ring

/-- Operator-norm continuity estimate for the real resolvent family. -/
theorem finiteDefectReducedRealResolvent_sub_opNorm_le
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (firstParameter secondParameter : Real)
    (hFirst : |firstParameter| < data.coercivityConstant)
    (hSecond : |secondParameter| < data.coercivityConstant) :
    ‖finiteDefectReducedRealResolvent operator hSelfAdjoint data firstParameter
          hFirst -
        finiteDefectReducedRealResolvent operator hSelfAdjoint data
          secondParameter hSecond‖ ≤
      |firstParameter - secondParameter| *
        (data.coercivityConstant - |firstParameter|)⁻¹ *
        (data.coercivityConstant - |secondParameter|)⁻¹ := by
  have hNonneg :
      0 ≤ |firstParameter - secondParameter| *
        (data.coercivityConstant - |firstParameter|)⁻¹ *
        (data.coercivityConstant - |secondParameter|)⁻¹ := by
    positivity
  apply (finiteDefectReducedRealResolvent operator hSelfAdjoint data
      firstParameter hFirst -
    finiteDefectReducedRealResolvent operator hSelfAdjoint data
      secondParameter hSecond).opNorm_le_bound hNonneg
  intro vector
  simpa [mul_assoc] using
    finiteDefectReducedRealResolvent_sub_norm_le operator hSelfAdjoint data
      firstParameter secondParameter hFirst hSecond vector

/-- Public resolvent-identity checkpoint. -/
theorem finite_defect_reduced_real_resolvent_identity_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : FiniteDefectCoerciveShiftData operator)
    (firstParameter secondParameter : Real)
    (hFirst : |firstParameter| < data.coercivityConstant)
    (hSecond : |secondParameter| < data.coercivityConstant) :
    finiteDefectReducedRealResolvent operator hSelfAdjoint data firstParameter
        hFirst -
      finiteDefectReducedRealResolvent operator hSelfAdjoint data secondParameter
        hSecond =
      (firstParameter - secondParameter) •
        ((finiteDefectReducedRealResolvent operator hSelfAdjoint data
            firstParameter hFirst).comp
          (finiteDefectReducedRealResolvent operator hSelfAdjoint data
            secondParameter hSecond)) ∧
      ‖finiteDefectReducedRealResolvent operator hSelfAdjoint data firstParameter
            hFirst -
          finiteDefectReducedRealResolvent operator hSelfAdjoint data
            secondParameter hSecond‖ ≤
        |firstParameter - secondParameter| *
          (data.coercivityConstant - |firstParameter|)⁻¹ *
          (data.coercivityConstant - |secondParameter|)⁻¹ :=
  ⟨finiteDefectReducedRealResolvent_identity operator hSelfAdjoint data
      firstParameter secondParameter hFirst hSecond,
    finiteDefectReducedRealResolvent_sub_opNorm_le operator hSelfAdjoint data
      firstParameter secondParameter hFirst hSecond⟩

end
end P0EFTJanusProgramPFiniteDefectReducedResolventIdentity4D
end JanusFormal
