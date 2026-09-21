import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08KineticMarkedQuarticClassification

/-!
# T08: scalar quartic classification when positive action scaling is allowed

Within the declared real scalar local class, C1 point transformations fixing
the reference, field-only boundary currents, additive constants and a positive
overall action factor identify exactly quartic coefficients of the same sign.
Thus the nonnegative family has two classes: zero and positive coupling.
This is not a classification of all Janus fields or of the BV quotient.
-/

namespace JanusFormal
namespace P0EFTJanusT08ScaledQuarticClassification

set_option autoImplicit false
noncomputable section

open P0EFTJanusT08KineticMarkedQuarticClassification
open P0EFTJanusT08KineticPointTransformationRigidity

theorem scaled_comparison_separates_kinetic_and_boundary
    (first second reference scale : Real) (transform jacobian boundary : Real → Real)
    (offset : Real)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        scale * density first reference value velocity + boundary value * velocity + offset) :
    (∀ value, jacobian value ^ 2 = scale) ∧ (∀ value, boundary value = 0) := by
  have hCoefficients (value : Real) : jacobian value ^ 2 = scale ∧ boundary value = 0 := by
    have hZero := hCompare value 0
    have hPlus := hCompare value 1
    have hMinus := hCompare value (-1)
    dsimp [density] at hZero hPlus hMinus
    constructor <;> nlinarith
  exact ⟨fun value => (hCoefficients value).1, fun value => (hCoefficients value).2⟩

theorem scaled_reference_fixes_offset
    (first second reference scale : Real) (transform jacobian boundary : Real → Real)
    (offset : Real) (hReference : transform reference = reference)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        scale * density first reference value velocity + boundary value * velocity + offset) :
    offset = 0 := by
  have h := hCompare reference 0
  simpa [density, hReference] using h.symm

/-- The only surviving coefficient relation is first = scale * second. -/
theorem scaled_point_comparison_selects_ratio
    (first second reference scale : Real) (hScale : 0 < scale)
    (transform jacobian boundary : Real → Real) (offset : Real)
    (hDerivative : ∀ value, HasDerivAt transform (jacobian value) value)
    (hContinuous : Continuous jacobian) (hReference : transform reference = reference)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        scale * density first reference value velocity + boundary value * velocity + offset) :
    first = scale * second := by
  have hKinetic := (scaled_comparison_separates_kinetic_and_boundary first second reference
    scale transform jacobian boundary offset hCompare).1
  have hSquare := positive_kinetic_sq_displacement transform jacobian reference scale
    hScale hDerivative hContinuous hKinetic hReference
  have hTwo : (transform (reference + 1) - reference) ^ 2 = scale := by
    simpa using hSquare (reference + 1)
  have hFour : (transform (reference + 1) - reference) ^ 4 = scale ^ 2 := by
    calc
      _ = ((transform (reference + 1) - reference) ^ 2) ^ 2 := by ring
      _ = scale ^ 2 := by rw [hTwo]
  have hOffset := scaled_reference_fixes_offset first second reference scale transform
    jacobian boundary offset hReference hCompare
  have h := hCompare (reference + 1) 0
  simp [density, hOffset, hTwo, hFour] at h
  apply mul_left_cancel₀ (ne_of_gt hScale) (b := first) (c := scale * second)
  nlinarith

def ScaledPointEquivalent (first second reference : Real) : Prop :=
  ∃ scale : Real, 0 < scale ∧
    ∃ transform jacobian boundary : Real → Real, ∃ offset : Real,
      (∀ value, HasDerivAt transform (jacobian value) value) ∧
      Continuous jacobian ∧ transform reference = reference ∧
      ∀ value velocity,
        density second reference (transform value) (jacobian value * velocity) =
          scale * density first reference value velocity + boundary value * velocity + offset

theorem scaledPointEquivalent_iff_positive_multiple (first second reference : Real) :
    ScaledPointEquivalent first second reference ↔ ∃ scale : Real, 0 < scale ∧ first = scale * second := by
  constructor
  · rintro ⟨scale, hScale, transform, jacobian, boundary, offset,
      hDerivative, hContinuous, hReference, hCompare⟩
    exact ⟨scale, hScale, scaled_point_comparison_selects_ratio first second reference scale
      hScale transform jacobian boundary offset hDerivative hContinuous hReference hCompare⟩
  · rintro ⟨scale, hScale, hRatio⟩
    let root := Real.sqrt scale
    have hRoot : root ^ 2 = scale := Real.sq_sqrt hScale.le
    refine ⟨scale, hScale, fun value => reference + root * (value - reference),
      fun _ => root, fun _ => 0, 0, ?_, continuous_const, ?_, ?_⟩
    · intro value
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id value).sub_const reference).const_mul root).const_add reference
    · simp
    · intro value velocity
      have h := simultaneous_field_action_scaling second reference root value velocity
      rw [hRoot, mul_comm second scale, ← hRatio] at h
      simpa only [zero_mul, add_zero] using h

/-- Three classes on the full real parameter line; no numerical positive
coupling survives this larger equivalence category. -/
theorem scaledPointEquivalent_iff_sign_classes (first second reference : Real) :
    ScaledPointEquivalent first second reference ↔
      (first = 0 ∧ second = 0) ∨ (0 < first ∧ 0 < second) ∨ (first < 0 ∧ second < 0) := by
  rw [scaledPointEquivalent_iff_positive_multiple]
  constructor
  · rintro ⟨scale, hScale, rfl⟩
    rcases lt_trichotomy second 0 with hNegative | hZero | hPositive
    · exact Or.inr (Or.inr ⟨mul_neg_of_pos_of_neg hScale hNegative, hNegative⟩)
    · exact Or.inl ⟨by rw [hZero, mul_zero], hZero⟩
    · exact Or.inr (Or.inl ⟨mul_pos hScale hPositive, hPositive⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨hFirst, hSecond⟩ | ⟨hFirst, hSecond⟩)
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨first / second, div_pos hFirst hSecond, (div_mul_cancel₀ first (ne_of_gt hSecond)).symm⟩
    · exact ⟨first / second, div_pos_of_neg_of_neg hFirst hSecond,
        (div_mul_cancel₀ first (ne_of_lt hSecond)).symm⟩

theorem nonnegative_scaledPointEquivalent_iff (first second reference : Real)
    (hFirst : 0 ≤ first) (hSecond : 0 ≤ second) :
    ScaledPointEquivalent first second reference ↔ (first = 0 ↔ second = 0) := by
  rw [scaledPointEquivalent_iff_sign_classes]
  constructor
  · rintro (⟨hF, hS⟩ | ⟨hF, hS⟩ | ⟨hF, hS⟩)
    · simp [hF, hS]
    · simp [ne_of_gt hF, ne_of_gt hS]
    · linarith
  · intro hZero
    by_cases hF : first = 0
    · exact Or.inl ⟨hF, hZero.mp hF⟩
    · exact Or.inr (Or.inl ⟨lt_of_le_of_ne hFirst (Ne.symm hF),
        lt_of_le_of_ne hSecond (Ne.symm (mt hZero.mpr hF))⟩)

theorem zero_not_equivalent_to_positive (coupling reference : Real) (hCoupling : 0 < coupling) :
    ¬ ScaledPointEquivalent 0 coupling reference := by
  rw [nonnegative_scaledPointEquivalent_iff 0 coupling reference (by norm_num) hCoupling.le]
  simp [ne_of_gt hCoupling]

end
end P0EFTJanusT08ScaledQuarticClassification
end JanusFormal
