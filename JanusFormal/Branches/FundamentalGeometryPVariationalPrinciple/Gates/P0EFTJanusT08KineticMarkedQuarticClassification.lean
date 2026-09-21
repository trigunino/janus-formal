import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08KineticPointTransformationRigidity
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08QuarticDeformationFreedom4D

/-!
# T08: quartic coupling with a fixed scalar kinetic term

This finite scalar local class includes the canonical quadratic velocity
term, a marked reference value and a relative quartic coupling. Comparison
allows a C1 point transformation, a field-only boundary-current derivative
and an additive constant. Both the kinetic coefficient and absolute action
scale are fixed, not physically derived. A separate identity exhibits the
remaining ambiguity when field and action scalings are allowed together.
No derivative-dependent redefinitions or full BV quotient is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusT08KineticMarkedQuarticClassification

set_option autoImplicit false
noncomputable section

open P0EFTJanusT08KineticPointTransformationRigidity

def density (coupling reference value velocity : Real) : Real :=
  velocity ^ 2 / 2 + (value - reference) ^ 2 + coupling * (value - reference) ^ 4

/-- The potential is exactly the previously constructed T02 functional.
Only the extra one-dimensional canonical kinetic mark is supplied here. -/
theorem density_eq_actual_T02_potential (period : Real) (hPeriod : period ≠ 0)
    (coupling reference velocity : Real)
    (jet : P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D.ActualPhysicalSecondOrderJetProductFiber) :
    density coupling reference (P0EFTJanusT08InvariantDeformationFreedom4D.t08LLMeasureValue jet)
      velocity = velocity ^ 2 / 2 +
      P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D.actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation
        period hPeriod
        (P0EFTJanusT08QuarticDeformationFreedom4D.t08NormalizedQuarticInvariantDeformation
          period hPeriod reference coupling) jet := by
  rw [P0EFTJanusT08QuarticDeformationFreedom4D.t08NormalizedQuarticInvariantDeformation_evaluation]
  unfold density
  ring

/-- The odd velocity coefficient is exactly the possible field-only boundary
current term; the even quadratic coefficient is the kinetic mark. -/
theorem density_comparison_separates_kinetic_and_boundary
    (first second reference : Real) (transform jacobian boundary : Real → Real)
    (offset : Real)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        density first reference value velocity + boundary value * velocity + offset) :
    (∀ value, jacobian value ^ 2 = 1) ∧ (∀ value, boundary value = 0) := by
  have hCoefficients (value : Real) : jacobian value ^ 2 = 1 ∧ boundary value = 0 := by
    have hZero := hCompare value 0
    have hPlus := hCompare value 1
    have hMinus := hCompare value (-1)
    dsimp [density] at hZero hPlus hMinus
    constructor <;> nlinarith
  exact ⟨fun value => (hCoefficients value).1, fun value => (hCoefficients value).2⟩

theorem marked_reference_fixes_offset
    (first second reference : Real) (transform jacobian boundary : Real → Real)
    (offset : Real) (hReference : transform reference = reference)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        density first reference value velocity + boundary value * velocity + offset) :
    offset = 0 := by
  have h := hCompare reference 0
  simpa [density, hReference] using h.symm

/-- Once squared displacement is preserved, the full density comparison
identifies the relative quartic coefficient. -/
theorem squared_displacement_selects_coupling
    (first second reference : Real) (transform jacobian boundary : Real → Real)
    (offset : Real) (hReference : transform reference = reference)
    (hSquare : ∀ value, (transform value - reference) ^ 2 = (value - reference) ^ 2)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        density first reference value velocity + boundary value * velocity + offset) :
    first = second := by
  have hOffset := marked_reference_fixes_offset first second reference transform jacobian
    boundary offset hReference hCompare
  have hTwo : (transform (reference + 1) - reference) ^ 2 = 1 := by
    simpa using hSquare (reference + 1)
  have hFour : (transform (reference + 1) - reference) ^ 4 = 1 := by
    nlinarith [sq_nonneg ((transform (reference + 1) - reference) ^ 2 - 1)]
  have h := hCompare (reference + 1) 0
  simp [density, hOffset, hTwo, hFour] at h
  linarith

/-- Every nonnegative quartic coefficient yields a nonnegative density, with
the same scalar rest configuration. -/
theorem density_nonnegative (coupling reference value velocity : Real)
    (hCoupling : 0 ≤ coupling) : 0 ≤ density coupling reference value velocity := by
  unfold density
  positivity

theorem density_at_reference (coupling reference : Real) :
    density coupling reference reference 0 = 0 := by simp [density]

/-- These local representatives have the same quadratic value/velocity terms;
the coupling is a genuinely higher-order term in this fixed coordinate. -/
theorem density_difference (first second reference value velocity : Real) :
    density first reference value velocity - density second reference value velocity =
      (first - second) * (value - reference) ^ 4 := by unfold density; ring

/-- The kinetic mark is inferred from equality of densities, then integrated
using the actual derivative of the point transformation. -/
theorem kinetic_point_comparison_selects_coupling
    (first second reference : Real) (transform jacobian boundary : Real → Real)
    (offset : Real) (hDerivative : ∀ value, HasDerivAt transform (jacobian value) value)
    (hContinuous : Continuous jacobian) (hReference : transform reference = reference)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        density first reference value velocity + boundary value * velocity + offset) :
    first = second := by
  have hUnit := (density_comparison_separates_kinetic_and_boundary first second reference
    transform jacobian boundary offset hCompare).1
  exact squared_displacement_selects_coupling first second reference transform jacobian
    boundary offset hReference
    (unit_kinetic_sq_displacement transform jacobian reference
      hDerivative hContinuous hUnit hReference) hCompare

/-- Equivalence in the declared local scalar class, at fixed absolute action
scale. The boundary coefficient may be any function, so this includes every
total derivative of a differentiable current depending only on the field. -/
def PointEquivalent (first second reference : Real) : Prop :=
  ∃ transform jacobian boundary : Real → Real, ∃ offset : Real,
    (∀ value, HasDerivAt transform (jacobian value) value) ∧
    Continuous jacobian ∧ transform reference = reference ∧
    ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        density first reference value velocity + boundary value * velocity + offset

theorem pointEquivalent_iff (first second reference : Real) :
    PointEquivalent first second reference ↔ first = second := by
  constructor
  · rintro ⟨transform, jacobian, boundary, offset, hDerivative, hContinuous, hReference, hCompare⟩
    exact kinetic_point_comparison_selects_coupling first second reference transform jacobian
      boundary offset hDerivative hContinuous hReference hCompare
  · intro hEqual
    subst second
    refine ⟨id, fun _ => 1, fun _ => 0, 0, ?_, continuous_const, rfl, ?_⟩
    · intro value
      exact hasDerivAt_id value
    · intro value velocity
      simp

/-- If an actual primitive is supplied, the allowed boundary current must
be constant; the proof does not confuse an odd velocity term with a kinetic term. -/
theorem boundary_primitive_constant
    (first second reference : Real) (transform jacobian boundary current : Real → Real)
    (offset : Real) (hCurrent : ∀ value, HasDerivAt current (boundary value) value)
    (hCompare : ∀ value velocity,
      density second reference (transform value) (jacobian value * velocity) =
        density first reference value velocity + boundary value * velocity + offset)
    (x y : Real) : current x = current y := by
  have hBoundary := (density_comparison_separates_kinetic_and_boundary first second reference
    transform jacobian boundary offset hCompare).2
  apply is_const_of_deriv_eq_zero (fun value => (hCurrent value).differentiableAt) _ x y
  intro value
  rw [(hCurrent value).deriv, hBoundary value]

/-- Keeping canonical kinetic form while allowing an overall action scale
does not fix the numerical coupling. For nonzero scale this is invertible. -/
theorem simultaneous_field_action_scaling (coupling reference scale value velocity : Real) :
    density coupling reference (reference + scale * (value - reference)) (scale * velocity) =
      scale ^ 2 * density (coupling * scale ^ 2) reference value velocity := by
  unfold density
  ring

theorem positive_examples_distinct_at_fixed_scale (reference : Real) :
    ¬ PointEquivalent 1 (1 / 4) reference := by rw [pointEquivalent_iff]; norm_num

theorem positive_examples_equivalent_with_action_scaling (reference value velocity : Real) :
    density (1 / 4) reference (reference + 2 * (value - reference)) (2 * velocity) =
      4 * density 1 reference value velocity := by
  convert simultaneous_field_action_scaling (1 / 4) reference 2 value velocity using 1
  norm_num

end
end P0EFTJanusT08KineticMarkedQuarticClassification
end JanusFormal
