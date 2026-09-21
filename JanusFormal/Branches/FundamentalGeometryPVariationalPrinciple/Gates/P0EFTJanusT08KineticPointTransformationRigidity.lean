import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# T08: point transformations preserving a unit scalar kinetic coefficient

A continuous real Jacobian satisfying `g(x)^2 = 1` cannot change sign on the
connected real line. If it is the derivative of a field redefinition, that
redefinition is affine. Fixing a marked reference leaves only identity and
reflection, so its squared scalar displacement is preserved.

The hypothesis is a local Jacobian identity, not an assumed global isometry.
This addresses C1 point transformations of one real scalar only.
-/

namespace JanusFormal
namespace P0EFTJanusT08KineticPointTransformationRigidity

set_option autoImplicit false
noncomputable section

/-- The unit-Jacobian condition and continuity force one global sign. -/
theorem continuous_unit_jacobian_constant
    (g : Real → Real) (v : Real) (hContinuous : Continuous g)
    (hUnit : ∀ x, (g x) ^ 2 = 1) : ∀ x, g x = g v := by
  have hNoZero : ¬ ∃ x, g x = 0 := by
    rintro ⟨x, hx⟩
    have h := hUnit x
    simp [hx] at h
  intro x
  rcases sq_eq_one_iff.mp (hUnit x) with hx | hx <;>
    rcases sq_eq_one_iff.mp (hUnit v) with hv | hv
  · exact hx.trans hv.symm
  · exfalso
    apply hNoZero
    exact intermediate_value_univ₂ (a := v) (b := x) hContinuous continuous_const
      (by simp [hv]) (by simp [hx])
  · exfalso
    apply hNoZero
    exact intermediate_value_univ₂ (a := x) (b := v) hContinuous continuous_const
      (by simp [hx]) (by simp [hv])
  · exact hx.trans hv.symm

/-- Unit kinetic coefficient and a fixed reference force an affine sign map. -/
theorem unit_kinetic_affine_of_fixed_reference
    (f g : Real → Real) (v : Real)
    (hDerivative : ∀ x, HasDerivAt f (g x) x)
    (hContinuous : Continuous g) (hUnit : ∀ x, (g x) ^ 2 = 1)
    (hFixed : f v = v) : ∀ x, f x - v = g v * (x - v) := by
  have hConstant := continuous_unit_jacobian_constant g v hContinuous hUnit
  have hZero : ∀ x, HasDerivAt (fun y => f y - g v * y) 0 x := by
    intro x
    simpa only [hConstant x, mul_one, sub_self, id_eq] using
      (hDerivative x).fun_sub ((hasDerivAt_id x).const_mul (g v))
  intro x
  have h := is_const_of_deriv_eq_zero
    (fun y => (hZero y).differentiableAt) (fun y => (hZero y).deriv) x v
  rw [hFixed] at h
  nlinarith

/-- Identity and reflection are the complete fixed-reference alternatives. -/
theorem unit_kinetic_identity_or_reflection
    (f g : Real → Real) (v : Real)
    (hDerivative : ∀ x, HasDerivAt f (g x) x)
    (hContinuous : Continuous g) (hUnit : ∀ x, (g x) ^ 2 = 1)
    (hFixed : f v = v) :
    (∀ x, f x = x) ∨ (∀ x, f x = 2 * v - x) := by
  have hAffine := unit_kinetic_affine_of_fixed_reference
    f g v hDerivative hContinuous hUnit hFixed
  rcases sq_eq_one_iff.mp (hUnit v) with hSign | hSign
  · left
    intro x
    have h := hAffine x
    rw [hSign] at h
    linarith
  · right
    intro x
    have h := hAffine x
    rw [hSign] at h
    linarith

/-- A marked scalar potential depending on squared displacement is preserved. -/
theorem unit_kinetic_sq_displacement
    (f g : Real → Real) (v : Real)
    (hDerivative : ∀ x, HasDerivAt f (g x) x)
    (hContinuous : Continuous g) (hUnit : ∀ x, (g x) ^ 2 = 1)
    (hFixed : f v = v) : ∀ x, (f x - v) ^ 2 = (x - v) ^ 2 := by
  intro x
  rw [unit_kinetic_affine_of_fixed_reference
    f g v hDerivative hContinuous hUnit hFixed x, mul_pow, hUnit v, one_mul]

/-- A positive constant kinetic scale still forces one constant Jacobian. -/
theorem positive_kinetic_jacobian_constant
    (g : Real → Real) (v scale : Real) (hScale : 0 < scale)
    (hContinuous : Continuous g) (hSquare : ∀ x, (g x) ^ 2 = scale) :
    ∀ x, g x = g v := by
  have hRoot : Real.sqrt scale ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hScale)
  have hNormalized : ∀ x, (g x / Real.sqrt scale) ^ 2 = 1 := by
    intro x
    rw [div_pow, hSquare x, Real.sq_sqrt (le_of_lt hScale),
      div_self (ne_of_gt hScale)]
  have hConstant := continuous_unit_jacobian_constant
    (fun x => g x / Real.sqrt scale) v (hContinuous.div_const _) hNormalized
  intro x
  exact (div_left_inj' hRoot).mp (hConstant x)

/-- The affine conclusion follows from the actual derivative identity at any
positive constant kinetic scale. -/
theorem positive_kinetic_affine_of_fixed_reference
    (f g : Real → Real) (v scale : Real) (hScale : 0 < scale)
    (hDerivative : ∀ x, HasDerivAt f (g x) x)
    (hContinuous : Continuous g) (hSquare : ∀ x, (g x) ^ 2 = scale)
    (hFixed : f v = v) : ∀ x, f x - v = g v * (x - v) := by
  have hConstant := positive_kinetic_jacobian_constant g v scale hScale hContinuous hSquare
  have hZero : ∀ x, HasDerivAt (fun y => f y - g v * y) 0 x := by
    intro x
    simpa only [hConstant x, mul_one, sub_self, id_eq] using
      (hDerivative x).fun_sub ((hasDerivAt_id x).const_mul (g v))
  intro x
  have h := is_const_of_deriv_eq_zero
    (fun y => (hZero y).differentiableAt) (fun y => (hZero y).deriv) x v
  rw [hFixed] at h
  nlinarith

/-- A local constant kinetic-scale law fixes the squared scalar displacement
without assuming a global similarity beforehand. -/
theorem positive_kinetic_sq_displacement
    (f g : Real → Real) (v scale : Real) (hScale : 0 < scale)
    (hDerivative : ∀ x, HasDerivAt f (g x) x)
    (hContinuous : Continuous g) (hSquare : ∀ x, (g x) ^ 2 = scale)
    (hFixed : f v = v) : ∀ x, (f x - v) ^ 2 = scale * (x - v) ^ 2 := by
  intro x
  rw [positive_kinetic_affine_of_fixed_reference
    f g v scale hScale hDerivative hContinuous hSquare hFixed x, mul_pow, hSquare v]

end
end P0EFTJanusT08KineticPointTransformationRigidity
end JanusFormal
