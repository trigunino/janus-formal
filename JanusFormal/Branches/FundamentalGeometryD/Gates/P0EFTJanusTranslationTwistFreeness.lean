import Mathlib

namespace JanusFormal
namespace P0EFTJanusTranslationTwistFreeness

set_option autoImplicit false

variable {X : Type*}

/-- Abstract action of the integer monodromy group on the fiber. -/
structure IntegerFiberAction (X : Type*) where
  act : ℤ → X → X
  zero_act : ∀ x, act 0 x = x
  add_act : ∀ m n x, act (m + n) x = act m (act n x)

/-- Combined fiber monodromy and translation on the logarithmic radial line. -/
def totalAction
    (fiber : IntegerFiberAction X)
    (period : ℝ)
    (n : ℤ)
    (p : X × ℝ) : X × ℝ :=
  (fiber.act n p.1, p.2 + (n : ℝ) * period)

@[simp] theorem total_action_zero
    (fiber : IntegerFiberAction X)
    (period : ℝ)
    (p : X × ℝ) :
    totalAction fiber period 0 p = p := by
  rcases p with ⟨x, u⟩
  simp [totalAction, fiber.zero_act]

/-- The combined transformations satisfy the integer action law. -/
theorem total_action_add
    (fiber : IntegerFiberAction X)
    (period : ℝ)
    (m n : ℤ)
    (p : X × ℝ) :
    totalAction fiber period (m + n) p =
      totalAction fiber period m
        (totalAction fiber period n p) := by
  rcases p with ⟨x, u⟩
  apply Prod.ext
  · simp [totalAction, fiber.add_act]
  · simp [totalAction]
    ring

/--
A nonzero translation period makes the full integer action free, independently
of the detailed fiber monodromy.
-/
theorem total_action_is_free_when_period_nonzero
    (fiber : IntegerFiberAction X)
    (period : ℝ)
    (hPeriod : period ≠ 0)
    (n : ℤ)
    (p : X × ℝ)
    (hFixed : totalAction fiber period n p = p) :
    n = 0 := by
  have hSecond := congrArg Prod.snd hFixed
  change p.2 + (n : ℝ) * period = p.2 at hSecond
  have hProduct : (n : ℝ) * period = 0 := by
    linarith
  have hCast : (n : ℝ) = 0 :=
    (mul_eq_zero.mp hProduct).resolve_right hPeriod
  exact_mod_cast hCast

/-- Every nontrivial integer element acts without fixed points. -/
theorem nontrivial_element_has_no_fixed_point
    (fiber : IntegerFiberAction X)
    (period : ℝ)
    (hPeriod : period ≠ 0)
    (n : ℤ)
    (hNonzero : n ≠ 0)
    (p : X × ℝ) :
    totalAction fiber period n p ≠ p := by
  intro hFixed
  exact hNonzero
    (total_action_is_free_when_period_nonzero
      fiber period hPeriod n p hFixed)

/--
The remaining smooth-quotient theorem is proper discontinuity and manifold
structure. Freeness itself is completely controlled by the logarithmic
translation and does not require the reflection to be fixed-point free.
-/
structure SmoothQuotientStatus where
  integerActionLawDerived : Prop
  actionFreeDerived : Prop
  actionProperlyDiscontinuousDerived : Prop
  quotientHausdorffDerived : Prop
  quotientSmoothStructureDerived : Prop
  coveringProjectionDerived : Prop


def smoothQuotientClosed (s : SmoothQuotientStatus) : Prop :=
  s.integerActionLawDerived /\
  s.actionFreeDerived /\
  s.actionProperlyDiscontinuousDerived /\
  s.quotientHausdorffDerived /\
  s.quotientSmoothStructureDerived /\
  s.coveringProjectionDerived

end P0EFTJanusTranslationTwistFreeness
end JanusFormal
