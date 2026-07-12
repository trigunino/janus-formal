import Mathlib

namespace JanusFormal
namespace P0EFTJanusOneSidedThroatNormalMonodromy

set_option autoImplicit false

/-- Local normal coordinate and logarithmic mapping-torus coordinate. -/
abbrev NormalCylinderPoint := ℝ × ℝ

/-- The reflection mapping-torus gluing reverses the throat normal coordinate. -/
def normalStep
    (period : ℝ) (p : NormalCylinderPoint) : NormalCylinderPoint :=
  (-p.1, p.2 + period)

/-- Two traversals restore the normal direction and translate by `2T`. -/
theorem normal_step_square
    (period : ℝ) (p : NormalCylinderPoint) :
    normalStep period (normalStep period p) =
      (p.1, p.2 + 2 * period) := by
  rcases p with ⟨normal, u⟩
  simp [normalStep]
  ring

/-- The throat itself is the zero-normal locus and is translated around the circle. -/
theorem normal_step_on_throat
    (period u : ℝ) :
    normalStep period (0, u) = (0, u + period) := by
  simp [normalStep]

/-- A locally positive side is carried to the locally negative side. -/
theorem positive_normal_is_sent_negative
    (period normal u : ℝ)
    (hPositive : 0 < normal) :
    (normalStep period (normal, u)).1 < 0 := by
  simp [normalStep]
  exact neg_neg_of_pos hPositive

/-- A locally negative side is carried to the locally positive side. -/
theorem negative_normal_is_sent_positive
    (period normal u : ℝ)
    (hNegative : normal < 0) :
    0 < (normalStep period (normal, u)).1 := by
  simp [normalStep]
  exact neg_pos.mpr hNegative

/-- Combinatorial side transition. -/
def sideTransition (side : Bool) : Bool := !side

/-- No local side label is invariant under one mapping-torus traversal. -/
theorem no_global_invariant_side
    (side : Bool) :
    sideTransition side ≠ side := by
  cases side <;> decide

/-- The doubled/orientation cover restores a side after two traversals. -/
@[simp] theorem side_transition_square
    (side : Bool) :
    sideTransition (sideTransition side) = side := by
  cases side <;> rfl

/-- The two local labels belong to one orbit under the gluing. -/
theorem both_local_sides_are_exchanged :
    sideTransition false = true /\
      sideTransition true = false := by
  decide

/--
This is the algebraic signature of a one-sided hypersurface: the normal line has
holonomy `-1` around the throat circle.  The two Janus layers are local sides of
one connected geometry, while the orientation double cover trivializes the
normal line after period `2T`.
-/
structure OneSidedThroatGeometryStatus where
  throatEmbeddedAsHypersurface : Prop
  normalLineBundleConstructed : Prop
  normalHolonomyMinusOneProved : Prop
  normalLineNontrivialProved : Prop
  complementConnectedProved : Prop
  orientationCoverNormalTrivialized : Prop
  layerExchangeIdentifiedWithNormalMonodromy : Prop
  bulkJunctionInterpretationDerived : Prop


def oneSidedThroatGeometryClosed
    (s : OneSidedThroatGeometryStatus) : Prop :=
  s.throatEmbeddedAsHypersurface /\
  s.normalLineBundleConstructed /\
  s.normalHolonomyMinusOneProved /\
  s.normalLineNontrivialProved /\
  s.complementConnectedProved /\
  s.orientationCoverNormalTrivialized /\
  s.layerExchangeIdentifiedWithNormalMonodromy /\
  s.bulkJunctionInterpretationDerived

end P0EFTJanusOneSidedThroatNormalMonodromy
end JanusFormal
