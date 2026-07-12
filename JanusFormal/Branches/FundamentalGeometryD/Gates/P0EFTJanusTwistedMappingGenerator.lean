import Mathlib

namespace JanusFormal
namespace P0EFTJanusTwistedMappingGenerator

set_option autoImplicit false

variable {X : Type*}

/-- Mapping-torus generator `(x,u) ↦ (rho x,u+T)`. -/
def twistedStep
    (rho : X → X) (period : ℝ) (p : X × ℝ) : X × ℝ :=
  (rho p.1, p.2 + period)

/-- Pure translation by the doubled period. -/
def doubleTranslation
    (period : ℝ) (p : X × ℝ) : X × ℝ :=
  (p.1, p.2 + 2 * period)

/-- If the fiber map is involutive, two twisted steps are pure translation by `2T`. -/
theorem twisted_step_square
    (rho : X → X)
    (period : ℝ)
    (hInvolutive : Function.Involutive rho)
    (p : X × ℝ) :
    twistedStep rho period (twistedStep rho period p) =
      doubleTranslation period p := by
  rcases p with ⟨x, u⟩
  simp [twistedStep, doubleTranslation, hInvolutive x]
  ring

/-- The square acts trivially on the geometric fiber. -/
theorem twisted_step_square_first_coordinate
    (rho : X → X)
    (period : ℝ)
    (hInvolutive : Function.Involutive rho)
    (p : X × ℝ) :
    (twistedStep rho period (twistedStep rho period p)).1 = p.1 := by
  rw [twisted_step_square rho period hInvolutive p]
  rfl

/-- The square advances the logarithmic coordinate by exactly `2T`. -/
theorem twisted_step_square_second_coordinate
    (rho : X → X)
    (period : ℝ)
    (hInvolutive : Function.Involutive rho)
    (p : X × ℝ) :
    (twistedStep rho period (twistedStep rho period p)).2 =
      p.2 + 2 * period := by
  rw [twisted_step_square rho period hInvolutive p]
  rfl

/-- Points fixed by `rho` form the candidate throat fiber. -/
def FixedBy (rho : X → X) (x : X) : Prop :=
  rho x = x

/-- On a fixed fiber point, one mapping-torus step is pure translation by `T`. -/
theorem twisted_step_on_fixed_point
    (rho : X → X)
    (period : ℝ)
    (x : X)
    (u : ℝ)
    (hFixed : FixedBy rho x) :
    twistedStep rho period (x, u) = (x, u + period) := by
  unfold FixedBy at hFixed
  simp [twistedStep, hFixed]

/--
The algebraic index-two cover is explicit: the original generator contains
`rho`, while its square is the untwisted period-`2T` translation. The remaining
geometric theorem is to form the corresponding quotients and prove that the
square-subgroup quotient is the orientation double cover.
-/
structure MappingTorusQuotientStatus where
  twistedIntegerActionConstructed : Prop
  actionProperlyDiscontinuous : Prop
  quotientTopologyConstructed : Prop
  squareSubgroupIndexTwoProved : Prop
  squareQuotientIdentifiedWithProductCircle : Prop
  orientationCharacterComputed : Prop
  deckInvolutionDerived : Prop


def orientationCoverConstructionClosed
    (s : MappingTorusQuotientStatus) : Prop :=
  s.twistedIntegerActionConstructed /\
  s.actionProperlyDiscontinuous /\
  s.quotientTopologyConstructed /\
  s.squareSubgroupIndexTwoProved /\
  s.squareQuotientIdentifiedWithProductCircle /\
  s.orientationCharacterComputed /\
  s.deckInvolutionDerived

end P0EFTJanusTwistedMappingGenerator
end JanusFormal
