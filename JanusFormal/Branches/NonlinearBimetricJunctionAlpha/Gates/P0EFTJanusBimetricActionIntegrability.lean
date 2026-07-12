import Mathlib

namespace JanusFormal
namespace P0EFTJanusBimetricActionIntegrability

set_option autoImplicit false

/-- Linearized cross sources for two reduced metric degrees of freedom. -/
structure LinearCrossSources where
  plusSelf : ℝ
  plusFromMinus : ℝ
  minusFromPlus : ℝ
  minusSelf : ℝ


def plusSource (s : LinearCrossSources) (x y : ℝ) : ℝ :=
  s.plusSelf * x + s.plusFromMinus * y


def minusSource (s : LinearCrossSources) (x y : ℝ) : ℝ :=
  s.minusFromPlus * x + s.minusSelf * y

/-- Work along a small rectangle, varying the plus degree first. -/
def workPlusThenMinus
    (s : LinearCrossSources)
    (x y dx dy : ℝ) : ℝ :=
  plusSource s x y * dx + minusSource s (x + dx) y * dy

/-- Work along the same rectangle, varying the minus degree first. -/
def workMinusThenPlus
    (s : LinearCrossSources)
    (x y dx dy : ℝ) : ℝ :=
  minusSource s x y * dy + plusSource s x (y + dy) * dx

/-- The rectangular path defect is exactly the cross-coefficient mismatch. -/
theorem rectangular_path_defect
    (s : LinearCrossSources)
    (x y dx dy : ℝ) :
    workPlusThenMinus s x y dx dy -
        workMinusThenPlus s x y dx dy =
      (s.minusFromPlus - s.plusFromMinus) * dx * dy := by
  unfold workPlusThenMinus workMinusThenPlus plusSource minusSource
  ring

/-- A single common action requires reciprocity of the two cross variations. -/
theorem path_independence_requires_cross_reciprocity
    (s : LinearCrossSources)
    (hPathIndependent :
      ∀ x y dx dy,
        workPlusThenMinus s x y dx dy =
          workMinusThenPlus s x y dx dy) :
    s.plusFromMinus = s.minusFromPlus := by
  have h := hPathIndependent 0 0 1 1
  have hDefect := rectangular_path_defect s 0 0 1 1
  rw [h] at hDefect
  norm_num at hDefect
  linarith

/-- Reciprocity is sufficient for rectangular path independence in the linear model. -/
theorem cross_reciprocity_implies_path_independence
    (s : LinearCrossSources)
    (hReciprocity : s.plusFromMinus = s.minusFromPlus) :
    ∀ x y dx dy,
      workPlusThenMinus s x y dx dy =
        workMinusThenPlus s x y dx dy := by
  intro x y dx dy
  have hDefect := rectangular_path_defect s x y dx dy
  rw [hReciprocity] at hDefect
  norm_num at hDefect
  linarith

/--
The nonlinear analogue is the closedness of the interaction one-form in field
space.  The 2024 Janus notation uses two interaction functionals; a complete
action must prove that their variations satisfy this common-potential
integrability condition rather than choose them independently.
-/
structure NonlinearInteractionIntegrabilityStatus where
  commonFieldSpaceDefined : Prop
  plusInteractionVariationDerived : Prop
  minusInteractionVariationDerived : Prop
  mixedVariationSymmetryProved : Prop
  commonInteractionFunctionalConstructed : Prop
  diagonalDiffeomorphismNoetherIdentityProved : Prop
  determinantWeightConventionDerived : Prop
  nonlinearReciprocityProved : Prop


def nonlinearInteractionIntegrable
    (s : NonlinearInteractionIntegrabilityStatus) : Prop :=
  s.commonFieldSpaceDefined /\
  s.plusInteractionVariationDerived /\
  s.minusInteractionVariationDerived /\
  s.mixedVariationSymmetryProved /\
  s.commonInteractionFunctionalConstructed /\
  s.diagonalDiffeomorphismNoetherIdentityProved /\
  s.determinantWeightConventionDerived /\
  s.nonlinearReciprocityProved

end P0EFTJanusBimetricActionIntegrability
end JanusFormal
