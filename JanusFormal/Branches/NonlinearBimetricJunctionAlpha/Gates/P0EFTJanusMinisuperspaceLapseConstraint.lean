import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusReciprocalBimetricPotential

namespace JanusFormal
namespace P0EFTJanusMinisuperspaceLapseConstraint

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential

/-- Coefficient multiplying the plus lapse on a diagonal FLRW branch. -/
def plusLapseCoefficient (b : PotentialCoefficients) (r : ℝ) : ℝ :=
  b.beta0 + 3 * b.beta1 * r + 3 * b.beta2 * r ^ 2 + b.beta3 * r ^ 3

/-- Coefficient multiplying the minus lapse on the same branch. -/
def minusLapseCoefficient (b : PotentialCoefficients) (r : ℝ) : ℝ :=
  b.beta1 + 3 * b.beta2 * r + 3 * b.beta3 * r ^ 2 + b.beta4 * r ^ 3

/-- HR interaction density after multiplying by the plus-sector volume lapse. -/
def lapseLinearInteraction
    (b : PotentialCoefficients) (r lapsePlus lapseMinus : ℝ) : ℝ :=
  lapsePlus * plusLapseCoefficient b r +
    lapseMinus * minusLapseCoefficient b r

/-- Exact reconstruction from the elementary-symmetric polynomial expansion. -/
theorem elementary_polynomial_density_is_lapse_linear
    (b : PotentialCoefficients) (r lapsePlus lapseMinus : ℝ)
    (hLapse : lapsePlus ≠ 0) :
    lapsePlus *
        (b.beta0 + b.beta1 * (lapseMinus / lapsePlus + 3 * r) +
          b.beta2 * (3 * (lapseMinus / lapsePlus) * r + 3 * r ^ 2) +
          b.beta3 * (3 * (lapseMinus / lapsePlus) * r ^ 2 + r ^ 3) +
          b.beta4 * (lapseMinus / lapsePlus) * r ^ 3) =
      lapseLinearInteraction b r lapsePlus lapseMinus := by
  unfold lapseLinearInteraction plusLapseCoefficient minusLapseCoefficient
  field_simp [hLapse]
  ring

/-- Finite first variation with respect to the plus lapse is lapse-independent. -/
theorem plus_lapse_variation_is_constraint
    (b : PotentialCoefficients) (r lapsePlus lapseMinus increment : ℝ) :
    lapseLinearInteraction b r (lapsePlus + increment) lapseMinus -
        lapseLinearInteraction b r lapsePlus lapseMinus =
      increment * plusLapseCoefficient b r := by
  unfold lapseLinearInteraction
  ring

/-- Finite first variation with respect to the minus lapse is lapse-independent. -/
theorem minus_lapse_variation_is_constraint
    (b : PotentialCoefficients) (r lapsePlus lapseMinus increment : ℝ) :
    lapseLinearInteraction b r lapsePlus (lapseMinus + increment) -
        lapseLinearInteraction b r lapsePlus lapseMinus =
      increment * minusLapseCoefficient b r := by
  unfold lapseLinearInteraction
  ring

/-- The pure lapse Hessian vanishes exactly. -/
theorem lapse_second_variations_vanish
    (b : PotentialCoefficients) (r lapsePlus lapseMinus increment₁ increment₂ : ℝ) :
    (lapseLinearInteraction b r (lapsePlus + increment₁ + increment₂) lapseMinus -
        lapseLinearInteraction b r (lapsePlus + increment₁) lapseMinus) -
      (lapseLinearInteraction b r (lapsePlus + increment₂) lapseMinus -
        lapseLinearInteraction b r lapsePlus lapseMinus) = 0 := by
  unfold lapseLinearInteraction
  ring

/-- Linear lapse dependence supplies primary constraints, not their secondary closure. -/
structure LapseConstraintClosureStatus where
  admShiftRedefinitionDerived : Prop
  interactionLinearInBothLapses : Prop
  primaryHamiltonianConstraintsDerived : Prop
  poissonBracketComputed : Prop
  secondaryConstraintDerived : Prop
  boulwareDeserModeRemoved : Prop

def lapseConstraintClosed (s : LapseConstraintClosureStatus) : Prop :=
  s.admShiftRedefinitionDerived ∧
  s.interactionLinearInBothLapses ∧
  s.primaryHamiltonianConstraintsDerived ∧
  s.poissonBracketComputed ∧
  s.secondaryConstraintDerived ∧
  s.boulwareDeserModeRemoved

/-- Lapse linearity alone is logically insufficient to close the secondary gate. -/
theorem lapse_linearity_does_not_imply_secondary_constraint :
    ∃ s : LapseConstraintClosureStatus,
      s.interactionLinearInBothLapses ∧
      s.primaryHamiltonianConstraintsDerived ∧
      ¬s.secondaryConstraintDerived ∧
      ¬lapseConstraintClosed s := by
  let s : LapseConstraintClosureStatus :=
    { admShiftRedefinitionDerived := True
      interactionLinearInBothLapses := True
      primaryHamiltonianConstraintsDerived := True
      poissonBracketComputed := False
      secondaryConstraintDerived := False
      boulwareDeserModeRemoved := False }
  refine ⟨s, trivial, trivial, ?_, ?_⟩
  · exact id
  · intro hClosed
    exact hClosed.2.2.2.2.1

end P0EFTJanusMinisuperspaceLapseConstraint
end JanusFormal
