import JanusFormal.Branches.JanusPTPhaseTransition.Gates.P0EFTJanusPT02LandauMinima

namespace JanusFormal
namespace P0EFTJanusPT03ScaleNoGo

set_option autoImplicit false

/-- Broken-phase order-parameter scale squared. -/
noncomputable def brokenScaleSquared (a b : ℝ) : ℝ := -a / (2 * b)

theorem common_coefficient_rescaling_changes_broken_scale
    (a b lambda : ℝ) (hB : b ≠ 0) :
    brokenScaleSquared (lambda ^ 2 * a) b =
      lambda ^ 2 * brokenScaleSquared a b := by
  unfold brokenScaleSquared
  field_simp

/-- PT fixes parity but not the coefficient ratio that sets the nonzero
minimum. -/
structure PT0103Status where
  orderParameterDerivedFromP : Prop
  ptParityDerived : Prop
  evenInvariantBasisClassified : Prop
  quadraticCoefficientDerived : Prop
  quarticCoefficientDerived : Prop
  renormalizedPotentialDerived : Prop
  physicalTemperatureLawDerived : Prop

def conditionalLandauCoreClosed (s : PT0103Status) : Prop :=
  s.ptParityDerived ∧ s.evenInvariantBasisClassified

def physicalPhaseDiagramClosed (s : PT0103Status) : Prop :=
  conditionalLandauCoreClosed s ∧
  s.orderParameterDerivedFromP ∧
  s.quadraticCoefficientDerived ∧
  s.quarticCoefficientDerived ∧
  s.renormalizedPotentialDerived ∧
  s.physicalTemperatureLawDerived

theorem missing_quadratic_coefficient_blocks_scale_selection
    (s : PT0103Status)
    (hMissing : ¬s.quadraticCoefficientDerived) :
    ¬physicalPhaseDiagramClosed s := by
  intro hClosed
  exact hMissing hClosed.2.2.1

end P0EFTJanusPT03ScaleNoGo
end JanusFormal
