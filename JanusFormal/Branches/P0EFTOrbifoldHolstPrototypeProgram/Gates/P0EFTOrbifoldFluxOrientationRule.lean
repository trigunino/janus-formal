import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldFluxIntegerTheorem

namespace JanusFormal
namespace P0EFTOrbifoldFluxOrientationRule

set_option autoImplicit false

structure OrbifoldFluxOrientationRule where
  janusNormalOrientationFixed : Prop
  mirrorNormalOrientationFixed : Prop
  positiveFluxSectorHasMultiplicityTwo : Prop
  negativeFluxSectorHasMultiplicityOne : Prop

def orientationRuleClosed (r : OrbifoldFluxOrientationRule) : Prop :=
  r.janusNormalOrientationFixed /\
  r.mirrorNormalOrientationFixed /\
  r.positiveFluxSectorHasMultiplicityTwo /\
  r.negativeFluxSectorHasMultiplicityOne

theorem orientation_rule_supplies_janus_cover_selection
    (r : OrbifoldFluxOrientationRule)
    (t : P0EFTOrbifoldFluxIntegerTheorem.OrbifoldFluxIntegerTheorem)
    (_hRule : orientationRuleClosed r)
    (hCycle : t.singularCycleDefined)
    (hFlux : t.normalizedSpinConnectionFluxDefined)
    (hInteger : t.integerFluxLawProved)
    (hPositive : t.janusOrientationSelectsPositiveDoubleCover)
    (hNegative : t.mirrorOrientationSelectsNegativeSingleCover) :
    P0EFTOrbifoldFluxIntegerTheorem.janusBranchIndicesForced t := by
  unfold P0EFTOrbifoldFluxIntegerTheorem.janusBranchIndicesForced
  unfold P0EFTOrbifoldFluxIntegerTheorem.integerFluxDataClosed
  exact And.intro
    (And.intro hCycle (And.intro hFlux hInteger))
    (And.intro hPositive hNegative)

theorem missing_positive_flux_sector_blocks_orientation_rule
    (r : OrbifoldFluxOrientationRule)
    (hMissing : Not r.positiveFluxSectorHasMultiplicityTwo) :
    Not (orientationRuleClosed r) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_mirror_orientation_blocks_orientation_rule
    (r : OrbifoldFluxOrientationRule)
    (hMissing : Not r.mirrorNormalOrientationFixed) :
    Not (orientationRuleClosed r) := by
  intro h
  exact hMissing h.right.left

end P0EFTOrbifoldFluxOrientationRule
end JanusFormal
