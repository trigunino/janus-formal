import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldHolonomyFluxQuantization

namespace JanusFormal
namespace P0EFTOrbifoldFluxIntegerTheorem

set_option autoImplicit false

structure OrbifoldFluxIntegerTheorem where
  singularCycleDefined : Prop
  normalizedSpinConnectionFluxDefined : Prop
  integerFluxLawProved : Prop
  janusOrientationSelectsPositiveDoubleCover : Prop
  mirrorOrientationSelectsNegativeSingleCover : Prop

def integerFluxDataClosed (t : OrbifoldFluxIntegerTheorem) : Prop :=
  t.singularCycleDefined /\
  t.normalizedSpinConnectionFluxDefined /\
  t.integerFluxLawProved

def janusBranchIndicesForced (t : OrbifoldFluxIntegerTheorem) : Prop :=
  integerFluxDataClosed t /\
  t.janusOrientationSelectsPositiveDoubleCover /\
  t.mirrorOrientationSelectsNegativeSingleCover

theorem integer_flux_and_orientation_force_branch_indices
    (t : OrbifoldFluxIntegerTheorem)
    (q : P0EFTOrbifoldHolonomyFluxQuantization.OrbifoldHolonomyFluxQuantization)
    (_hForced : janusBranchIndicesForced t)
    (hCycle : q.singularCycleAroundSigmaDefined)
    (hFlux : q.spinConnectionFluxIntegralDefined)
    (hQuantized : q.fluxQuantizationConditionLoaded)
    (hPositive : q.branchIndexPositiveComputedAsTwo)
    (hNegative : q.branchIndexNegativeComputedAsOne) :
    P0EFTOrbifoldHolonomyFluxQuantization.branchIndicesComputed q := by
  unfold P0EFTOrbifoldHolonomyFluxQuantization.branchIndicesComputed
  unfold P0EFTOrbifoldHolonomyFluxQuantization.holonomyFluxQuantized
  exact And.intro
    (And.intro hCycle (And.intro hFlux hQuantized))
    (And.intro hPositive hNegative)

theorem missing_integer_flux_law_blocks_forced_indices
    (t : OrbifoldFluxIntegerTheorem)
    (hMissing : Not t.integerFluxLawProved) :
    Not (janusBranchIndicesForced t) := by
  intro h
  exact hMissing h.left.right.right

theorem missing_positive_orientation_blocks_forced_indices
    (t : OrbifoldFluxIntegerTheorem)
    (hMissing : Not t.janusOrientationSelectsPositiveDoubleCover) :
    Not (janusBranchIndicesForced t) := by
  intro h
  exact hMissing h.right.left

end P0EFTOrbifoldFluxIntegerTheorem
end JanusFormal
