import JanusFormal.Legacy.P0EFT.Gates.P0EFTRadionPotentialDerivation

namespace JanusFormal
namespace P0EFTRadionAmplitudeClosure

set_option autoImplicit false

structure RadionAmplitudeClosure where
  backgroundEquationEncoded : Prop
  lambdaJSolvedAlgebraically : Prop
  nonzeroAsymptoticRadionRequired : Prop
  chiInfinityFixedByJanusBackground : Prop
  rhoDSResidualFixed : Prop
  lambdaJFixedNoFit : Prop
  potentialFullyFixedNoFit : Prop
  jbgStationarySourceDerived : Prop

def lambdaJReducedToBackgroundData (a : RadionAmplitudeClosure) : Prop :=
  a.backgroundEquationEncoded /\
  a.lambdaJSolvedAlgebraically /\
  a.nonzeroAsymptoticRadionRequired

def lambdaJClosedNoFit (a : RadionAmplitudeClosure) : Prop :=
  lambdaJReducedToBackgroundData a /\
  a.chiInfinityFixedByJanusBackground /\
  a.rhoDSResidualFixed /\
  a.lambdaJFixedNoFit

def potentialAmplitudeFullyClosed (a : RadionAmplitudeClosure) : Prop :=
  lambdaJClosedNoFit a /\ a.jbgStationarySourceDerived /\ a.potentialFullyFixedNoFit

theorem background_equation_reduces_lambdaJ_to_branch_data
    (a : RadionAmplitudeClosure)
    (hEq : a.backgroundEquationEncoded)
    (hSolve : a.lambdaJSolvedAlgebraically)
    (hNonzero : a.nonzeroAsymptoticRadionRequired) :
    lambdaJReducedToBackgroundData a := by
  exact And.intro hEq (And.intro hSolve hNonzero)

theorem missing_chi_infinity_blocks_no_fit_amplitude
    (a : RadionAmplitudeClosure)
    (hMissing : Not a.chiInfinityFixedByJanusBackground) :
    Not (lambdaJClosedNoFit a) := by
  intro h
  exact hMissing h.right.left

theorem missing_dS_residual_blocks_no_fit_amplitude
    (a : RadionAmplitudeClosure)
    (hMissing : Not a.rhoDSResidualFixed) :
    Not (lambdaJClosedNoFit a) := by
  intro h
  exact hMissing h.right.right.left

theorem amplitude_closes_after_background_data
    (a : RadionAmplitudeClosure)
    (hReduced : lambdaJReducedToBackgroundData a)
    (hChi : a.chiInfinityFixedByJanusBackground)
    (hRho : a.rhoDSResidualFixed)
    (hLambda : a.lambdaJFixedNoFit) :
    lambdaJClosedNoFit a := by
  exact And.intro hReduced (And.intro hChi (And.intro hRho hLambda))

theorem potential_fully_closes_after_amplitude
    (a : RadionAmplitudeClosure)
    (hAmp : lambdaJClosedNoFit a)
    (hJ : a.jbgStationarySourceDerived)
    (hFull : a.potentialFullyFixedNoFit) :
    potentialAmplitudeFullyClosed a := by
  exact And.intro hAmp (And.intro hJ hFull)

end P0EFTRadionAmplitudeClosure
end JanusFormal
