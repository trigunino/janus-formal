namespace JanusFormal
namespace P0EFTHolstPlasmaDeltaNeffDerivation

set_option autoImplicit false

structure HolstPlasmaDeltaNeffDerivation where
  deltaNeffTargetEncoded : Prop
  existingLockedConstantsTested : Prop
  closeExistingConstantCandidateFound : Prop
  candidatePromotedToDerivation : Prop
  earlyPlasmaConnectionTermDerived : Prop

def deltaNeffDerivationAttemptReady (d : HolstPlasmaDeltaNeffDerivation) : Prop :=
  d.deltaNeffTargetEncoded /\
  d.existingLockedConstantsTested /\
  d.closeExistingConstantCandidateFound

def deltaNeffNoFitReady (d : HolstPlasmaDeltaNeffDerivation) : Prop :=
  deltaNeffDerivationAttemptReady d /\
  d.candidatePromotedToDerivation /\
  d.earlyPlasmaConnectionTermDerived

theorem existing_constants_candidate_opens_plasma_route
    (d : HolstPlasmaDeltaNeffDerivation)
    (hTarget : d.deltaNeffTargetEncoded)
    (hTested : d.existingLockedConstantsTested)
    (hCandidate : d.closeExistingConstantCandidateFound) :
    deltaNeffDerivationAttemptReady d := by
  exact And.intro hTarget (And.intro hTested hCandidate)

theorem unpromoted_candidate_blocks_no_fit
    (d : HolstPlasmaDeltaNeffDerivation)
    (hMissing : Not d.candidatePromotedToDerivation) :
    Not (deltaNeffNoFitReady d) := by
  intro h
  exact hMissing h.right.left

theorem missing_early_plasma_term_blocks_no_fit
    (d : HolstPlasmaDeltaNeffDerivation)
    (hMissing : Not d.earlyPlasmaConnectionTermDerived) :
    Not (deltaNeffNoFitReady d) := by
  intro h
  exact hMissing h.right.right

end P0EFTHolstPlasmaDeltaNeffDerivation
end JanusFormal
