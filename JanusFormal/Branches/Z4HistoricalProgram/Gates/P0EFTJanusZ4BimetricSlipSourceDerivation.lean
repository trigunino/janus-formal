namespace JanusFormal
namespace P0EFTJanusZ4BimetricSlipSourceDerivation

set_option autoImplicit false

structure BimetricSlipSourceDerivation where
  slipRowsWritten : Prop
  derivativeJumpSlipSourceClosed : Prop
  slipSourceEquationDerived : Prop
  freeSlipParameter : Prop
  freeEtaRatio : Prop
  directClPatch : Prop
  rawToyLOS : Prop
  bianchiConsistencyGuard : Prop
  sourceLevelRegenerationRequired : Prop
  valueSlipTransportClosed : Prop
  boundaryGreenOrNormalModeRequired : Prop
  derivedSlipCandidateEnabled : Prop
  planckTrialAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def sourceEquationReady (g : BimetricSlipSourceDerivation) : Prop :=
  g.slipRowsWritten /\
  g.derivativeJumpSlipSourceClosed /\
  Not g.freeSlipParameter /\
  Not g.freeEtaRatio /\
  Not g.directClPatch /\
  Not g.rawToyLOS /\
  g.bianchiConsistencyGuard /\
  g.sourceLevelRegenerationRequired /\
  Not g.valueSlipTransportClosed /\
  g.boundaryGreenOrNormalModeRequired /\
  Not g.derivedSlipCandidateEnabled /\
  Not g.planckTrialAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem source_rows_derive_slip_source_but_not_candidate
    (g : BimetricSlipSourceDerivation)
    (hPolicy : sourceEquationReady g -> g.slipSourceEquationDerived)
    (h : sourceEquationReady g) :
    g.slipSourceEquationDerived := by
  exact hPolicy h

end P0EFTJanusZ4BimetricSlipSourceDerivation
end JanusFormal
