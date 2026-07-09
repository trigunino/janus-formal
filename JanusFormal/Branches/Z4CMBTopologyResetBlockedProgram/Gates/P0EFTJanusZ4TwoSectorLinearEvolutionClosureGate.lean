import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4TwoSectorInitialModeGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorLinearEvolutionClosureGate

set_option autoImplicit false

structure TwoSectorLinearEvolutionClosureGate where
  initialModeGatePassed : Prop
  stateVectorDeclared : Prop
  linearEvolutionOperatorDeclared : Prop
  plusFluidRowsEvolved : Prop
  minusFluidRowsEvolved : Prop
  plusMetricConstraintsEvolved : Prop
  minusMetricConstraintsEvolved : Prop
  projectionRowsEvolved : Prop
  couplingMatrixEntersOperator : Prop
  exchangeTermsRespectBianchiGate : Prop
  constraintPreservationGuard : Prop
  superhorizonRegularEvolutionGuard : Prop
  grLimitEvolutionRecovered : Prop
  hiddenSectorNotForcedToPlus : Prop
  rhoEffShortcutForbidden : Prop
  directClPatchForbidden : Prop
  rawToyLOSForbidden : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  eigenmodeStabilityRequiredNext : Prop
  sourceLevelRegenerationAllowed : Prop
  carrierTangentProjectionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def linearEvolutionReady (g : TwoSectorLinearEvolutionClosureGate) : Prop :=
  g.initialModeGatePassed /\
  g.stateVectorDeclared /\
  g.linearEvolutionOperatorDeclared /\
  g.plusFluidRowsEvolved /\
  g.minusFluidRowsEvolved /\
  g.plusMetricConstraintsEvolved /\
  g.minusMetricConstraintsEvolved /\
  g.projectionRowsEvolved /\
  g.couplingMatrixEntersOperator /\
  g.exchangeTermsRespectBianchiGate /\
  g.constraintPreservationGuard /\
  g.superhorizonRegularEvolutionGuard /\
  g.grLimitEvolutionRecovered /\
  g.hiddenSectorNotForcedToPlus /\
  g.rhoEffShortcutForbidden /\
  g.directClPatchForbidden /\
  g.rawToyLOSForbidden /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  g.eigenmodeStabilityRequiredNext /\
  Not g.sourceLevelRegenerationAllowed /\
  Not g.carrierTangentProjectionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem linear_evolution_closure_blocks_spectra_until_stability
    (g : TwoSectorLinearEvolutionClosureGate)
    (hPolicy : linearEvolutionReady g -> g.gatePassed)
    (h : linearEvolutionReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorLinearEvolutionClosureGate
end JanusFormal
