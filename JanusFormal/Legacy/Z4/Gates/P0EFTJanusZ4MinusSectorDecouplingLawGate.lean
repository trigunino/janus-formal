import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MinusSectorThermalRatioGate

namespace JanusFormal
namespace P0EFTJanusZ4MinusSectorDecouplingLawGate

set_option autoImplicit false

structure MinusSectorDecouplingLawGate where
  thermalRatioGateCompleted : Prop
  thermalRatioDiagnosticOnly : Prop
  minusRecombinationSolverRequired : Prop
  conservationBianchiRequired : Prop
  fullActionOrMicrophysicalDerivationRequired : Prop
  minusDecouplingLawDeclared : Prop
  minusVisibilityFunctionDeclared : Prop
  minusDragEpochDeclared : Prop
  minusOpacityHistoryDeclared : Prop
  freeDecouplingShiftAllowed : Prop
  freeVisibilityPatchAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def decouplingBlockedReady (g : MinusSectorDecouplingLawGate) : Prop :=
  g.thermalRatioGateCompleted /\
  g.thermalRatioDiagnosticOnly /\
  g.minusRecombinationSolverRequired /\
  g.conservationBianchiRequired /\
  g.fullActionOrMicrophysicalDerivationRequired /\
  Not g.minusDecouplingLawDeclared /\
  Not g.minusVisibilityFunctionDeclared /\
  Not g.minusDragEpochDeclared /\
  Not g.minusOpacityHistoryDeclared /\
  Not g.freeDecouplingShiftAllowed /\
  Not g.freeVisibilityPatchAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem decoupling_law_gate_blocks_shortcuts
    (g : MinusSectorDecouplingLawGate)
    (hPolicy : decouplingBlockedReady g -> g.gatePassed)
    (h : decouplingBlockedReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MinusSectorDecouplingLawGate
end JanusFormal
