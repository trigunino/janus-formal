import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4UniqueEquationMasterGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterReconstructionGate

set_option autoImplicit false

structure MasterReconstructionGate where
  uniqueEquationMasterGatePassed : Prop
  phiPlusReconstructionDeclared : Prop
  psiPlusReconstructionDeclared : Prop
  phiMinusReconstructionDeclared : Prop
  psiMinusReconstructionDeclared : Prop
  plusFluidReconstructionDeclared : Prop
  minusFluidReconstructionDeclared : Prop
  theta0ReconstructionDeclared : Prop
  dopplerReconstructionDeclared : Prop
  piReconstructionDeclared : Prop
  weylReconstructionDeclared : Prop
  observableProjectionReconstructionDeclared : Prop
  missingMapsBlockedNotFree : Prop
  allMapsDerivedFromSameUZ4 : Prop
  independentDownstreamSourceAllowed : Prop
  freeReconstructionCoefficientAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def reconstructionGateReady (g : MasterReconstructionGate) : Prop :=
  g.uniqueEquationMasterGatePassed /\
  g.phiPlusReconstructionDeclared /\
  g.psiPlusReconstructionDeclared /\
  g.phiMinusReconstructionDeclared /\
  g.psiMinusReconstructionDeclared /\
  g.plusFluidReconstructionDeclared /\
  g.minusFluidReconstructionDeclared /\
  g.theta0ReconstructionDeclared /\
  g.dopplerReconstructionDeclared /\
  g.piReconstructionDeclared /\
  g.weylReconstructionDeclared /\
  g.observableProjectionReconstructionDeclared /\
  g.missingMapsBlockedNotFree /\
  Not g.allMapsDerivedFromSameUZ4 /\
  Not g.independentDownstreamSourceAllowed /\
  Not g.freeReconstructionCoefficientAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem master_reconstruction_blocks_free_maps
    (g : MasterReconstructionGate)
    (hPolicy : reconstructionGateReady g -> g.gatePassed)
    (h : reconstructionGateReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterReconstructionGate
end JanusFormal
