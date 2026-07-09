import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4MasterConstraintConsistencyGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterToObservableMapGate

set_option autoImplicit false

structure MasterToObservableMapGate where
  masterConstraintConsistencyGatePassed : Prop
  observableFunctionalsDeclared : Prop
  temperatureSourceFromUZ4 : Prop
  polarizationSourceFromUZ4 : Prop
  lensingSourceFromUZ4 : Prop
  dopplerFromUZ4 : Prop
  theta0FromUZ4 : Prop
  piFromUZ4 : Prop
  slipFromUZ4 : Prop
  minusSectorFromUZ4 : Prop
  allObservableMapsDerivedFromSameUZ4 : Prop
  independentTemperaturePatchAllowed : Prop
  independentPolarizationPatchAllowed : Prop
  independentLensingPatchAllowed : Prop
  independentDopplerPatchAllowed : Prop
  independentPiPatchAllowed : Prop
  independentMinusSectorAmplitudeAllowed : Prop
  rhoEffShortcutAllowed : Prop
  directClPatchAllowed : Prop
  rawToyLOSAllowed : Prop
  planckTrialAllowed : Prop
  spectraGenerationAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def observableMapReady (g : MasterToObservableMapGate) : Prop :=
  g.masterConstraintConsistencyGatePassed /\
  g.observableFunctionalsDeclared /\
  g.temperatureSourceFromUZ4 /\
  g.polarizationSourceFromUZ4 /\
  g.lensingSourceFromUZ4 /\
  g.dopplerFromUZ4 /\
  g.theta0FromUZ4 /\
  g.piFromUZ4 /\
  g.slipFromUZ4 /\
  g.minusSectorFromUZ4 /\
  g.allObservableMapsDerivedFromSameUZ4 /\
  Not g.independentTemperaturePatchAllowed /\
  Not g.independentPolarizationPatchAllowed /\
  Not g.independentLensingPatchAllowed /\
  Not g.independentDopplerPatchAllowed /\
  Not g.independentPiPatchAllowed /\
  Not g.independentMinusSectorAmplitudeAllowed /\
  Not g.rhoEffShortcutAllowed /\
  Not g.directClPatchAllowed /\
  Not g.rawToyLOSAllowed /\
  Not g.planckTrialAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem master_to_observable_map_blocks_patchwork
    (g : MasterToObservableMapGate)
    (hPolicy : observableMapReady g -> g.gatePassed)
    (h : observableMapReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4MasterToObservableMapGate
end JanusFormal
