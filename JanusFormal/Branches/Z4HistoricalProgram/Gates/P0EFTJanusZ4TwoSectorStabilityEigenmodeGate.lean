import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4TwoSectorLinearEvolutionClosureGate

namespace JanusFormal
namespace P0EFTJanusZ4TwoSectorStabilityEigenmodeGate

set_option autoImplicit false

structure TwoSectorStabilityEigenmodeGate where
  linearEvolutionGatePassed : Prop
  eigenvaluesFinite : Prop
  noExplosiveRealModes : Prop
  superhorizonKRegular : Prop
  subhorizonKRegular : Prop
  symmetricModeStable : Prop
  antisymmetricZ4ModeStable : Prop
  relativeIsocurvatureModeStable : Prop
  projectionModeStable : Prop
  ghostTachyonGuard : Prop
  constraintPreservationGuard : Prop
  grLimitStabilityRecovered : Prop
  sourceLevelRegenerationAllowed : Prop
  spectraGenerationAllowed : Prop
  planckTrialAllowed : Prop
  carrierTangentProjectionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop
  gatePassed : Prop

def stabilityReady (g : TwoSectorStabilityEigenmodeGate) : Prop :=
  g.linearEvolutionGatePassed /\
  g.eigenvaluesFinite /\
  g.noExplosiveRealModes /\
  g.superhorizonKRegular /\
  g.subhorizonKRegular /\
  g.symmetricModeStable /\
  g.antisymmetricZ4ModeStable /\
  g.relativeIsocurvatureModeStable /\
  g.projectionModeStable /\
  g.ghostTachyonGuard /\
  g.constraintPreservationGuard /\
  g.grLimitStabilityRecovered /\
  g.sourceLevelRegenerationAllowed /\
  Not g.spectraGenerationAllowed /\
  Not g.planckTrialAllowed /\
  Not g.carrierTangentProjectionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem stability_gate_allows_source_regeneration_only
    (g : TwoSectorStabilityEigenmodeGate)
    (hPolicy : stabilityReady g -> g.gatePassed)
    (h : stabilityReady g) :
    g.gatePassed := by
  exact hPolicy h

end P0EFTJanusZ4TwoSectorStabilityEigenmodeGate
end JanusFormal
