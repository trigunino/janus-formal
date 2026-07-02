import JanusFormal.P0EFTJanusZ4MasterObservedFailureMapGate

namespace JanusFormal
namespace P0EFTJanusZ4MasterHighLAcousticRevisionScanGate

set_option autoImplicit false

structure MasterHighLAcousticRevisionScanGate where
  observedHighLAcousticFailure : Prop
  sharedUZ4NormalizationDeclared : Prop
  silkGuardDeclared : Prop
  revisionFound : Prop
  selectedRevisionIsUpstreamMaster : Prop
  carrierThresholdPassed : Prop
  highLReductionPassed : Prop
  keepsNontrivialSignal : Prop
  downstreamPatchAllowed : Prop
  observedPlanckRerunAllowed : Prop
  candidatePromotionAllowed : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def revisionScanReady (g : MasterHighLAcousticRevisionScanGate) : Prop :=
  g.observedHighLAcousticFailure /\
  g.sharedUZ4NormalizationDeclared /\
  g.silkGuardDeclared /\
  g.revisionFound /\
  g.selectedRevisionIsUpstreamMaster /\
  g.carrierThresholdPassed /\
  g.highLReductionPassed /\
  g.keepsNontrivialSignal /\
  Not g.downstreamPatchAllowed /\
  Not g.observedPlanckRerunAllowed /\
  Not g.candidatePromotionAllowed /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem revision_scan_is_upstream_not_planck_rerun
    (g : MasterHighLAcousticRevisionScanGate)
    (h : revisionScanReady g) :
    g.revisionFound /\ Not g.observedPlanckRerunAllowed := by
  rcases h with ⟨_, _, _, hFound, _, _, _, _, _, hRerun, _, _, _⟩
  exact ⟨hFound, hRerun⟩

end P0EFTJanusZ4MasterHighLAcousticRevisionScanGate
end JanusFormal
