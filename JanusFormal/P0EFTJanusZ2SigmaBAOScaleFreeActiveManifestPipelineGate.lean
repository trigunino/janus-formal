namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOScaleFreeActiveManifestPipelineGate

set_option autoImplicit false

structure BAOScaleFreeActiveManifestPipelineGate where
  activeCoreZ2TunnelSigma : Prop
  componentManifestAvailable : Prop
  pipelineExecuted : Prop
  scaleFreeBAOInputManifestWritten : Prop
  observationalH0FitUsed : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  gatePassed : Prop

def scaleFreePipelineClosed
    (g : BAOScaleFreeActiveManifestPipelineGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.componentManifestAvailable /\
  g.pipelineExecuted /\
  g.scaleFreeBAOInputManifestWritten /\
  ¬ g.observationalH0FitUsed /\
  ¬ g.compressedPlanckLCDMUsed /\
  ¬ g.archivedZ4Used /\
  g.gatePassed

theorem scale_free_pipeline_forbids_H0_fit_and_archived_Z4
    (g : BAOScaleFreeActiveManifestPipelineGate)
    (hClosed : scaleFreePipelineClosed g) :
    ¬ g.observationalH0FitUsed ∧ ¬ g.archivedZ4Used := by
  rcases hClosed with ⟨_, _, _, _, hNoH0, _, hNoZ4, _⟩
  exact ⟨hNoH0, hNoZ4⟩

end P0EFTJanusZ2SigmaBAOScaleFreeActiveManifestPipelineGate
end JanusFormal
