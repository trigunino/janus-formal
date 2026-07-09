namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOComponentToChi2DryRunGate

set_option autoImplicit false

structure Z2SigmaBAOComponentToChi2DryRunGate where
  componentManifestWriterExercised : Prop
  activeManifestPipelineExercised : Prop
  officialChi2CalculatorExercised : Prop
  dryRunOnly : Prop
  officialBAOEvaluation : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4ReuseUsed : Prop

def dryRunPathReady
    (g : Z2SigmaBAOComponentToChi2DryRunGate) : Prop :=
  g.componentManifestWriterExercised /\
  g.activeManifestPipelineExercised /\
  g.officialChi2CalculatorExercised /\
  g.dryRunOnly /\
  Not g.officialBAOEvaluation /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4ReuseUsed

theorem dry_run_is_not_official_evaluation
    (g : Z2SigmaBAOComponentToChi2DryRunGate)
    (hReady : dryRunPathReady g) :
    Not g.officialBAOEvaluation := by
  exact hReady.2.2.2.2.1

end P0EFTJanusZ2SigmaBAOComponentToChi2DryRunGate
end JanusFormal
