import JanusFormal.P0EFTJanusZ2SigmaActiveCurvatureSignGate
import JanusFormal.P0EFTJanusZ2SigmaActiveOmegaKDerivationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundCurvatureBranchInputsAssemblerGate

set_option autoImplicit false

structure BackgroundCurvatureBranchInputsAssemblerGate where
  activeCoreZ2Sigma : Prop
  h0InputAvailable : Prop
  curvatureSignInputAvailable : Prop
  curvatureRadiusInputAvailable : Prop
  h0ActiveDerived : Prop
  curvatureSignActiveDerived : Prop
  curvatureRadiusActiveDerived : Prop
  noCompressedPlanckLCDMBackground : Prop
  noArchivedZ4Background : Prop
  noObservationalH0Fit : Prop
  noObservationalCurvatureFit : Prop
  curvatureBranchInputsWritten : Prop
  gatePassed : Prop
  h0WriterGateDeclared : Prop
  radiusWriterGateDeclared : Prop
  nearestBackgroundCurvatureBranchFrontierDeclared : Prop
  nearestBackgroundCurvatureBranchFrontierDiagnosticOnly : Prop

def curvatureBranchAssemblerPolicyClosed
    (g : BackgroundCurvatureBranchInputsAssemblerGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.h0InputAvailable /\
  g.curvatureSignInputAvailable /\
  g.curvatureRadiusInputAvailable /\
  g.h0ActiveDerived /\
  g.curvatureSignActiveDerived /\
  g.curvatureRadiusActiveDerived /\
  g.noCompressedPlanckLCDMBackground /\
  g.noArchivedZ4Background /\
  g.noObservationalH0Fit /\
  g.noObservationalCurvatureFit /\
  g.h0WriterGateDeclared /\
  g.radiusWriterGateDeclared /\
  g.nearestBackgroundCurvatureBranchFrontierDeclared /\
  g.nearestBackgroundCurvatureBranchFrontierDiagnosticOnly

theorem gate_pass_requires_curvature_branch_manifest
    (g : BackgroundCurvatureBranchInputsAssemblerGate)
    (_hGate : g.gatePassed)
    (hImplies : g.gatePassed -> g.curvatureBranchInputsWritten) :
    g.curvatureBranchInputsWritten := by
  exact hImplies _hGate

theorem assembler_requires_radius_input
    (g : BackgroundCurvatureBranchInputsAssemblerGate)
    (h : curvatureBranchAssemblerPolicyClosed g) :
    g.curvatureRadiusInputAvailable := by
  exact h.2.2.2.1

theorem assembler_requires_h0_input
    (g : BackgroundCurvatureBranchInputsAssemblerGate)
    (h : curvatureBranchAssemblerPolicyClosed g) :
    g.h0InputAvailable := by
  exact h.2.1

theorem nearest_background_frontier_diagnostic_does_not_write_branch
    (g : BackgroundCurvatureBranchInputsAssemblerGate)
    (_hDiag : g.nearestBackgroundCurvatureBranchFrontierDiagnosticOnly)
    (hNoH0 : Not g.h0InputAvailable) :
    Not (g.nearestBackgroundCurvatureBranchFrontierDiagnosticOnly /\
      curvatureBranchAssemblerPolicyClosed g) := by
  intro h
  exact hNoH0 h.2.2.1

end P0EFTJanusZ2SigmaBackgroundCurvatureBranchInputsAssemblerGate
end JanusFormal
