namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOScaleFreeFormulationGate

set_option autoImplicit false

structure BAOScaleFreeFormulationGate where
  activeCoreZ2TunnelSigma : Prop
  eZ2SigmaInputDeclared : Prop
  csOverCInputDeclared : Prop
  zdZ2SigmaInputDeclared : Prop
  rdHatDefinedAsH0RdOverC : Prop
  dimensionlessEBuilderReady : Prop
  dimensionlessDragRatioBuilderReady : Prop
  scaleFreeZdSolverReady : Prop
  dimensionalBAOEquivalencePassed : Prop
  observationalH0FitUsed : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4ReuseUsed : Prop
  officialBAOEvaluation : Prop
  officialBAOGateUnblocked : Prop
  gatePassed : Prop

def scaleFreeContractClosed
    (g : BAOScaleFreeFormulationGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.eZ2SigmaInputDeclared /\
  g.csOverCInputDeclared /\
  g.zdZ2SigmaInputDeclared /\
  g.rdHatDefinedAsH0RdOverC /\
  g.dimensionlessEBuilderReady /\
  g.dimensionlessDragRatioBuilderReady /\
  g.scaleFreeZdSolverReady /\
  g.dimensionalBAOEquivalencePassed /\
  ¬ g.observationalH0FitUsed /\
  ¬ g.compressedPlanckLCDMRdUsed /\
  ¬ g.archivedZ4ReuseUsed /\
  ¬ g.officialBAOEvaluation /\
  ¬ g.officialBAOGateUnblocked

theorem scale_free_gate_does_not_unblock_official_bao
    (g : BAOScaleFreeFormulationGate)
    (hClosed : scaleFreeContractClosed g) :
    ¬ g.officialBAOGateUnblocked := by
  rcases hClosed with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hBlocked⟩
  exact hBlocked

theorem scale_free_gate_forbids_observational_H0_fit
    (g : BAOScaleFreeFormulationGate)
    (hClosed : scaleFreeContractClosed g) :
    ¬ g.observationalH0FitUsed := by
  rcases hClosed with ⟨_, _, _, _, _, _, _, _, _, hNoH0Fit, _, _, _, _⟩
  exact hNoH0Fit

end P0EFTJanusZ2SigmaBAOScaleFreeFormulationGate
end JanusFormal
