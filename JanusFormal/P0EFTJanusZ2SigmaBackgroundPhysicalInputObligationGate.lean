namespace JanusFormal
namespace P0EFTJanusZ2SigmaBackgroundPhysicalInputObligationGate

set_option autoImplicit false

structure BackgroundPhysicalInputObligationGate where
  activeCoreZ2TunnelSigma : Prop
  h0Z2SigmaValid : Prop
  omegaKFromFLRWBranchValid : Prop
  gZ2SigmaValid : Prop
  omegaKFormulaReady : Prop
  requiresActiveH0ForEZ2Sigma : Prop
  requiresActiveFLRWComponentsForEZ2Sigma : Prop
  requiresActiveCurvatureBranchForOmegaK : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  archivedZ4BackgroundUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  mockInputsUsed : Prop
  gatePassed : Prop

def activeBackgroundInputsReady
    (g : BackgroundPhysicalInputObligationGate) : Prop :=
  g.h0Z2SigmaValid /\
  g.omegaKFromFLRWBranchValid /\
  g.gZ2SigmaValid

def backgroundPolicyClosed
    (g : BackgroundPhysicalInputObligationGate) : Prop :=
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.archivedZ4BackgroundUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed /\
  Not g.mockInputsUsed

theorem gate_requires_active_background_inputs
    (g : BackgroundPhysicalInputObligationGate)
    (hGate : g.gatePassed)
    (hImplies : g.gatePassed -> activeBackgroundInputsReady g) :
    activeBackgroundInputsReady g := by
  exact hImplies hGate

theorem omega_k_formula_needs_curvature_branch
    (g : BackgroundPhysicalInputObligationGate)
    (hReady : g.omegaKFormulaReady)
    (hImplies : g.omegaKFormulaReady -> g.requiresActiveCurvatureBranchForOmegaK) :
    g.requiresActiveCurvatureBranchForOmegaK := by
  exact hImplies hReady

theorem policy_forbids_background_legacy_inputs
    (g : BackgroundPhysicalInputObligationGate)
    (hPolicy : backgroundPolicyClosed g) :
    Not g.compressedPlanckLCDMBackgroundUsed /\
    Not g.archivedZ4BackgroundUsed /\
    Not g.observationalH0FitUsed /\
    Not g.observationalCurvatureFitUsed /\
    Not g.mockInputsUsed := by
  exact hPolicy

end P0EFTJanusZ2SigmaBackgroundPhysicalInputObligationGate
end JanusFormal
