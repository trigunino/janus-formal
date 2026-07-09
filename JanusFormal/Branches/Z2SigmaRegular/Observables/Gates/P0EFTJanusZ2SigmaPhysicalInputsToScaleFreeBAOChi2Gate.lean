namespace JanusFormal
namespace P0EFTJanusZ2SigmaPhysicalInputsToScaleFreeBAOChi2Gate

set_option autoImplicit false

structure PhysicalInputsToScaleFreeBAOChi2Gate where
  activeCoreZ2TunnelSigma : Prop
  backgroundPipelinePassed : Prop
  curvatureChargeSahaPlasmaPipelinePassed : Prop
  plasmaPrimitivePassed : Prop
  splitPrimitivesChi2Passed : Prop
  baoChi2Evaluated : Prop
  compressedPlanckLCDMUsed : Prop
  archivedZ4Used : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop
  backgroundFrontierDeclared : Prop
  curvatureChargePlasmaFrontierDeclared : Prop
  plasmaPrimitiveFrontierDeclared : Prop
  plasmaPrimitiveInputFrontiersDeclared : Prop
  nearestPlasmaPrimitiveFrontierDeclared : Prop
  nearestPhysicalInputsFrontierDeclared : Prop
  nearestPhysicalInputsFrontierDiagnosticOnly : Prop
  physicalFrontierSummaryDeclared : Prop

def noLegacyObservationInputs
    (g : PhysicalInputsToScaleFreeBAOChi2Gate) : Prop :=
  Not g.compressedPlanckLCDMUsed /\
  Not g.archivedZ4Used /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed

def physicalInputsToDESIChi2Ready
    (g : PhysicalInputsToScaleFreeBAOChi2Gate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.backgroundPipelinePassed /\
  g.curvatureChargeSahaPlasmaPipelinePassed /\
  g.plasmaPrimitivePassed /\
  g.splitPrimitivesChi2Passed /\
  g.baoChi2Evaluated /\
  noLegacyObservationInputs g /\
  g.backgroundFrontierDeclared /\
  g.curvatureChargePlasmaFrontierDeclared /\
  g.plasmaPrimitiveFrontierDeclared /\
  g.plasmaPrimitiveInputFrontiersDeclared /\
  g.nearestPlasmaPrimitiveFrontierDeclared /\
  g.nearestPhysicalInputsFrontierDeclared /\
  g.nearestPhysicalInputsFrontierDiagnosticOnly /\
  g.physicalFrontierSummaryDeclared

theorem gate_pass_requires_physical_inputs_to_desi_chi2_chain
    (g : PhysicalInputsToScaleFreeBAOChi2Gate)
    (hPass : g.gatePassed)
    (hImplies : g.gatePassed -> physicalInputsToDESIChi2Ready g) :
    physicalInputsToDESIChi2Ready g := by
  exact hImplies hPass

theorem physical_inputs_require_background_pipeline
    (g : PhysicalInputsToScaleFreeBAOChi2Gate)
    (hReady : physicalInputsToDESIChi2Ready g) :
    g.backgroundPipelinePassed := by
  exact hReady.2.1

theorem nearest_physical_inputs_frontier_diagnostic_does_not_evaluate_chi2
    (g : PhysicalInputsToScaleFreeBAOChi2Gate)
    (_hDiag : g.nearestPhysicalInputsFrontierDiagnosticOnly)
    (hNoBackground : Not g.backgroundPipelinePassed) :
    Not (g.nearestPhysicalInputsFrontierDiagnosticOnly /\
      physicalInputsToDESIChi2Ready g) := by
  intro h
  exact hNoBackground h.2.2.1

theorem plasma_primitive_frontier_diagnostic_is_not_bao_chi2
    (g : PhysicalInputsToScaleFreeBAOChi2Gate)
    (_hPlasmaPrimitiveFrontier : g.nearestPlasmaPrimitiveFrontierDeclared)
    (hNoPlasmaPrimitive : Not g.plasmaPrimitivePassed) :
    Not (g.nearestPlasmaPrimitiveFrontierDeclared /\
      physicalInputsToDESIChi2Ready g) := by
  intro h
  exact hNoPlasmaPrimitive h.2.2.2.2.1

end P0EFTJanusZ2SigmaPhysicalInputsToScaleFreeBAOChi2Gate
end JanusFormal
