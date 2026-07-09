namespace JanusFormal
namespace P0EFTJanusZ2SigmaCurvatureChargeToSahaEarlyPlasmaPipelineGate

set_option autoImplicit false

structure CurvatureChargeToSahaEarlyPlasmaPipelineGate where
  activeCoreZ2TunnelSigma : Prop
  curvatureBranchValid : Prop
  projectedBaryonChargeValid : Prop
  spatialVolumeInputPassed : Prop
  spatialVolumePassed : Prop
  noetherVolumeToSahaEarlyPlasmaPassed : Prop
  compressedPlanckLCDMBackgroundUsed : Prop
  compressedPlanckLCDMRdUsed : Prop
  archivedZ4InputsUsed : Prop
  observationalH0FitUsed : Prop
  observationalCurvatureFitUsed : Prop
  gatePassed : Prop
  curvatureBranchAssemblerGateDeclared : Prop
  projectedBaryonChargeGateDeclared : Prop
  projectedBaryonChargeUpstreamFrontierDeclared : Prop
  spatialVolumeInputFrontierDeclared : Prop
  baryonDensityToPlasmaFrontierDeclared : Prop
  nearestCurvatureChargePlasmaFrontierDeclared : Prop
  nearestCurvatureChargePlasmaFrontierDiagnosticOnly : Prop

def noLegacyCurvatureChargePipelineInputs
    (g : CurvatureChargeToSahaEarlyPlasmaPipelineGate) : Prop :=
  Not g.compressedPlanckLCDMBackgroundUsed /\
  Not g.compressedPlanckLCDMRdUsed /\
  Not g.archivedZ4InputsUsed /\
  Not g.observationalH0FitUsed /\
  Not g.observationalCurvatureFitUsed

def curvatureChargeToPlasmaReady
    (g : CurvatureChargeToSahaEarlyPlasmaPipelineGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.curvatureBranchValid /\
  g.projectedBaryonChargeValid /\
  g.spatialVolumeInputPassed /\
  g.spatialVolumePassed /\
  g.noetherVolumeToSahaEarlyPlasmaPassed /\
  noLegacyCurvatureChargePipelineInputs g /\
  g.curvatureBranchAssemblerGateDeclared /\
  g.projectedBaryonChargeGateDeclared /\
  g.projectedBaryonChargeUpstreamFrontierDeclared /\
  g.spatialVolumeInputFrontierDeclared /\
  g.baryonDensityToPlasmaFrontierDeclared /\
  g.nearestCurvatureChargePlasmaFrontierDeclared /\
  g.nearestCurvatureChargePlasmaFrontierDiagnosticOnly

theorem gate_pass_requires_curvature_charge_to_plasma_chain
    (g : CurvatureChargeToSahaEarlyPlasmaPipelineGate)
    (hPass : g.gatePassed)
    (hImplies : g.gatePassed -> curvatureChargeToPlasmaReady g) :
    curvatureChargeToPlasmaReady g := by
  exact hImplies hPass

theorem curvature_charge_to_plasma_requires_projected_charge
    (g : CurvatureChargeToSahaEarlyPlasmaPipelineGate)
    (hReady : curvatureChargeToPlasmaReady g) :
    g.projectedBaryonChargeValid := by
  exact hReady.2.2.1

theorem nearest_curvature_charge_frontier_diagnostic_does_not_close_plasma
    (g : CurvatureChargeToSahaEarlyPlasmaPipelineGate)
    (_hDiag : g.nearestCurvatureChargePlasmaFrontierDiagnosticOnly)
    (hNoCharge : Not g.projectedBaryonChargeValid) :
    Not (g.nearestCurvatureChargePlasmaFrontierDiagnosticOnly /\
      curvatureChargeToPlasmaReady g) := by
  intro h
  exact hNoCharge h.2.2.2.1

theorem curvature_charge_to_plasma_requires_spatial_volume
    (g : CurvatureChargeToSahaEarlyPlasmaPipelineGate)
    (hReady : curvatureChargeToPlasmaReady g) :
    g.spatialVolumeInputPassed /\ g.spatialVolumePassed := by
  exact ⟨hReady.2.2.2.1, hReady.2.2.2.2.1⟩

end P0EFTJanusZ2SigmaCurvatureChargeToSahaEarlyPlasmaPipelineGate
end JanusFormal
