import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaBAONonCompressedObservationGate
import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaNumericalBackgroundClosureGate
import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaBAONonFitMaterializationRunner

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAOActiveReadinessGate

set_option autoImplicit false

structure Z2SigmaBAOActiveReadinessGate where
  hZ2SigmaNumericalReady : Prop
  dmDhDvZ2SigmaReady : Prop
  csZ2SigmaReady : Prop
  zdZ2SigmaReady : Prop
  rdZ2SigmaEvaluated : Prop
  desiDR2GaussianBAODataReady : Prop
  desiDR2CovarianceReady : Prop
  strictHZ2SigmaBuilderReady : Prop
  strictEffectiveFluidAssemblerReady : Prop
  effectiveFluidAssemblerRequiresActiveFLRWComponents : Prop
  hBuilderRequiresActiveH0Z2Sigma : Prop
  hBuilderRequiresActiveRhoEffOverRhoCrit0 : Prop
  strictCsZ2SigmaBuilderReady : Prop
  csBuilderRequiresActiveBaryonDensity : Prop
  csBuilderRequiresActivePhotonDensity : Prop
  strictZdZ2SigmaSolverReady : Prop
  zdSolverRequiresActiveHZ2Sigma : Prop
  zdSolverRequiresActiveDragRate : Prop
  strictZ2SigmaBAOCalculatorReady : Prop
  strictZ2SigmaSoundRulerIntegratorReady : Prop
  calculatorRequiresActiveHZ2Sigma : Prop
  calculatorRequiresActiveRdZ2Sigma : Prop
  soundRulerIntegratorRequiresActiveCsZ2Sigma : Prop
  soundRulerIntegratorRequiresActiveZdZ2Sigma : Prop
  calculatorHasNoPlanckLCDMDefaults : Prop
  compressedPlanckLCDMRdForbidden : Prop
  planckLikeScaleForbidden : Prop
  archivedZ4BAOReuseForbidden : Prop
  nonfitMaterializationRunnerChecked : Prop
  nonfitMaterializationPassed : Prop
  nonfitMaterializationUsesNoPlanckLCDM : Prop
  nonfitMaterializationUsesNoArchivedZ4 : Prop
  baoPredictionVectorReady : Prop
  baoChi2Evaluated : Prop
  baoActiveReadinessGatePassed : Prop

def activeBAOInputsReady
    (g : Z2SigmaBAOActiveReadinessGate) : Prop :=
  g.hZ2SigmaNumericalReady /\
  g.dmDhDvZ2SigmaReady /\
  g.csZ2SigmaReady /\
  g.zdZ2SigmaReady /\
  g.rdZ2SigmaEvaluated

def directBAODataReady
    (g : Z2SigmaBAOActiveReadinessGate) : Prop :=
  g.desiDR2GaussianBAODataReady /\ g.desiDR2CovarianceReady

def strictBAOCalculatorReady
    (g : Z2SigmaBAOActiveReadinessGate) : Prop :=
  g.strictZ2SigmaBAOCalculatorReady /\
  g.strictHZ2SigmaBuilderReady /\
  g.strictEffectiveFluidAssemblerReady /\
  g.effectiveFluidAssemblerRequiresActiveFLRWComponents /\
  g.hBuilderRequiresActiveH0Z2Sigma /\
  g.hBuilderRequiresActiveRhoEffOverRhoCrit0 /\
  g.strictCsZ2SigmaBuilderReady /\
  g.csBuilderRequiresActiveBaryonDensity /\
  g.csBuilderRequiresActivePhotonDensity /\
  g.strictZdZ2SigmaSolverReady /\
  g.zdSolverRequiresActiveHZ2Sigma /\
  g.zdSolverRequiresActiveDragRate /\
  g.strictZ2SigmaSoundRulerIntegratorReady /\
  g.calculatorRequiresActiveHZ2Sigma /\
  g.calculatorRequiresActiveRdZ2Sigma /\
  g.soundRulerIntegratorRequiresActiveCsZ2Sigma /\
  g.soundRulerIntegratorRequiresActiveZdZ2Sigma /\
  g.calculatorHasNoPlanckLCDMDefaults

def activeBAOForbiddenReuseBlocked
    (g : Z2SigmaBAOActiveReadinessGate) : Prop :=
  g.compressedPlanckLCDMRdForbidden /\
  g.planckLikeScaleForbidden /\
  g.archivedZ4BAOReuseForbidden /\
  g.nonfitMaterializationRunnerChecked /\
  g.nonfitMaterializationUsesNoPlanckLCDM /\
  g.nonfitMaterializationUsesNoArchivedZ4

def activeBAOReadinessClosed
    (g : Z2SigmaBAOActiveReadinessGate) : Prop :=
  activeBAOInputsReady g /\
  directBAODataReady g /\
  strictBAOCalculatorReady g /\
  activeBAOForbiddenReuseBlocked g /\
  g.baoPredictionVectorReady /\
  g.baoChi2Evaluated

theorem bao_readiness_gate_requires_active_inputs
    (g : Z2SigmaBAOActiveReadinessGate)
    (hGate : g.baoActiveReadinessGatePassed)
    (hImplies : g.baoActiveReadinessGatePassed -> activeBAOReadinessClosed g) :
    activeBAOInputsReady g := by
  exact (hImplies hGate).1

theorem bao_chi2_requires_prediction_vector
    (g : Z2SigmaBAOActiveReadinessGate)
    (hClosed : activeBAOReadinessClosed g) :
    g.baoPredictionVectorReady := by
  exact hClosed.2.2.2.2.1

end P0EFTJanusZ2SigmaBAOActiveReadinessGate
end JanusFormal
