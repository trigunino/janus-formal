import JanusFormal.P0EFTJanusZ2SigmaBAOSoundRulerGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaBAONonCompressedObservationGate

set_option autoImplicit false

structure Z2SigmaBAONonCompressedObservationGate where
  photonDistanceMapDerived : Prop
  baoSoundRulerFormulaReady : Prop
  baoSoundRulerEvaluated : Prop
  desiDR2GaussianBAODataReady : Prop
  desiDR2CovarianceReady : Prop
  compressedLCDMPlanckRdForbidden : Prop
  archivedHolstBAOReuseForbidden : Prop
  z2SigmaBAOPredictionVectorReady : Prop
  chi2EvaluatedAgainstDESIBAOCovariance : Prop
  baoNonCompressedGatePassed : Prop

def baoObservationPrerequisites
    (g : Z2SigmaBAONonCompressedObservationGate) : Prop :=
  g.photonDistanceMapDerived /\
  g.baoSoundRulerFormulaReady /\
  g.desiDR2GaussianBAODataReady /\
  g.desiDR2CovarianceReady /\
  g.compressedLCDMPlanckRdForbidden /\
  g.archivedHolstBAOReuseForbidden

def baoObservationLockClosed
    (g : Z2SigmaBAONonCompressedObservationGate) : Prop :=
  baoObservationPrerequisites g /\
  g.baoSoundRulerEvaluated /\
  g.z2SigmaBAOPredictionVectorReady /\
  g.chi2EvaluatedAgainstDESIBAOCovariance

theorem bao_gate_requires_active_z2_sigma_prediction
    (g : Z2SigmaBAONonCompressedObservationGate)
    (hGate : g.baoNonCompressedGatePassed)
    (hImplies : g.baoNonCompressedGatePassed -> baoObservationLockClosed g) :
    baoObservationLockClosed g := by
  exact hImplies hGate

end P0EFTJanusZ2SigmaBAONonCompressedObservationGate
end JanusFormal
