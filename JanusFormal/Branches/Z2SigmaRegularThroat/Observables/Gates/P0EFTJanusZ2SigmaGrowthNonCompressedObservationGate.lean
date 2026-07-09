import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaGrowthPerturbationEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaGrowthNonCompressedObservationGate

set_option autoImplicit false

structure Z2SigmaGrowthNonCompressedObservationGate where
  growthPerturbationEquationsDerived : Prop
  sdssEbossDirectFsigma8DataReady : Prop
  sdssEbossCovarianceReady : Prop
  archivedHolstGrowthReuseForbidden : Prop
  z2SigmaGrowthPredictionVectorReady : Prop
  chi2EvaluatedAgainstDirectFsigma8 : Prop
  growthNonCompressedGatePassed : Prop

def growthObservationPrerequisites
    (g : Z2SigmaGrowthNonCompressedObservationGate) : Prop :=
  g.growthPerturbationEquationsDerived /\
  g.sdssEbossDirectFsigma8DataReady /\
  g.sdssEbossCovarianceReady /\
  g.archivedHolstGrowthReuseForbidden

def growthObservationLockClosed
    (g : Z2SigmaGrowthNonCompressedObservationGate) : Prop :=
  growthObservationPrerequisites g /\
  g.z2SigmaGrowthPredictionVectorReady /\
  g.chi2EvaluatedAgainstDirectFsigma8

theorem growth_gate_requires_active_z2_sigma_prediction
    (g : Z2SigmaGrowthNonCompressedObservationGate)
    (hGate : g.growthNonCompressedGatePassed)
    (hImplies : g.growthNonCompressedGatePassed -> growthObservationLockClosed g) :
    growthObservationLockClosed g := by
  exact hImplies hGate

end P0EFTJanusZ2SigmaGrowthNonCompressedObservationGate
end JanusFormal
