import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaCMBBoltzmannEquationGate
import JanusFormal.Branches.Z2SigmaRegularThroat.Observables.Gates.P0EFTJanusZ2SigmaObservationalRoadmapGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaNonCompressedObservationGate

set_option autoImplicit false

structure Z2SigmaNonCompressedObservationGate where
  observationEquationLocksClosed : Prop
  growthNonCompressedGatePassed : Prop
  baoNonCompressedGatePassed : Prop
  cmbNonCompressedGatePassed : Prop
  compressedLCDMValidationForbidden : Prop
  nonCompressedObservationGatesPassed : Prop
  fullCosmologyPredictionReadyNoFit : Prop

def nonCompressedObservationLocksClosed
    (g : Z2SigmaNonCompressedObservationGate) : Prop :=
  g.observationEquationLocksClosed /\
  g.growthNonCompressedGatePassed /\
  g.baoNonCompressedGatePassed /\
  g.cmbNonCompressedGatePassed /\
  g.compressedLCDMValidationForbidden

theorem no_fit_requires_non_compressed_observations
    (g : Z2SigmaNonCompressedObservationGate)
    (hNoFit : g.fullCosmologyPredictionReadyNoFit)
    (hImplies : g.fullCosmologyPredictionReadyNoFit -> nonCompressedObservationLocksClosed g) :
    nonCompressedObservationLocksClosed g := by
  exact hImplies hNoFit

end P0EFTJanusZ2SigmaNonCompressedObservationGate
end JanusFormal
