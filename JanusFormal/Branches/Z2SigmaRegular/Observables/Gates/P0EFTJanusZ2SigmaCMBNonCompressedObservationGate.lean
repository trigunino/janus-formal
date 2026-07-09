import JanusFormal.Branches.Z2SigmaRegular.Observables.Gates.P0EFTJanusZ2SigmaCMBBoltzmannEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCMBNonCompressedObservationGate

set_option autoImplicit false

structure Z2SigmaCMBNonCompressedObservationGate where
  cmbBoltzmannEquationsDerived : Prop
  planckLowLCommanderAvailable : Prop
  planckLowESimAllAvailable : Prop
  planckHighLTTTEEEAvailable : Prop
  planckLensingAvailable : Prop
  compressedLCDMPlanckPriorsForbidden : Prop
  archivedZ4CMBSpectraReuseForbidden : Prop
  z2SigmaCMBTheorySpectraReady : Prop
  planckLikelihoodEvaluatedOnZ2SigmaSpectra : Prop
  cmbNonCompressedGatePassed : Prop

def cmbObservationPrerequisites
    (g : Z2SigmaCMBNonCompressedObservationGate) : Prop :=
  g.cmbBoltzmannEquationsDerived /\
  g.planckLowLCommanderAvailable /\
  g.planckLowESimAllAvailable /\
  g.planckHighLTTTEEEAvailable /\
  g.planckLensingAvailable /\
  g.compressedLCDMPlanckPriorsForbidden /\
  g.archivedZ4CMBSpectraReuseForbidden

def cmbObservationLockClosed
    (g : Z2SigmaCMBNonCompressedObservationGate) : Prop :=
  cmbObservationPrerequisites g /\
  g.z2SigmaCMBTheorySpectraReady /\
  g.planckLikelihoodEvaluatedOnZ2SigmaSpectra

theorem cmb_gate_requires_active_z2_sigma_spectra
    (g : Z2SigmaCMBNonCompressedObservationGate)
    (hGate : g.cmbNonCompressedGatePassed)
    (hImplies : g.cmbNonCompressedGatePassed -> cmbObservationLockClosed g) :
    cmbObservationLockClosed g := by
  exact hImplies hGate

end P0EFTJanusZ2SigmaCMBNonCompressedObservationGate
end JanusFormal
