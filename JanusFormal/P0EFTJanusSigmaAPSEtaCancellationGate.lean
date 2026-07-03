namespace JanusFormal
namespace P0EFTJanusSigmaAPSEtaCancellationGate

set_option autoImplicit false

structure SigmaAPSEtaCancellationGate where
  sigmaApsLocalThroatModelClosed : Prop
  sigmaDiracSpectrumPaired : Prop
  sigmaDiracKernelTrivial : Prop
  etaInvariantZero : Prop
  zeroModeDimensionZero : Prop
  etaPlusZeroModeContributionZero : Prop
  parityAnomalyCancellationGlobalClosed : Prop
  sigmaApsBoundaryPinLiftClosed : Prop

def sigmaEtaZeroModeCancellationClosed
    (g : SigmaAPSEtaCancellationGate) : Prop :=
  g.sigmaApsLocalThroatModelClosed /\
  g.sigmaDiracSpectrumPaired /\
  g.sigmaDiracKernelTrivial /\
  g.etaInvariantZero /\
  g.zeroModeDimensionZero /\
  g.etaPlusZeroModeContributionZero

def sigmaEtaClosedParityOpen
    (g : SigmaAPSEtaCancellationGate) : Prop :=
  sigmaEtaZeroModeCancellationClosed g /\
  Not g.parityAnomalyCancellationGlobalClosed /\
  Not g.sigmaApsBoundaryPinLiftClosed

theorem eta_zero_mode_package_does_not_close_parity_anomaly
    (g : SigmaAPSEtaCancellationGate)
    (h : sigmaEtaClosedParityOpen g) :
    Not g.parityAnomalyCancellationGlobalClosed := by
  exact h.2.1

theorem eta_zero_mode_package_does_not_close_full_aps_lift
    (g : SigmaAPSEtaCancellationGate)
    (h : sigmaEtaClosedParityOpen g) :
    Not g.sigmaApsBoundaryPinLiftClosed := by
  exact h.2.2

end P0EFTJanusSigmaAPSEtaCancellationGate
end JanusFormal
