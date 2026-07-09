namespace JanusFormal
namespace P0EFTJanusSigmaAPSParityAnomalyCancellationGate

set_option autoImplicit false

structure SigmaAPSParityAnomalyCancellationGate where
  sigmaEtaZeroModeCancellationClosed : Prop
  z2TunnelPairingDeclared : Prop
  pairedBoundaryOrientationReversalDeclared : Prop
  pairedDiracDeterminantPhaseOpposite : Prop
  parityAnomalyContributionsCancelPairwise : Prop
  parityAnomalyCancellationGlobalClosed : Prop
  sigmaApsBoundaryPinLiftClosed : Prop

def sigmaParityAnomalyCancellationClosed
    (g : SigmaAPSParityAnomalyCancellationGate) : Prop :=
  g.sigmaEtaZeroModeCancellationClosed /\
  g.z2TunnelPairingDeclared /\
  g.pairedBoundaryOrientationReversalDeclared /\
  g.pairedDiracDeterminantPhaseOpposite /\
  g.parityAnomalyContributionsCancelPairwise /\
  g.parityAnomalyCancellationGlobalClosed

def sigmaApsPinLiftClosed
    (g : SigmaAPSParityAnomalyCancellationGate) : Prop :=
  sigmaParityAnomalyCancellationClosed g /\
  g.sigmaApsBoundaryPinLiftClosed

theorem parity_cancellation_closes_sigma_aps_pin_lift
    (g : SigmaAPSParityAnomalyCancellationGate)
    (h : sigmaApsPinLiftClosed g) :
    g.sigmaApsBoundaryPinLiftClosed := by
  exact h.2

theorem parity_cancellation_requires_z2_tunnel_pairing
    (g : SigmaAPSParityAnomalyCancellationGate)
    (h : sigmaParityAnomalyCancellationClosed g) :
    g.z2TunnelPairingDeclared /\ g.parityAnomalyContributionsCancelPairwise := by
  rcases h with ⟨_, hPairing, _, _, hCancel, _⟩
  exact And.intro hPairing hCancel

end P0EFTJanusSigmaAPSParityAnomalyCancellationGate
end JanusFormal
