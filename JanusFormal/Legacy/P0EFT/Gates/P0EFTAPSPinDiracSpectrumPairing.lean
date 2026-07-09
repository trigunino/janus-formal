import JanusFormal.Legacy.P0EFT.Gates.P0EFTAPSPinTraceGlobalDerivation

namespace JanusFormal
namespace P0EFTAPSPinDiracSpectrumPairing

set_option autoImplicit false

structure APSPinDiracSpectrumPairing where
  boundaryOperatorSelfAdjoint : Prop
  pinMinusPairingOperatorExists : Prop
  pairingOperatorAntiCommutesWithAAPS : Prop
  nonzeroSpectrumPairedBySign : Prop
  zeroModesVanishOrCancel : Prop

def spectralPairingClosed (s : APSPinDiracSpectrumPairing) : Prop :=
  s.boundaryOperatorSelfAdjoint /\
  s.pinMinusPairingOperatorExists /\
  s.pairingOperatorAntiCommutesWithAAPS /\
  s.nonzeroSpectrumPairedBySign

def etaRegularizationFixedByPairing (s : APSPinDiracSpectrumPairing) : Prop :=
  spectralPairingClosed s /\ s.zeroModesVanishOrCancel

theorem anticommuting_pin_operator_pairs_nonzero_spectrum
    (s : APSPinDiracSpectrumPairing)
    (hSelf : s.boundaryOperatorSelfAdjoint)
    (hJ : s.pinMinusPairingOperatorExists)
    (hAnti : s.pairingOperatorAntiCommutesWithAAPS)
    (hPairs : s.nonzeroSpectrumPairedBySign) :
    spectralPairingClosed s := by
  exact And.intro hSelf (And.intro hJ (And.intro hAnti hPairs))

theorem spectral_pairing_fixes_eta_zero_mode_cancellation
    (s : APSPinDiracSpectrumPairing)
    (hPairing : spectralPairingClosed s)
    (hZero : s.zeroModesVanishOrCancel) :
    etaRegularizationFixedByPairing s := by
  exact And.intro hPairing hZero

theorem missing_zero_mode_control_blocks_eta_regularization
    (s : APSPinDiracSpectrumPairing)
    (hMissing : Not s.zeroModesVanishOrCancel) :
    Not (etaRegularizationFixedByPairing s) := by
  intro h
  exact hMissing h.right

theorem spectral_pairing_supplies_global_index_eta_cancellation
    (s : APSPinDiracSpectrumPairing)
    (p : P0EFTAPSPinTraceGlobalDerivation.APSPinGlobalIndexPackage)
    (_hEta : etaRegularizationFixedByPairing s)
    (hBoundaryEta : p.boundaryEtaZeroModeCancellation)
    (hPin : p.pinMinusLiftSquaredMinusOne)
    (hAPS : p.apsBoundaryProjectorFredholm)
    (hParity : p.noParityAnomaly)
    (hTrace : p.traceRegularizationStandard) :
    P0EFTAPSPinTraceGlobalDerivation.apsPinIndexPackageClosed p := by
  unfold P0EFTAPSPinTraceGlobalDerivation.apsPinIndexPackageClosed
  exact And.intro hPin
    (And.intro hAPS
      (And.intro hBoundaryEta
        (And.intro hParity hTrace)))

end P0EFTAPSPinDiracSpectrumPairing
end JanusFormal
