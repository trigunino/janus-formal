import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTAPSPinTraceGlobalDerivation
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTAPSPinDiracSpectrumPairing
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTAPSPinDiracKernelTrivialization

namespace JanusFormal
namespace P0EFTAPSPinGlobalIndexClosure

set_option autoImplicit false

structure APSPinGlobalIndexClosure where
  spectrumPairingClosed : Prop
  kernelTrivialized : Prop
  noParityAnomaly : Prop
  traceRegularizationStandard : Prop

def apsGlobalIndexClosed (c : APSPinGlobalIndexClosure) : Prop :=
  c.spectrumPairingClosed /\
  c.kernelTrivialized /\
  c.noParityAnomaly /\
  c.traceRegularizationStandard

theorem aps_global_index_closure_supplies_index_package
    (c : APSPinGlobalIndexClosure)
    (p : P0EFTAPSPinTraceGlobalDerivation.APSPinGlobalIndexPackage)
    (_hClosed : apsGlobalIndexClosed c)
    (hPin : p.pinMinusLiftSquaredMinusOne)
    (hAPS : p.apsBoundaryProjectorFredholm)
    (hEta : p.boundaryEtaZeroModeCancellation)
    (hParity : p.noParityAnomaly)
    (hTrace : p.traceRegularizationStandard) :
    P0EFTAPSPinTraceGlobalDerivation.apsPinIndexPackageClosed p := by
  unfold P0EFTAPSPinTraceGlobalDerivation.apsPinIndexPackageClosed
  exact And.intro hPin
    (And.intro hAPS
      (And.intro hEta (And.intro hParity hTrace)))

theorem missing_spectrum_pairing_blocks_aps_global_index
    (c : APSPinGlobalIndexClosure)
    (hMissing : Not c.spectrumPairingClosed) :
    Not (apsGlobalIndexClosed c) := by
  intro h
  exact hMissing h.left

end P0EFTAPSPinGlobalIndexClosure
end JanusFormal
