import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTAPSPinGlobalIndexClosure
import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTAPSPinTraceGlobalDerivation

namespace JanusFormal
namespace P0EFTJanusZ4APSIndexPackageObligationGate

set_option autoImplicit false

structure APSIndexPackageObligationGate where
  spectralPairingInterfaceAvailable : Prop
  kernelTrivializationInterfaceAvailable : Prop
  pinMinusLiftSquaredMinusOne : Prop
  apsBoundaryProjectorFredholm : Prop
  etaZeroModeCancellationGlobal : Prop
  noParityAnomalyGlobal : Prop
  traceRegularizationStandardGlobal : Prop
  apsIndexPackageClosed : Prop

def apsLocalInterfacesReady (g : APSIndexPackageObligationGate) : Prop :=
  g.spectralPairingInterfaceAvailable /\
  g.kernelTrivializationInterfaceAvailable

def apsGlobalAtomicObligationsClosed
    (g : APSIndexPackageObligationGate) : Prop :=
  apsLocalInterfacesReady g /\
  g.pinMinusLiftSquaredMinusOne /\
  g.apsBoundaryProjectorFredholm /\
  g.etaZeroModeCancellationGlobal /\
  g.noParityAnomalyGlobal /\
  g.traceRegularizationStandardGlobal

theorem missing_pin_lift_blocks_aps_index_package
    (g : APSIndexPackageObligationGate)
    (hMissing : Not g.pinMinusLiftSquaredMinusOne) :
    Not (apsGlobalAtomicObligationsClosed g) := by
  intro h
  exact hMissing h.right.left

theorem aps_atomic_obligations_transport_to_index_package
    (g : APSIndexPackageObligationGate)
    (h : apsGlobalAtomicObligationsClosed g)
    (hTransport :
      apsGlobalAtomicObligationsClosed g -> g.apsIndexPackageClosed) :
    g.apsIndexPackageClosed := by
  exact hTransport h

end P0EFTJanusZ4APSIndexPackageObligationGate
end JanusFormal
