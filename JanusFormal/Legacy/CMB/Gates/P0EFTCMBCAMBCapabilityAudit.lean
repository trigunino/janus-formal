namespace JanusFormal
namespace P0EFTCMBCAMBCapabilityAudit

set_option autoImplicit false

structure CAMBCapabilityAudit where
  pythonCAMBAvailable : Prop
  symbolicSourcesAvailable : Prop
  janusMuSigmaTablesAreTabulated : Prop
  stockCAMBAcceptsTabulatedMuSigma : Prop
  wrapperOrForkImplemented : Prop

def cambBackendAvailable (a : CAMBCapabilityAudit) : Prop :=
  a.pythonCAMBAvailable /\ a.symbolicSourcesAvailable

def janusCMBTransferReady (a : CAMBCapabilityAudit) : Prop :=
  cambBackendAvailable a /\
  a.janusMuSigmaTablesAreTabulated /\
  (a.stockCAMBAcceptsTabulatedMuSigma \/ a.wrapperOrForkImplemented)

theorem tabulated_mu_sigma_requires_wrapper_when_stock_camb_rejects
    (a : CAMBCapabilityAudit)
    (hReady : janusCMBTransferReady a)
    (hStockMissing : Not a.stockCAMBAcceptsTabulatedMuSigma) :
    a.wrapperOrForkImplemented := by
  exact Or.resolve_left hReady.right.right hStockMissing

theorem backend_available_from_python_and_symbolic
    (a : CAMBCapabilityAudit)
    (hPython : a.pythonCAMBAvailable)
    (hSymbolic : a.symbolicSourcesAvailable) :
    cambBackendAvailable a := by
  exact And.intro hPython hSymbolic

end P0EFTCMBCAMBCapabilityAudit
end JanusFormal
