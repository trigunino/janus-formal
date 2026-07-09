import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4LineOfSightIntegratorTarget
import JanusFormal.Legacy.Z4.Gates.P0EFTJanusZ4WeylLensingIntegratorTarget

namespace JanusFormal
namespace P0EFTJanusZ4CMBSpectrumAssemblyTarget

set_option autoImplicit false

structure CMBSpectrumAssemblyTarget where
  ttSpectrumAssembled : Prop
  teSpectrumAssembled : Prop
  eeSpectrumAssembled : Prop
  ppSpectrumAssembled : Prop
  spectraFiniteAndExportable : Prop
  physicalTransferFunctionsUsed : Prop

def spectrumAssemblyReady (s : CMBSpectrumAssemblyTarget) : Prop :=
  s.ttSpectrumAssembled /\
  s.teSpectrumAssembled /\
  s.eeSpectrumAssembled /\
  s.ppSpectrumAssembled /\
  s.spectraFiniteAndExportable

def spectrumAssemblyPhysicalReady (s : CMBSpectrumAssemblyTarget) : Prop :=
  spectrumAssemblyReady s /\
  s.physicalTransferFunctionsUsed

theorem spectrum_assembly_requires_exportable_spectra
    (s : CMBSpectrumAssemblyTarget)
    (h : spectrumAssemblyReady s) :
    s.spectraFiniteAndExportable := by
  exact h.right.right.right.right

theorem spectrum_assembly_does_not_imply_physical_transfer
    (s : CMBSpectrumAssemblyTarget)
    (_h : spectrumAssemblyReady s)
    (hMissing : Not s.physicalTransferFunctionsUsed) :
    Not (spectrumAssemblyPhysicalReady s) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4CMBSpectrumAssemblyTarget
end JanusFormal
