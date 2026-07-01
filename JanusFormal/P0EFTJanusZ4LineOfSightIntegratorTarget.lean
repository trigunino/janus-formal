import JanusFormal.P0EFTJanusZ4LineOfSightSourceTarget
import JanusFormal.P0EFTJanusZ4VisibilityNormalizationClosure

namespace JanusFormal
namespace P0EFTJanusZ4LineOfSightIntegratorTarget

set_option autoImplicit false

structure LineOfSightIntegratorTarget where
  sourceFunctionDeclared : Prop
  visibilitySourceInserted : Prop
  iswSourceInserted : Prop
  finiteIntegralProduced : Prop
  spectrumProxyExported : Prop
  physicalBoltzmannTransferExecuted : Prop

def losIntegratorReady (l : LineOfSightIntegratorTarget) : Prop :=
  l.sourceFunctionDeclared /\
  l.visibilitySourceInserted /\
  l.iswSourceInserted /\
  l.finiteIntegralProduced /\
  l.spectrumProxyExported

def losPhysicalTransferReady (l : LineOfSightIntegratorTarget) : Prop :=
  losIntegratorReady l /\
  l.physicalBoltzmannTransferExecuted

theorem los_integrator_requires_finite_integral
    (l : LineOfSightIntegratorTarget)
    (h : losIntegratorReady l) :
    l.finiteIntegralProduced := by
  exact h.right.right.right.left

theorem los_integrator_does_not_execute_physical_transfer
    (l : LineOfSightIntegratorTarget)
    (_h : losIntegratorReady l)
    (hMissing : Not l.physicalBoltzmannTransferExecuted) :
    Not (losPhysicalTransferReady l) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4LineOfSightIntegratorTarget
end JanusFormal
