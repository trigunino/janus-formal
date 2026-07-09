import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4WeylLensingSourceTarget

namespace JanusFormal
namespace P0EFTJanusZ4WeylLensingIntegratorTarget

set_option autoImplicit false

structure WeylLensingIntegratorTarget where
  weylPotentialDeclared : Prop
  lensingKernelDeclared : Prop
  finiteKernelIntegralProduced : Prop
  projectedZ4SlipInputUsed : Prop
  lensingProxySpectrumExported : Prop
  physicalPlanckLensingLikelihoodExecuted : Prop

def weylLensingIntegratorReady (w : WeylLensingIntegratorTarget) : Prop :=
  w.weylPotentialDeclared /\
  w.lensingKernelDeclared /\
  w.finiteKernelIntegralProduced /\
  w.projectedZ4SlipInputUsed /\
  w.lensingProxySpectrumExported

def weylLensingPhysicalReady (w : WeylLensingIntegratorTarget) : Prop :=
  weylLensingIntegratorReady w /\
  w.physicalPlanckLensingLikelihoodExecuted

theorem lensing_integrator_requires_finite_kernel
    (w : WeylLensingIntegratorTarget)
    (h : weylLensingIntegratorReady w) :
    w.finiteKernelIntegralProduced := by
  exact h.right.right.left

theorem lensing_integrator_does_not_execute_planck_lensing
    (w : WeylLensingIntegratorTarget)
    (_h : weylLensingIntegratorReady w)
    (hMissing : Not w.physicalPlanckLensingLikelihoodExecuted) :
    Not (weylLensingPhysicalReady w) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4WeylLensingIntegratorTarget
end JanusFormal
