import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PostClosurePlanckDecomposition
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4PolarizationHierarchyClosure

namespace JanusFormal
namespace P0EFTJanusZ4AcousticPolarizationPhaseKernel

set_option autoImplicit false

structure AcousticPolarizationPhaseKernel where
  monopoleVariableIsolated : Prop
  dopplerVariableIsolated : Prop
  quadrupoleVariableIsolated : Prop
  eModeVariableIsolated : Prop
  z4FreePolarizationSourceRemoved : Prop
  tePhaseKernelDeclared : Prop
  tightCouplingQuadrupoleIdentityDerived : Prop
  solverNumericsModified : Prop
  planckValidationClaimed : Prop

def phaseKernelScaffoldReady (k : AcousticPolarizationPhaseKernel) : Prop :=
  k.monopoleVariableIsolated /\
  k.dopplerVariableIsolated /\
  k.quadrupoleVariableIsolated /\
  k.eModeVariableIsolated /\
  k.z4FreePolarizationSourceRemoved /\
  k.tePhaseKernelDeclared

def phaseKernelPhysicalReady (k : AcousticPolarizationPhaseKernel) : Prop :=
  phaseKernelScaffoldReady k /\ k.tightCouplingQuadrupoleIdentityDerived

theorem phase_kernel_scaffold_does_not_close_physics
    (k : AcousticPolarizationPhaseKernel)
    (_h : phaseKernelScaffoldReady k)
    (hMissing : Not k.tightCouplingQuadrupoleIdentityDerived) :
    Not (phaseKernelPhysicalReady k) := by
  intro h
  exact hMissing h.right

theorem phase_kernel_keeps_solver_frozen
    (k : AcousticPolarizationPhaseKernel)
    (_h : phaseKernelScaffoldReady k)
    (hFrozen : Not k.solverNumericsModified) :
    Not k.solverNumericsModified := by
  exact hFrozen

theorem phase_kernel_does_not_claim_planck
    (k : AcousticPolarizationPhaseKernel)
    (_h : phaseKernelScaffoldReady k)
    (hNoClaim : Not k.planckValidationClaimed) :
    Not k.planckValidationClaimed := by
  exact hNoClaim

end P0EFTJanusZ4AcousticPolarizationPhaseKernel
end JanusFormal
