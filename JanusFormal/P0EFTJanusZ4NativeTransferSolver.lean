import JanusFormal.P0EFTJanusZ4PlanckAdapterReadyClosure

namespace JanusFormal
namespace P0EFTJanusZ4NativeTransferSolver

set_option autoImplicit false

structure NativeTransferSolver where
  kGridDeclared : Prop
  ellGridDeclared : Prop
  denseLensingEllGridUsed : Prop
  sphericalBesselProjectionUsed : Prop
  visibilityWeightedSourcesUsed : Prop
  coupledPhotonBaryonSourcesUsed : Prop
  dedicatedWeylLensingSourceUsed : Prop
  cmbLensingPhiKernelUsed : Prop
  ppMedianCalibrationTargetUsed : Prop
  tightCouplingPolarizationSourceUsed : Prop
  spin2EModeProjectionUsed : Prop
  silkDampingUsed : Prop
  finiteRecombinationWidthUsed : Prop
  primordialPowerIntegrated : Prop
  finiteTTTEEEPPProduced : Prop
  noLegacyCAMBForkRequired : Prop
  officialPlanckLikelihoodExecuted : Prop

def nativeTransferSolverReady (s : NativeTransferSolver) : Prop :=
  s.kGridDeclared /\
  s.ellGridDeclared /\
  s.denseLensingEllGridUsed /\
  s.sphericalBesselProjectionUsed /\
  s.visibilityWeightedSourcesUsed /\
  s.coupledPhotonBaryonSourcesUsed /\
  s.dedicatedWeylLensingSourceUsed /\
  s.cmbLensingPhiKernelUsed /\
  s.ppMedianCalibrationTargetUsed /\
  s.tightCouplingPolarizationSourceUsed /\
  s.spin2EModeProjectionUsed /\
  s.silkDampingUsed /\
  s.finiteRecombinationWidthUsed /\
  s.primordialPowerIntegrated /\
  s.finiteTTTEEEPPProduced /\
  s.noLegacyCAMBForkRequired

def nativeTransferPlanckReady (s : NativeTransferSolver) : Prop :=
  nativeTransferSolverReady s /\
  s.officialPlanckLikelihoodExecuted

theorem native_transfer_produces_finite_spectra
    (s : NativeTransferSolver)
    (h : nativeTransferSolverReady s) :
    s.finiteTTTEEEPPProduced := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hFinite, _⟩
  exact hFinite

theorem native_transfer_does_not_claim_planck
    (s : NativeTransferSolver)
    (_h : nativeTransferSolverReady s)
    (hMissing : Not s.officialPlanckLikelihoodExecuted) :
    Not (nativeTransferPlanckReady s) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4NativeTransferSolver
end JanusFormal
