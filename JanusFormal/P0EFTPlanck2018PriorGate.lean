namespace JanusFormal
namespace P0EFTPlanck2018PriorGate

set_option autoImplicit false

structure Planck2018PriorGate where
  planckLCDMDerivedOmegaMPriorLoaded : Prop
  holstOmegaMComputed : Prop
  lcdmDerivedOmegaMStressTestScored : Prop
  directJanusCMBLikelihood : Prop
  cmbTransferFunctionsDerived : Prop
  cmbSpectraComputed : Prop
  fullPlanckLikelihoodComputed : Prop

def lcdmDerivedOmegaMStressTestReady (g : Planck2018PriorGate) : Prop :=
  g.planckLCDMDerivedOmegaMPriorLoaded /\
  g.holstOmegaMComputed /\
  g.lcdmDerivedOmegaMStressTestScored

def fullPlanckGateReady (g : Planck2018PriorGate) : Prop :=
  lcdmDerivedOmegaMStressTestReady g /\
  g.directJanusCMBLikelihood /\
  g.cmbTransferFunctionsDerived /\
  g.cmbSpectraComputed /\
  g.fullPlanckLikelihoodComputed

theorem lcdm_derived_omega_m_closes_only_stress_test
    (g : Planck2018PriorGate)
    (hPrior : g.planckLCDMDerivedOmegaMPriorLoaded)
    (hModel : g.holstOmegaMComputed)
    (hScore : g.lcdmDerivedOmegaMStressTestScored) :
    lcdmDerivedOmegaMStressTestReady g := by
  exact And.intro hPrior (And.intro hModel hScore)

theorem stress_test_alone_does_not_imply_direct_planck_likelihood
    (g : Planck2018PriorGate)
    (_hStress : lcdmDerivedOmegaMStressTestReady g)
    (hMissing : Not g.directJanusCMBLikelihood) :
    Not (fullPlanckGateReady g) := by
  intro h
  exact hMissing h.right.left

theorem missing_cmb_transfer_functions_blocks_full_planck
    (g : Planck2018PriorGate)
    (hMissing : Not g.cmbTransferFunctionsDerived) :
    Not (fullPlanckGateReady g) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTPlanck2018PriorGate
end JanusFormal
