namespace JanusFormal
namespace P0EFTJanusZ2SigmaDiracCurrentParityFromSpinorIntertwinerGate

set_option autoImplicit false

structure DiracCurrentParityFromSpinorIntertwinerGate where
  pinCliffordCovarianceBibliographyChecked : Prop
  diracCurrentBilinearDeclared : Prop
  spinorIntertwinerConditionDeclared : Prop
  cliffordIntertwiningConditionDeclared : Prop
  diracAdjointCompatibilityDeclared : Prop
  observationalFitForbidden : Prop
  currentBilinearFormulaReady : Prop
  intertwinerImpliesGammaTransportFormulaReady : Prop
  intertwinerImpliesCurrentTransportConditional : Prop
  plusMinusSpinorBundleDataReady : Prop
  z2SpinorIntertwinerFromResolvedTunnelPinLiftReady : Prop
  cliffordIntertwiningVerified : Prop
  diracAdjointCompatibilityVerified : Prop
  physicalSpinorEquivarianceFromBoundaryVariationReady : Prop
  physicalSpinorEquivarianceFromQuotientDescentReady : Prop
  diracCurrentZ2ParityDerived : Prop

def physicalSpinorEquivarianceReady
    (g : DiracCurrentParityFromSpinorIntertwinerGate) : Prop :=
  g.physicalSpinorEquivarianceFromBoundaryVariationReady \/
  g.physicalSpinorEquivarianceFromQuotientDescentReady

def conditionalCurrentParityAlgebraReady
    (g : DiracCurrentParityFromSpinorIntertwinerGate) : Prop :=
  g.pinCliffordCovarianceBibliographyChecked /\
  g.diracCurrentBilinearDeclared /\
  g.spinorIntertwinerConditionDeclared /\
  g.cliffordIntertwiningConditionDeclared /\
  g.diracAdjointCompatibilityDeclared /\
  g.observationalFitForbidden /\
  g.currentBilinearFormulaReady /\
  g.intertwinerImpliesGammaTransportFormulaReady /\
  g.intertwinerImpliesCurrentTransportConditional

def diracCurrentZ2ParityReady
    (g : DiracCurrentParityFromSpinorIntertwinerGate) : Prop :=
  conditionalCurrentParityAlgebraReady g /\
  g.plusMinusSpinorBundleDataReady /\
  g.z2SpinorIntertwinerFromResolvedTunnelPinLiftReady /\
  g.cliffordIntertwiningVerified /\
  g.diracAdjointCompatibilityVerified /\
  physicalSpinorEquivarianceReady g /\
  g.diracCurrentZ2ParityDerived

theorem current_parity_requires_z2_spinor_intertwiner
    (g : DiracCurrentParityFromSpinorIntertwinerGate)
    (h : diracCurrentZ2ParityReady g) :
    g.z2SpinorIntertwinerFromResolvedTunnelPinLiftReady := by
  exact h.2.2.1

theorem current_parity_requires_boundary_variation_equivariance
    (g : DiracCurrentParityFromSpinorIntertwinerGate)
    (h : diracCurrentZ2ParityReady g) :
    physicalSpinorEquivarianceReady g := by
  exact h.2.2.2.2.2.1

theorem conditional_algebra_does_not_close_global_parity
    (g : DiracCurrentParityFromSpinorIntertwinerGate)
    (_h : conditionalCurrentParityAlgebraReady g)
    (hMissing : Not g.z2SpinorIntertwinerFromResolvedTunnelPinLiftReady) :
    Not (diracCurrentZ2ParityReady g) := by
  intro hReady
  exact hMissing hReady.2.2.1

end P0EFTJanusZ2SigmaDiracCurrentParityFromSpinorIntertwinerGate
end JanusFormal
