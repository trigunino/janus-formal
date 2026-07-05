namespace JanusFormal
namespace P0EFTJanusZ2SigmaSpinorSolderingEquivarianceFromBoundaryVariationGate

set_option autoImplicit false

structure SpinorSolderingEquivarianceFromBoundaryVariationGate where
  boundaryVariationalDecompositionImported : Prop
  spinorResidualChannelImported : Prop
  localUZ2SigmaImported : Prop
  spinorSolderingConditionDeclared : Prop
  freeSpinorPhaseForbidden : Prop
  mitProjectorAssumptionForbidden : Prop
  observationalFitForbidden : Prop
  rPsiExplicitFromBoundaryVariation : Prop
  rPsibarExplicitFromBoundaryVariation : Prop
  spinorResidualCompatibleWithUZ2Projection : Prop
  solderingResidualZeroDerived : Prop
  physicalSpinorEquivarianceDerived : Prop

def ledgerDeclared
    (g : SpinorSolderingEquivarianceFromBoundaryVariationGate) : Prop :=
  g.boundaryVariationalDecompositionImported /\
  g.spinorResidualChannelImported /\
  g.localUZ2SigmaImported /\
  g.spinorSolderingConditionDeclared /\
  g.freeSpinorPhaseForbidden /\
  g.mitProjectorAssumptionForbidden /\
  g.observationalFitForbidden

def ready
    (g : SpinorSolderingEquivarianceFromBoundaryVariationGate) : Prop :=
  ledgerDeclared g /\
  g.rPsiExplicitFromBoundaryVariation /\
  g.rPsibarExplicitFromBoundaryVariation /\
  g.spinorResidualCompatibleWithUZ2Projection /\
  g.solderingResidualZeroDerived /\
  g.physicalSpinorEquivarianceDerived

theorem ready_requires_spinor_residual_coefficients
    (g : SpinorSolderingEquivarianceFromBoundaryVariationGate)
    (h : ready g) :
    g.rPsiExplicitFromBoundaryVariation /\
      g.rPsibarExplicitFromBoundaryVariation := by
  exact ⟨h.2.1, h.2.2.1⟩

theorem no_equivariance_without_soldering_residual
    (g : SpinorSolderingEquivarianceFromBoundaryVariationGate)
    (_h : ledgerDeclared g)
    (hMissing : Not g.solderingResidualZeroDerived) :
    Not (ready g) := by
  intro hReady
  exact hMissing hReady.2.2.2.2.1

end P0EFTJanusZ2SigmaSpinorSolderingEquivarianceFromBoundaryVariationGate
end JanusFormal
