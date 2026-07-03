namespace JanusFormal
namespace P0EFTJanusSigmaBoundaryVariationalDecompositionGate

set_option autoImplicit false

structure SigmaBoundaryVariationalDecompositionGate where
  throatSigmaDefined : Prop
  inducedBoundaryMeasureDeclared : Prop
  cartanGHYBoundaryTermDeclared : Prop
  holstNiehYanBoundaryTermDeclared : Prop
  matterFluxBoundaryTermDeclared : Prop
  tunnelJunctionTermDeclared : Prop
  boundaryVariationDecomposedByFields : Prop
  tetradVariationChannelDeclared : Prop
  connectionVariationChannelDeclared : Prop
  spinorVariationChannelDeclared : Prop
  nonlinearResidualObstructionIsolated : Prop
  nonlinearBoundaryVariationClosed : Prop
  fullBoundaryActionClosedOnSigma : Prop

def sigmaBoundaryVariationalPackageDeclared
    (g : SigmaBoundaryVariationalDecompositionGate) : Prop :=
  g.throatSigmaDefined /\
  g.inducedBoundaryMeasureDeclared /\
  g.cartanGHYBoundaryTermDeclared /\
  g.holstNiehYanBoundaryTermDeclared /\
  g.matterFluxBoundaryTermDeclared /\
  g.tunnelJunctionTermDeclared /\
  g.boundaryVariationDecomposedByFields /\
  g.tetradVariationChannelDeclared /\
  g.connectionVariationChannelDeclared /\
  g.spinorVariationChannelDeclared /\
  g.nonlinearResidualObstructionIsolated

def sigmaBoundaryVariationStillOpen
    (g : SigmaBoundaryVariationalDecompositionGate) : Prop :=
  sigmaBoundaryVariationalPackageDeclared g /\
  Not g.nonlinearBoundaryVariationClosed /\
  Not g.fullBoundaryActionClosedOnSigma

theorem nonlinear_residual_blocks_full_sigma_boundary_action
    (g : SigmaBoundaryVariationalDecompositionGate)
    (h : sigmaBoundaryVariationStillOpen g) :
    Not g.fullBoundaryActionClosedOnSigma := by
  exact h.2.2

theorem declared_variational_package_is_not_full_closure
    (g : SigmaBoundaryVariationalDecompositionGate)
    (h : sigmaBoundaryVariationStillOpen g) :
    sigmaBoundaryVariationalPackageDeclared g /\ Not g.nonlinearBoundaryVariationClosed := by
  exact And.intro h.1 h.2.1

end P0EFTJanusSigmaBoundaryVariationalDecompositionGate
end JanusFormal
