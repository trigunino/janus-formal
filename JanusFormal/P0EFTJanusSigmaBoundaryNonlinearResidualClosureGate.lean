namespace JanusFormal
namespace P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate

set_option autoImplicit false

structure SigmaBoundaryNonlinearResidualClosureGate where
  sigmaBoundaryVariationalPackageDeclared : Prop
  nonlinearResidualObstructionIsolated : Prop
  sigmaSupportedCountertermUnique : Prop
  countertermVariationCancelsResidual : Prop
  tetradChannelClosed : Prop
  connectionChannelClosed : Prop
  spinorChannelClosed : Prop
  nonlinearBoundaryVariationOnSigmaClosed : Prop
  fullBoundaryActionClosedOnSigma : Prop

def sigmaNonlinearBoundaryResidualClosed
    (g : SigmaBoundaryNonlinearResidualClosureGate) : Prop :=
  g.sigmaBoundaryVariationalPackageDeclared /\
  g.nonlinearResidualObstructionIsolated /\
  g.sigmaSupportedCountertermUnique /\
  g.countertermVariationCancelsResidual /\
  g.tetradChannelClosed /\
  g.connectionChannelClosed /\
  g.spinorChannelClosed /\
  g.nonlinearBoundaryVariationOnSigmaClosed

def sigmaFullBoundaryActionClosed
    (g : SigmaBoundaryNonlinearResidualClosureGate) : Prop :=
  sigmaNonlinearBoundaryResidualClosed g /\
  g.fullBoundaryActionClosedOnSigma

theorem nonlinear_residual_closure_gives_full_sigma_boundary_action
    (g : SigmaBoundaryNonlinearResidualClosureGate)
    (h : sigmaFullBoundaryActionClosed g) :
    g.fullBoundaryActionClosedOnSigma := by
  exact h.2

theorem sigma_counterterm_is_required_for_nonlinear_closure
    (g : SigmaBoundaryNonlinearResidualClosureGate)
    (h : sigmaNonlinearBoundaryResidualClosed g) :
    g.sigmaSupportedCountertermUnique /\ g.countertermVariationCancelsResidual := by
  exact And.intro h.right.right.left h.right.right.right.left

end P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
end JanusFormal
