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
  alphaResComponentsAvailable : Prop
  lCtExpressionEmitted : Prop

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

def sigmaClosureEmitsComponents
    (g : SigmaBoundaryNonlinearResidualClosureGate) : Prop :=
  sigmaFullBoundaryActionClosed g /\
  g.alphaResComponentsAvailable /\
  g.lCtExpressionEmitted

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

theorem missing_alpha_components_blocks_component_emission
    (g : SigmaBoundaryNonlinearResidualClosureGate)
    (hMissing : Not g.alphaResComponentsAvailable) :
    Not (sigmaClosureEmitsComponents g) := by
  intro hReady
  exact hMissing hReady.2.1

end P0EFTJanusSigmaBoundaryNonlinearResidualClosureGate
end JanusFormal
