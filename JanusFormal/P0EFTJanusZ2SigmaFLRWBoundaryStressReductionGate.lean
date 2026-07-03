import JanusFormal.P0EFTJanusZ2SigmaBoundaryStressExtractionGate
import JanusFormal.P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGate
import JanusFormal.P0EFTJanusZ2SigmaHolstNiehYanFLRWObligationGate
import JanusFormal.P0EFTJanusZ2SigmaMatterFluxFLRWObligationGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionFLRWReductionGate
import JanusFormal.P0EFTJanusZ2SigmaCountertermFLRWObligationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWBoundaryStressReductionGate

set_option autoImplicit false

structure Z2SigmaFLRWBoundaryStressReductionGate where
  boundaryStressExtractionFormulaClosed : Prop
  inducedFLRWSigmaMetricDeclared : Prop
  z2NormalOrientationDeclared : Prop
  cartanGHYFLRWReduced : Prop
  holstNiehYanFLRWReduced : Prop
  matterFluxFLRWReduced : Prop
  tunnelJunctionFLRWReduced : Prop
  countertermFLRWReduced : Prop
  componentSignsFixedByZ2Normal : Prop
  tEffABReadyForFLRWProjection : Prop

def allComponentReductionsReady
    (g : Z2SigmaFLRWBoundaryStressReductionGate) : Prop :=
  g.cartanGHYFLRWReduced /\
  g.holstNiehYanFLRWReduced /\
  g.matterFluxFLRWReduced /\
  g.tunnelJunctionFLRWReduced /\
  g.countertermFLRWReduced

def flrwBoundaryStressReductionReady
    (g : Z2SigmaFLRWBoundaryStressReductionGate) : Prop :=
  g.boundaryStressExtractionFormulaClosed /\
  g.inducedFLRWSigmaMetricDeclared /\
  g.z2NormalOrientationDeclared /\
  allComponentReductionsReady g /\
  g.componentSignsFixedByZ2Normal /\
  g.tEffABReadyForFLRWProjection

theorem flrw_projection_requires_all_component_reductions
    (g : Z2SigmaFLRWBoundaryStressReductionGate)
    (hReady : flrwBoundaryStressReductionReady g) :
    allComponentReductionsReady g := by
  exact hReady.2.2.2.1

end P0EFTJanusZ2SigmaFLRWBoundaryStressReductionGate
end JanusFormal
