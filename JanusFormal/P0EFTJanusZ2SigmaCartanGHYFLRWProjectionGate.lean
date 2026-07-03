import JanusFormal.P0EFTJanusZ2SigmaBoundaryStressExtractionGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGate

set_option autoImplicit false

structure CartanGHYFLRWProjectionGate where
  brownYorkCartanGHYConventionDeclared : Prop
  flrwInducedMetricDeclared : Prop
  z2NormalOrientationDeclared : Prop
  extrinsicCurvatureScalarsDeclared : Prop
  deltaKsProjectionFormulaReady : Prop
  deltaKtauProjectionFormulaReady : Prop
  rhoCartanGHYFormulaReady : Prop
  pCartanGHYFormulaReady : Prop
  deltaKsOfAReady : Prop
  deltaKtauOfAReady : Prop

def cartanGHYFLRWAlgebraicProjectionReady
    (g : CartanGHYFLRWProjectionGate) : Prop :=
  g.brownYorkCartanGHYConventionDeclared /\
  g.flrwInducedMetricDeclared /\
  g.z2NormalOrientationDeclared /\
  g.extrinsicCurvatureScalarsDeclared /\
  g.deltaKsProjectionFormulaReady /\
  g.deltaKtauProjectionFormulaReady /\
  g.rhoCartanGHYFormulaReady /\
  g.pCartanGHYFormulaReady

def cartanGHYFLRWScaleFactorClosureReady
    (g : CartanGHYFLRWProjectionGate) : Prop :=
  cartanGHYFLRWAlgebraicProjectionReady g /\
  g.deltaKsOfAReady /\
  g.deltaKtauOfAReady

theorem scale_factor_closure_requires_algebraic_projection
    (g : CartanGHYFLRWProjectionGate)
    (hReady : cartanGHYFLRWScaleFactorClosureReady g) :
    cartanGHYFLRWAlgebraicProjectionReady g := by
  exact hReady.left

end P0EFTJanusZ2SigmaCartanGHYFLRWProjectionGate
end JanusFormal
