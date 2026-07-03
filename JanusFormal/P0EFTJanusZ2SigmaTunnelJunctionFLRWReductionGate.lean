import JanusFormal.P0EFTJanusZ2SigmaTunnelJunctionConditionGate
import JanusFormal.P0EFTJanusZ2SigmaTunnelEmbeddingExtrinsicCurvatureGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaTunnelJunctionFLRWReductionGate

set_option autoImplicit false

structure TunnelJunctionFLRWReductionGate where
  israelJunctionBibliographyChecked : Prop
  z2TunnelJunctionConditionDerived : Prop
  tunnelEmbeddingExtrinsicCurvatureStructuralReady : Prop
  flrwTraceReverseAlgebraDeclared : Prop
  junctionRhoProjectionFormulaReady : Prop
  junctionPProjectionFormulaReady : Prop
  nonCircularUseOfJunctionDeclared : Prop
  deltaKsOfAReady : Prop
  deltaKtauOfAReady : Prop
  junctionRhoPOfAReady : Prop

def tunnelJunctionFLRWAlgebraReady
    (g : TunnelJunctionFLRWReductionGate) : Prop :=
  g.israelJunctionBibliographyChecked /\
  g.z2TunnelJunctionConditionDerived /\
  g.tunnelEmbeddingExtrinsicCurvatureStructuralReady /\
  g.flrwTraceReverseAlgebraDeclared /\
  g.junctionRhoProjectionFormulaReady /\
  g.junctionPProjectionFormulaReady /\
  g.nonCircularUseOfJunctionDeclared

def tunnelJunctionFLRWClosureReady
    (g : TunnelJunctionFLRWReductionGate) : Prop :=
  tunnelJunctionFLRWAlgebraReady g /\
  g.deltaKsOfAReady /\
  g.deltaKtauOfAReady /\
  g.junctionRhoPOfAReady

theorem junction_flrw_closure_requires_deltaK_of_a
    (g : TunnelJunctionFLRWReductionGate)
    (hReady : tunnelJunctionFLRWClosureReady g) :
    g.deltaKsOfAReady /\ g.deltaKtauOfAReady := by
  exact ⟨hReady.2.1, hReady.2.2.1⟩

end P0EFTJanusZ2SigmaTunnelJunctionFLRWReductionGate
end JanusFormal
