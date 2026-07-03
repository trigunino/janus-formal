import JanusFormal.P0EFTJanusZ2SigmaNormalMatterCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaPlusMinusMatterCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracMatterCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaProjectedDiracNormalCurrentGate
import JanusFormal.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGate

set_option autoImplicit false

structure NormalMatterCurrentReadinessGate where
  normalMatterCurrentGateImported : Prop
  plusMinusMatterCurrentGateImported : Prop
  projectedDiracMatterCurrentGateImported : Prop
  projectedDiracNormalCurrentGateImported : Prop
  activeEmbeddingReadinessGateImported : Prop
  diracNoetherCurrentBibliographyChecked : Prop
  activeEmbeddingReady : Prop
  sigmaNormalsReady : Prop
  plusMinusMatterCurrentsReady : Prop
  projectedDiracMatterCurrentReady : Prop
  projectedDiracNormalCurrentReady : Prop
  noNormalMatterCurrentDerived : Prop
  noNormalMatterCurrentReady : Prop

def normalMatterCurrentReadinessLedgerDeclared
    (g : NormalMatterCurrentReadinessGate) : Prop :=
  g.normalMatterCurrentGateImported /\
  g.plusMinusMatterCurrentGateImported /\
  g.projectedDiracMatterCurrentGateImported /\
  g.projectedDiracNormalCurrentGateImported /\
  g.activeEmbeddingReadinessGateImported /\
  g.diracNoetherCurrentBibliographyChecked

def normalMatterCurrentReadinessReady
    (g : NormalMatterCurrentReadinessGate) : Prop :=
  normalMatterCurrentReadinessLedgerDeclared g /\
  g.activeEmbeddingReady /\
  g.sigmaNormalsReady /\
  g.plusMinusMatterCurrentsReady /\
  g.projectedDiracMatterCurrentReady /\
  g.projectedDiracNormalCurrentReady /\
  g.noNormalMatterCurrentDerived /\
  g.noNormalMatterCurrentReady

theorem normal_current_readiness_requires_normals
    (g : NormalMatterCurrentReadinessGate)
    (hReady : normalMatterCurrentReadinessReady g) :
    g.sigmaNormalsReady := by
  exact hReady.2.2.1

theorem normal_current_readiness_feeds_no_normal_current
    (g : NormalMatterCurrentReadinessGate)
    (hReady : normalMatterCurrentReadinessReady g) :
    g.noNormalMatterCurrentReady := by
  exact hReady.2.2.2.2.2.2.2

end P0EFTJanusZ2SigmaNormalMatterCurrentReadinessGate
end JanusFormal
