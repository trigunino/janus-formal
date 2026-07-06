import JanusFormal.P0EFTJanusZ2SigmaActiveEmbeddingToFLRWExtrinsicCurvatureInputGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPlugstarCurvatureAmplitudeFromEmbeddingGate

set_option autoImplicit false

structure PlugstarCurvatureAmplitudeFromEmbeddingGate where
  activeEmbeddingToFLRWKImported : Prop
  plugstarThresholdGateImported : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  noObservationalFit : Prop
  rSigmaGridAvailable : Prop
  flrwKGridAvailable : Prop
  curvatureConcentrationDeclared : Prop
  curvatureConcentrationZ2Even : Prop
  aKDefinitionDeclared : Prop
  aKPositiveFinite : Prop
  rSigmaMinFormulaUsesActiveAK : Prop
  activeAKCertificateReady : Prop
  gatePassed : Prop

def activeAKLedgerDeclared
    (g : PlugstarCurvatureAmplitudeFromEmbeddingGate) : Prop :=
  g.activeEmbeddingToFLRWKImported /\
  g.plugstarThresholdGateImported /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.noObservationalFit

def activeAKReady
    (g : PlugstarCurvatureAmplitudeFromEmbeddingGate) : Prop :=
  activeAKLedgerDeclared g /\
  g.rSigmaGridAvailable /\
  g.flrwKGridAvailable /\
  g.curvatureConcentrationDeclared /\
  g.curvatureConcentrationZ2Even /\
  g.aKDefinitionDeclared /\
  g.aKPositiveFinite /\
  g.rSigmaMinFormulaUsesActiveAK /\
  g.activeAKCertificateReady /\
  g.gatePassed

theorem active_AK_requires_embedding_curvature_grid
    (g : PlugstarCurvatureAmplitudeFromEmbeddingGate)
    (hReady : activeAKReady g) :
    g.rSigmaGridAvailable /\ g.flrwKGridAvailable := by
  rcases hReady with ⟨_, hR, hK, _⟩
  exact ⟨hR, hK⟩

theorem active_AK_feeds_plugstar_min_radius
    (g : PlugstarCurvatureAmplitudeFromEmbeddingGate)
    (hReady : activeAKReady g) :
    g.rSigmaMinFormulaUsesActiveAK := by
  rcases hReady with ⟨_, _, _, _, _, _, _, hUses, _⟩
  exact hUses

theorem missing_active_K_grid_blocks_active_AK
    (g : PlugstarCurvatureAmplitudeFromEmbeddingGate)
    (hMissing : Not g.flrwKGridAvailable) :
    Not (activeAKReady g) := by
  intro hReady
  exact hMissing (active_AK_requires_embedding_curvature_grid g hReady).right

end P0EFTJanusZ2SigmaPlugstarCurvatureAmplitudeFromEmbeddingGate
end JanusFormal
