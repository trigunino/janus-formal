import JanusFormal.P0EFTJanusZ2SigmaConnectionForceResidualMatchingGate
import JanusFormal.P0EFTJanusZ2SigmaSCrossPhiLVariationLawGate
import JanusFormal.P0EFTJanusZ2SigmaActiveEmbeddingReadinessGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSourceForceEquationTargetGate

set_option autoImplicit false

structure SourceForceEquationTargetGate where
  connectionForceResidualMatchingGateImported : Prop
  sCrossPhiLVariationLawGateImported : Prop
  activeEmbeddingReadinessGateImported : Prop
  plusForceEquationTargetWritten : Prop
  minusForceEquationTargetWritten : Prop
  phiLSourceRouteAllowed : Prop
  activeEmbeddingSourceRouteAllowed : Prop
  noGeodesicShortcut : Prop
  noLorentzAdmissibilityShortcut : Prop
  noQcrossForceAbsorption : Prop
  phiLVariationLawReady : Prop
  activeEmbeddingReady : Prop
  plusSourceForceEquationDerived : Prop
  minusSourceForceEquationDerived : Prop
  sourceForceEquationsDerived : Prop
  feedsConnectionForceResidualMatching : Prop

def sourceForceEquationTargetWritten
    (g : SourceForceEquationTargetGate) : Prop :=
  g.connectionForceResidualMatchingGateImported /\
  g.sCrossPhiLVariationLawGateImported /\
  g.activeEmbeddingReadinessGateImported /\
  g.plusForceEquationTargetWritten /\
  g.minusForceEquationTargetWritten /\
  g.phiLSourceRouteAllowed /\
  g.activeEmbeddingSourceRouteAllowed /\
  g.noGeodesicShortcut /\
  g.noLorentzAdmissibilityShortcut /\
  g.noQcrossForceAbsorption

def sourceForceEquationReady
    (g : SourceForceEquationTargetGate) : Prop :=
  sourceForceEquationTargetWritten g /\
  (g.phiLVariationLawReady \/ g.activeEmbeddingReady) /\
  g.plusSourceForceEquationDerived /\
  g.minusSourceForceEquationDerived /\
  g.sourceForceEquationsDerived /\
  g.feedsConnectionForceResidualMatching

theorem source_force_equations_feed_connection_matching
    (g : SourceForceEquationTargetGate)
    (hReady : sourceForceEquationReady g) :
    g.sourceForceEquationsDerived /\ g.feedsConnectionForceResidualMatching := by
  exact And.intro hReady.right.right.right.right.left
    hReady.right.right.right.right.right

theorem missing_plus_source_force_blocks_source_force_ready
    (g : SourceForceEquationTargetGate)
    (hMissing : Not g.plusSourceForceEquationDerived) :
    Not (sourceForceEquationReady g) := by
  intro hReady
  exact hMissing hReady.right.right.left

theorem target_forbids_shortcuts
    (g : SourceForceEquationTargetGate)
    (hTarget : sourceForceEquationTargetWritten g) :
    g.noGeodesicShortcut /\ g.noLorentzAdmissibilityShortcut /\
      g.noQcrossForceAbsorption := by
  exact And.intro hTarget.right.right.right.right.right.right.right.left
    (And.intro hTarget.right.right.right.right.right.right.right.right.left
      hTarget.right.right.right.right.right.right.right.right.right)

end P0EFTJanusZ2SigmaSourceForceEquationTargetGate
end JanusFormal
