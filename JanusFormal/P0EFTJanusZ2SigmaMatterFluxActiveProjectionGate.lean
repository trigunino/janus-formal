import JanusFormal.P0EFTJanusZ2SigmaMatterFluxTransparencyGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate

set_option autoImplicit false

structure MatterFluxActiveProjectionGate where
  thinShellFluxProjectionBibliographyChecked : Prop
  transparencyNotAssumed : Prop
  plusBulkStressDeclared : Prop
  minusBulkStressDeclared : Prop
  bulkStressNormalFluxCancellationGateDeclared : Prop
  sigmaTangentsDeclared : Prop
  sigmaNormalsDeclared : Prop
  z2OrientationProjectionDeclared : Prop
  observationalFitForbidden : Prop
  fPlusProjectionDeclared : Prop
  fMinusProjectionDeclared : Prop
  netFluxProjectionDeclared : Prop
  plusBulkStressOfAReady : Prop
  minusBulkStressOfAReady : Prop
  embeddingOfAReady : Prop
  activeFluxOfAReady : Prop

def activeFluxProjectionLedgerDeclared
    (g : MatterFluxActiveProjectionGate) : Prop :=
  g.thinShellFluxProjectionBibliographyChecked /\
  g.transparencyNotAssumed /\
  g.plusBulkStressDeclared /\
  g.minusBulkStressDeclared /\
  g.bulkStressNormalFluxCancellationGateDeclared /\
  g.sigmaTangentsDeclared /\
  g.sigmaNormalsDeclared /\
  g.z2OrientationProjectionDeclared /\
  g.observationalFitForbidden /\
  g.fPlusProjectionDeclared /\
  g.fMinusProjectionDeclared /\
  g.netFluxProjectionDeclared

def activeFluxProjectionReady
    (g : MatterFluxActiveProjectionGate) : Prop :=
  activeFluxProjectionLedgerDeclared g /\
  g.plusBulkStressOfAReady /\
  g.minusBulkStressOfAReady /\
  g.embeddingOfAReady /\
  g.activeFluxOfAReady

theorem active_flux_requires_embedding
    (g : MatterFluxActiveProjectionGate)
    (hReady : activeFluxProjectionReady g) :
    g.embeddingOfAReady := by
  rcases hReady with ⟨_, _, _, hEmbedding, _⟩
  exact hEmbedding

end P0EFTJanusZ2SigmaMatterFluxActiveProjectionGate
end JanusFormal
