import JanusFormal.Branches.Z2SigmaRegular.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaFLRWExtrinsicCurvatureGridWriterGate

set_option autoImplicit false

structure FLRWExtrinsicCurvatureGridWriterGate where
  gridInputDeclared : Prop
  gridInputValid : Prop
  activeTunnelEmbeddingOfAReady : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  aGridDeclared : Prop
  plusMinusKsDeclared : Prop
  plusMinusKtauDeclared : Prop
  z2OrientationSignDeclared : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  outputWritten : Prop

def canWriteFLRWExtrinsicCurvatureGrid
    (g : FLRWExtrinsicCurvatureGridWriterGate) : Prop :=
  g.gridInputDeclared /\
  g.gridInputValid /\
  g.activeTunnelEmbeddingOfAReady /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.aGridDeclared /\
  g.plusMinusKsDeclared /\
  g.plusMinusKtauDeclared /\
  g.z2OrientationSignDeclared /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden

theorem invalid_input_blocks_grid_write
    (g : FLRWExtrinsicCurvatureGridWriterGate)
    (hInvalid : Not g.gridInputValid) :
    Not (canWriteFLRWExtrinsicCurvatureGrid g) := by
  intro h
  exact hInvalid h.2.1

theorem grid_write_requires_active_embedding
    (g : FLRWExtrinsicCurvatureGridWriterGate)
    (h : canWriteFLRWExtrinsicCurvatureGrid g) :
    g.activeTunnelEmbeddingOfAReady := by
  exact h.2.2.1

theorem grid_write_requires_plus_minus_K_components
    (g : FLRWExtrinsicCurvatureGridWriterGate)
    (h : canWriteFLRWExtrinsicCurvatureGrid g) :
    g.plusMinusKsDeclared /\ g.plusMinusKtauDeclared := by
  exact And.intro h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaFLRWExtrinsicCurvatureGridWriterGate
end JanusFormal
