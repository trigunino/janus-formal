import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaActiveTunnelEmbeddingOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaActiveEmbeddingToFLRWExtrinsicCurvatureInputGate

set_option autoImplicit false

structure ActiveEmbeddingToFLRWExtrinsicCurvatureInputGate where
  adapterDeclared : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4BackgroundReuseForbidden : Prop
  observationalH0FitForbidden : Prop
  observationalCurvatureFitForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  embeddingManifestFiniteAndGridMatched : Prop
  embeddingProvenanceNonempty : Prop
  embeddingManifestIncludesReducedK : Prop
  activeTunnelEmbeddingOfAReady : Prop
  rSigmaOfADerived : Prop
  xPlusMinusOfADerived : Prop
  tangentFramesDerived : Prop
  unitNormalsDerived : Prop
  extrinsicCurvatureComponentsDerived : Prop
  activeTunnelEmbeddingFrontierDeclared : Prop
  embeddingGeometryManifestFrontierDeclared : Prop
  nearestEmbeddingToFLRWKFrontierDeclared : Prop
  nearestEmbeddingToFLRWKFrontierDiagnosticOnly : Prop
  flrwExtrinsicCurvatureGridInputsWritten : Prop
  gatePassed : Prop

def canWriteGridInputs
    (g : ActiveEmbeddingToFLRWExtrinsicCurvatureInputGate) : Prop :=
  g.adapterDeclared /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4BackgroundReuseForbidden /\
  g.observationalH0FitForbidden /\
  g.observationalCurvatureFitForbidden /\
  g.phenomenologicalHolstBAOScanForbidden /\
  g.embeddingManifestFiniteAndGridMatched /\
  g.embeddingProvenanceNonempty /\
  g.embeddingManifestIncludesReducedK /\
  g.tangentFramesDerived /\
  g.unitNormalsDerived /\
  g.extrinsicCurvatureComponentsDerived /\
  g.activeTunnelEmbeddingFrontierDeclared /\
  g.embeddingGeometryManifestFrontierDeclared /\
  g.nearestEmbeddingToFLRWKFrontierDeclared /\
  g.nearestEmbeddingToFLRWKFrontierDiagnosticOnly

theorem grid_inputs_can_use_active_manifest_certificate
    (g : ActiveEmbeddingToFLRWExtrinsicCurvatureInputGate)
    (h : canWriteGridInputs g) :
    g.embeddingManifestFiniteAndGridMatched /\
    g.embeddingProvenanceNonempty /\
    g.embeddingManifestIncludesReducedK := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, hFinite, hProv, hK, _⟩
  exact ⟨hFinite, hProv, hK⟩

theorem grid_inputs_require_active_embedding_manifest_provenance
    (g : ActiveEmbeddingToFLRWExtrinsicCurvatureInputGate)
    (h : canWriteGridInputs g) :
    g.activeCoreZ2Sigma /\
    g.activeDerivedSource /\
    g.compressedPlanckLCDMForbidden /\
    g.archivedZ4BackgroundReuseForbidden /\
    g.observationalH0FitForbidden /\
    g.observationalCurvatureFitForbidden /\
    g.phenomenologicalHolstBAOScanForbidden /\
    g.embeddingManifestFiniteAndGridMatched /\
    g.embeddingProvenanceNonempty := by
  rcases h with
    ⟨_, hCore, hSource, hPlanck, hZ4, hH0, hCurv, hHolst, hFinite, hProv, _⟩
  exact ⟨hCore, hSource, hPlanck, hZ4, hH0, hCurv, hHolst, hFinite, hProv⟩

theorem grid_inputs_require_tangents_normals_and_K
    (g : ActiveEmbeddingToFLRWExtrinsicCurvatureInputGate)
    (h : canWriteGridInputs g) :
    g.tangentFramesDerived /\
    g.unitNormalsDerived /\
    g.extrinsicCurvatureComponentsDerived := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hTangents, hNormals, hK, _⟩
  exact ⟨hTangents, hNormals, hK⟩

theorem grid_inputs_declare_embedding_frontiers
    (g : ActiveEmbeddingToFLRWExtrinsicCurvatureInputGate)
    (h : canWriteGridInputs g) :
    g.activeTunnelEmbeddingFrontierDeclared /\
    g.embeddingGeometryManifestFrontierDeclared /\
    g.nearestEmbeddingToFLRWKFrontierDeclared /\
    g.nearestEmbeddingToFLRWKFrontierDiagnosticOnly := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hEmbedding, hManifest, hNearest, hDiag⟩
  exact ⟨hEmbedding, hManifest, hNearest, hDiag⟩

end P0EFTJanusZ2SigmaActiveEmbeddingToFLRWExtrinsicCurvatureInputGate
end JanusFormal
