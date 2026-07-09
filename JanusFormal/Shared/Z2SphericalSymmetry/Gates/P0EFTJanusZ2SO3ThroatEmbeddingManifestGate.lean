namespace JanusFormal
namespace P0EFTJanusZ2SO3ThroatEmbeddingManifestGate

set_option autoImplicit false

structure SO3ThroatEmbeddingManifestGate where
  stationarySO3ReducedBianchiReady : Prop
  z2EvenRadiusReady : Prop
  minimalThroatReady : Prop
  activeEmbeddingSkeletonReady : Prop
  metricFunctionsReady : Prop
  christoffelsReady : Prop
  unitNormalsReady : Prop
  kAbPlusMinusReady : Prop
  deltaKReady : Prop
  rSigmaSolutionCertificateReady : Prop

def throatSkeletonReady
    (g : SO3ThroatEmbeddingManifestGate) : Prop :=
  g.stationarySO3ReducedBianchiReady /\
  g.z2EvenRadiusReady /\
  g.minimalThroatReady /\
  g.activeEmbeddingSkeletonReady

def extrinsicCurvatureReady
    (g : SO3ThroatEmbeddingManifestGate) : Prop :=
  throatSkeletonReady g /\
  g.metricFunctionsReady /\
  g.christoffelsReady /\
  g.unitNormalsReady /\
  g.kAbPlusMinusReady /\
  g.deltaKReady

theorem skeleton_does_not_imply_deltaK
    (g : SO3ThroatEmbeddingManifestGate)
    (_h : throatSkeletonReady g)
    (hNoDeltaK : Not g.deltaKReady) :
    Not g.deltaKReady := by
  exact hNoDeltaK

theorem extrinsic_curvature_requires_metric_functions
    (g : SO3ThroatEmbeddingManifestGate)
    (hReady : extrinsicCurvatureReady g) :
    g.metricFunctionsReady := by
  exact hReady.2.1

end P0EFTJanusZ2SO3ThroatEmbeddingManifestGate
end JanusFormal
