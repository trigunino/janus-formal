namespace JanusFormal
namespace P0EFTCMBFullHierarchyPreLikelihood

set_option autoImplicit false

structure CMBFullHierarchyPreLikelihood where
  weylSourceEquationUsed : Prop
  physicalVisibilityUsed : Prop
  photonBaryonNeutrinoHierarchyIntegrated : Prop
  primordialSpectrumIncluded : Prop
  spectraProxyComputed : Prop
  externalBoltzmannValidationReady : Prop
  uncompressedPlanckLikelihoodReady : Prop

def preLikelihoodPipelineReady (c : CMBFullHierarchyPreLikelihood) : Prop :=
  c.weylSourceEquationUsed /\
  c.physicalVisibilityUsed /\
  c.photonBaryonNeutrinoHierarchyIntegrated /\
  c.primordialSpectrumIncluded /\
  c.spectraProxyComputed

def directCMBLikelihoodReady (c : CMBFullHierarchyPreLikelihood) : Prop :=
  preLikelihoodPipelineReady c /\
  c.externalBoltzmannValidationReady /\
  c.uncompressedPlanckLikelihoodReady

theorem full_pre_likelihood_pipeline_computes_required_proxy_spectra
    (c : CMBFullHierarchyPreLikelihood)
    (hWeyl : c.weylSourceEquationUsed)
    (hVis : c.physicalVisibilityUsed)
    (hHierarchy : c.photonBaryonNeutrinoHierarchyIntegrated)
    (hPrimordial : c.primordialSpectrumIncluded)
    (hSpectra : c.spectraProxyComputed) :
    preLikelihoodPipelineReady c := by
  exact And.intro hWeyl (And.intro hVis (And.intro hHierarchy (And.intro hPrimordial hSpectra)))

theorem missing_external_boltzmann_validation_blocks_direct_cmb
    (c : CMBFullHierarchyPreLikelihood)
    (hMissing : Not c.externalBoltzmannValidationReady) :
    Not (directCMBLikelihoodReady c) := by
  intro h
  exact hMissing h.right.left

end P0EFTCMBFullHierarchyPreLikelihood
end JanusFormal
