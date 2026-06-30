import JanusFormal.P0EFTGlobalBoundarySpectralConvergence

namespace JanusFormal
namespace P0EFTCosmologyConditionalBridge

set_option autoImplicit false

structure CosmologyBridge where
  boundarySectorConditionallyReady : Prop
  feedsDSPerturbationPipeline : Prop
  scalarTensorDSUpdated : Prop
  matterVlasovClosed : Prop
  observablesDerived : Prop
  fullCosmologyPredictionReady : Prop

def boundaryMayFeedCosmology (b : CosmologyBridge) : Prop :=
  b.boundarySectorConditionallyReady /\
  b.feedsDSPerturbationPipeline

def fullCosmologyReady (b : CosmologyBridge) : Prop :=
  boundaryMayFeedCosmology b /\
  b.scalarTensorDSUpdated /\
  b.matterVlasovClosed /\
  b.observablesDerived /\
  b.fullCosmologyPredictionReady

theorem boundary_conditionally_feeds_ds_pipeline
    (b : CosmologyBridge)
    (hBoundary : b.boundarySectorConditionallyReady)
    (hFeeds : b.feedsDSPerturbationPipeline) :
    boundaryMayFeedCosmology b := by
  exact And.intro hBoundary hFeeds

theorem missing_matter_vlasov_blocks_full_cosmology
    (b : CosmologyBridge)
    (hMissing : Not b.matterVlasovClosed) :
    Not (fullCosmologyReady b) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_observables_blocks_full_cosmology
    (b : CosmologyBridge)
    (hMissing : Not b.observablesDerived) :
    Not (fullCosmologyReady b) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTCosmologyConditionalBridge
end JanusFormal
