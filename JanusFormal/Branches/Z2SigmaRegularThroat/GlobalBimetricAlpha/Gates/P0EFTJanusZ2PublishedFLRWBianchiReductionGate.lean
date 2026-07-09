namespace JanusFormal
namespace P0EFTJanusZ2PublishedFLRWBianchiReductionGate

set_option autoImplicit false

structure PublishedFLRWBianchiReductionGate where
  interactionSlotsReady : Prop
  determinantFormulaClosed : Prop
  dustScalarTransportClosed : Prop
  flrwReducedBianchiReady : Prop
  genericTensorBianchiReady : Prop
  sigmaTransportReady : Prop
  sigmaCountertermNeededDecided : Prop
  fullNoFitPredictionReady : Prop

def flrwDustReductionReady
    (g : PublishedFLRWBianchiReductionGate) : Prop :=
  g.interactionSlotsReady /\
  g.determinantFormulaClosed /\
  g.dustScalarTransportClosed /\
  g.flrwReducedBianchiReady

theorem flrw_reduction_is_not_generic_tensor_closure
    (g : PublishedFLRWBianchiReductionGate)
    (_h : flrwDustReductionReady g)
    (hNoGeneric : Not g.genericTensorBianchiReady) :
    Not g.genericTensorBianchiReady := by
  exact hNoGeneric

theorem flrw_reduction_does_not_imply_sigma_transport
    (g : PublishedFLRWBianchiReductionGate)
    (_h : flrwDustReductionReady g)
    (hNoSigma : Not g.sigmaTransportReady) :
    Not g.sigmaTransportReady := by
  exact hNoSigma

theorem missing_sigma_transport_blocks_no_fit_prediction
    (g : PublishedFLRWBianchiReductionGate)
    (hNoSigma : Not g.sigmaTransportReady)
    (hNoFitNeedsSigma : g.fullNoFitPredictionReady -> g.sigmaTransportReady) :
    Not g.fullNoFitPredictionReady := by
  intro hReady
  exact hNoSigma (hNoFitNeedsSigma hReady)

end P0EFTJanusZ2PublishedFLRWBianchiReductionGate
end JanusFormal
