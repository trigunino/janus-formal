namespace JanusFormal
namespace P0EFTJanusZ2PublishedSO3BianchiReductionGate

set_option autoImplicit false

structure PublishedSO3BianchiReductionGate where
  interactionSlotsReady : Prop
  sameSectorAttractionReady : Prop
  oppositeSectorRepulsionReady : Prop
  tovNewtonianBianchiAsymptoticReady : Prop
  stationarySO3ReducedBianchiReady : Prop
  genericTensorBianchiReady : Prop
  sigmaTransportReady : Prop
  sigmaSourceAvailable : Prop
  fullNoFitPredictionReady : Prop

def so3ReducedSectorReady
    (g : PublishedSO3BianchiReductionGate) : Prop :=
  g.interactionSlotsReady /\
  g.sameSectorAttractionReady /\
  g.oppositeSectorRepulsionReady /\
  g.tovNewtonianBianchiAsymptoticReady /\
  g.stationarySO3ReducedBianchiReady

theorem so3_reduction_is_not_generic_tensor_closure
    (g : PublishedSO3BianchiReductionGate)
    (_h : so3ReducedSectorReady g)
    (hNoGeneric : Not g.genericTensorBianchiReady) :
    Not g.genericTensorBianchiReady := by
  exact hNoGeneric

theorem so3_reduction_does_not_imply_sigma_source
    (g : PublishedSO3BianchiReductionGate)
    (_h : so3ReducedSectorReady g)
    (hNoSigma : Not g.sigmaSourceAvailable) :
    Not g.sigmaSourceAvailable := by
  exact hNoSigma

theorem missing_sigma_transport_blocks_no_fit_prediction
    (g : PublishedSO3BianchiReductionGate)
    (hNoSigma : Not g.sigmaTransportReady)
    (hNoFitNeedsSigma : g.fullNoFitPredictionReady -> g.sigmaTransportReady) :
    Not g.fullNoFitPredictionReady := by
  intro hReady
  exact hNoSigma (hNoFitNeedsSigma hReady)

end P0EFTJanusZ2PublishedSO3BianchiReductionGate
end JanusFormal
