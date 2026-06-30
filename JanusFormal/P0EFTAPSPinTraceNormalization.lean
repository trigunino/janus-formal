import JanusFormal.P0EFTNiehYanAnomalyDerivation

namespace JanusFormal
namespace P0EFTAPSPinTraceNormalization

set_option autoImplicit false

structure APSPinTraceNormalization where
  bulkHasPinMinusStructure : Prop
  apsBoundaryDomainDefined : Prop
  etaInvariantGlobalRegularizationFixed : Prop
  cliffordTraceRankFixedToFour : Prop
  apsProjectorRankFixedToHalf : Prop

def apsPinGlobalHypothesis (h : APSPinTraceNormalization) : Prop :=
  h.bulkHasPinMinusStructure /\
  h.apsBoundaryDomainDefined /\
  h.etaInvariantGlobalRegularizationFixed

def standardTraceNormalizationDerived (h : APSPinTraceNormalization) : Prop :=
  apsPinGlobalHypothesis h /\
  h.cliffordTraceRankFixedToFour /\
  h.apsProjectorRankFixedToHalf

theorem aps_pin_hypothesis_derives_local_trace_lock
    (h : APSPinTraceNormalization)
    (l : P0EFTNiehYanAnomalyDerivation.NiehYanTraceLock)
    (_hStd : standardTraceNormalizationDerived h)
    (hLocal : P0EFTNiehYanAnomalyDerivation.localTraceDerivesEtaMinusTwo l) :
    P0EFTNiehYanAnomalyDerivation.etaHPlusTwoClosed l := by
  exact P0EFTNiehYanAnomalyDerivation.eta_h_minus_two_from_standard_trace l hLocal

theorem missing_eta_regularization_blocks_standard_trace
    (h : APSPinTraceNormalization)
    (hMissing : Not h.etaInvariantGlobalRegularizationFixed) :
    Not (standardTraceNormalizationDerived h) := by
  intro hStd
  exact hMissing hStd.left.right.right

end P0EFTAPSPinTraceNormalization
end JanusFormal
