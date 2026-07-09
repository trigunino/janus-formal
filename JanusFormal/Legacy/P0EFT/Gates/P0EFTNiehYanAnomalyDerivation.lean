namespace JanusFormal
namespace P0EFTNiehYanAnomalyDerivation

set_option autoImplicit false

structure NiehYanTraceLock where
  diracTraceRank : Int
  apsHalfRank : Int
  etaH : Int
  standardTraceNormalizationLoaded : Prop
  globalTraceNormalizationDerived : Prop

def etaHPlusTwoClosed (l : NiehYanTraceLock) : Prop :=
  l.etaH + 2 = 0

def localTraceDerivesEtaMinusTwo (l : NiehYanTraceLock) : Prop :=
  l.standardTraceNormalizationLoaded /\
  l.diracTraceRank = 4 /\
  l.apsHalfRank = 2 /\
  l.etaH = -2

theorem eta_h_minus_two_from_standard_trace
    (l : NiehYanTraceLock)
    (h : localTraceDerivesEtaMinusTwo l) :
    etaHPlusTwoClosed l := by
  unfold etaHPlusTwoClosed
  rw [h.right.right.right]
  rfl

theorem no_global_no_fit_from_trace_alone
    (l : NiehYanTraceLock)
    (hMissing : Not l.globalTraceNormalizationDerived) :
    Not (l.globalTraceNormalizationDerived /\ etaHPlusTwoClosed l) := by
  intro h
  exact hMissing h.left

end P0EFTNiehYanAnomalyDerivation
end JanusFormal
