namespace JanusFormal
namespace P0EFTCoherentImmirziActivationProfileScan

set_option autoImplicit false

structure CoherentImmirziActivationProfileScan where
  earlyProfilesScanned : Prop
  adiabaticProfilesScanned : Prop
  planckDeltaAccepted : Prop

def profileScanComplete (s : CoherentImmirziActivationProfileScan) : Prop :=
  s.earlyProfilesScanned /\ s.adiabaticProfilesScanned

def profileNoFitReady (s : CoherentImmirziActivationProfileScan) : Prop :=
  profileScanComplete s /\ s.planckDeltaAccepted

theorem rejected_profiles_block_no_fit
    (s : CoherentImmirziActivationProfileScan)
    (hRejected : Not s.planckDeltaAccepted) :
    Not (profileNoFitReady s) := by
  intro h
  exact hRejected h.right

end P0EFTCoherentImmirziActivationProfileScan
end JanusFormal
