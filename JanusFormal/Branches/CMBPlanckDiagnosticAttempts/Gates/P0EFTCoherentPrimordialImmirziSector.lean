namespace JanusFormal
namespace P0EFTCoherentPrimordialImmirziSector

set_option autoImplicit false

structure CoherentPrimordialImmirziSector where
  singleHolstSource : Prop
  wardBianchiLocked : Prop
  tracelessHolstStress : Prop
  uniqueCoefficientsDerived : Prop
  cambPatchContractReady : Prop
  cambPatchActivated : Prop
  planckAccepted : Prop

def coherentSectorDerived (s : CoherentPrimordialImmirziSector) : Prop :=
  s.singleHolstSource /\
  s.wardBianchiLocked /\
  s.tracelessHolstStress /\
  s.uniqueCoefficientsDerived

def coherentPatchReady (s : CoherentPrimordialImmirziSector) : Prop :=
  coherentSectorDerived s /\ s.cambPatchContractReady

def cmbNoFitReady (s : CoherentPrimordialImmirziSector) : Prop :=
  coherentPatchReady s /\ s.cambPatchActivated /\ s.planckAccepted

theorem coherent_derivation_gives_patch_contract
    (s : CoherentPrimordialImmirziSector)
    (hSingle : s.singleHolstSource)
    (hWard : s.wardBianchiLocked)
    (hTrace : s.tracelessHolstStress)
    (hUnique : s.uniqueCoefficientsDerived)
    (hContract : s.cambPatchContractReady) :
    coherentPatchReady s := by
  exact And.intro (And.intro hSingle (And.intro hWard (And.intro hTrace hUnique))) hContract

theorem unactivated_contract_does_not_claim_cmb_no_fit
    (s : CoherentPrimordialImmirziSector)
    (_hReady : coherentPatchReady s)
    (hInactive : Not s.cambPatchActivated) :
    Not (cmbNoFitReady s) := by
  intro h
  exact hInactive h.right.left

theorem planck_rejection_blocks_cmb_no_fit
    (s : CoherentPrimordialImmirziSector)
    (hRejected : Not s.planckAccepted) :
    Not (cmbNoFitReady s) := by
  intro h
  exact hRejected h.right.right

end P0EFTCoherentPrimordialImmirziSector
end JanusFormal
