namespace JanusFormal
namespace P0EFTHolstFullStressTensorPatch

set_option autoImplicit false

structure HolstFullStressTensorPatch where
  deltaRhoPatched : Prop
  deltaPPatched : Prop
  heatFluxPatched : Prop
  anisotropicStressPatched : Prop
  einsteinConstraintsReceiveStress : Prop
  legacySourceTermsDecoupled : Prop
  cambPatchActivated : Prop
  planckAccepted : Prop

def fullStressTensorPatchComplete (p : HolstFullStressTensorPatch) : Prop :=
  p.deltaRhoPatched /\
  p.deltaPPatched /\
  p.heatFluxPatched /\
  p.anisotropicStressPatched /\
  p.einsteinConstraintsReceiveStress /\
  p.legacySourceTermsDecoupled

def planckNoFitReady (p : HolstFullStressTensorPatch) : Prop :=
  fullStressTensorPatchComplete p /\ p.cambPatchActivated /\ p.planckAccepted

theorem complete_patch_still_requires_planck_gate
    (p : HolstFullStressTensorPatch)
    (_hComplete : fullStressTensorPatchComplete p)
    (hRejected : Not p.planckAccepted) :
    Not (planckNoFitReady p) := by
  intro h
  exact hRejected h.right.right

end P0EFTHolstFullStressTensorPatch
end JanusFormal
