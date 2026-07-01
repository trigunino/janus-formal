namespace JanusFormal
namespace P0EFTPrimordialCoupledCMBSectorScaffold

set_option autoImplicit false

structure PrimordialCoupledCMBSector where
  singlePrimordialMode : Prop
  soundSpeedTiedToMode : Prop
  opacityLowETiedToMode : Prop
  backgroundGeffTiedToMode : Prop
  immirziPerturbationsTiedToMode : Prop
  wardIdentityDerived : Prop

def coupledScaffoldReady (s : PrimordialCoupledCMBSector) : Prop :=
  s.singlePrimordialMode /\
  s.soundSpeedTiedToMode /\
  s.opacityLowETiedToMode /\
  s.backgroundGeffTiedToMode /\
  s.immirziPerturbationsTiedToMode

def derivedCoupledSectorReady (s : PrimordialCoupledCMBSector) : Prop :=
  coupledScaffoldReady s /\
  s.wardIdentityDerived

theorem one_mode_ties_all_cmb_channels
    (s : PrimordialCoupledCMBSector)
    (hMode : s.singlePrimordialMode)
    (hSound : s.soundSpeedTiedToMode)
    (hOpacity : s.opacityLowETiedToMode)
    (hGeff : s.backgroundGeffTiedToMode)
    (hImmirzi : s.immirziPerturbationsTiedToMode) :
    coupledScaffoldReady s := by
  exact And.intro hMode (And.intro hSound (And.intro hOpacity (And.intro hGeff hImmirzi)))

theorem missing_ward_identity_blocks_activation
    (s : PrimordialCoupledCMBSector)
    (_hScaffold : coupledScaffoldReady s)
    (hMissing : Not s.wardIdentityDerived) :
    Not (derivedCoupledSectorReady s) := by
  intro h
  exact hMissing h.right

end P0EFTPrimordialCoupledCMBSectorScaffold
end JanusFormal
