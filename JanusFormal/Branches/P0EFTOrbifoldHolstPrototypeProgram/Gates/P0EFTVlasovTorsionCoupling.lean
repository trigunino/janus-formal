import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTMassShellLapseClosure

namespace JanusFormal
namespace P0EFTVlasovTorsionCoupling

set_option autoImplicit false

structure VlasovTorsionCoupling where
  spinlessTorsionForceZero : Prop
  spinningTorsionForceDerived : Prop
  spinlessMomentsClosed : Prop
  anisotropicStressClosed : Prop
  lensingGrowthSourcesClosed : Prop

def spinlessVlasovTorsionSafe (v : VlasovTorsionCoupling) : Prop :=
  v.spinlessTorsionForceZero

def fullMatterTorsionClosed (v : VlasovTorsionCoupling) : Prop :=
  v.spinlessTorsionForceZero /\
  v.spinningTorsionForceDerived /\
  v.spinlessMomentsClosed /\
  v.anisotropicStressClosed /\
  v.lensingGrowthSourcesClosed

theorem spinless_torsion_force_absent
    (v : VlasovTorsionCoupling)
    (hZero : v.spinlessTorsionForceZero) :
    spinlessVlasovTorsionSafe v := by
  exact hZero

theorem missing_spinning_force_blocks_full_matter_torsion
    (v : VlasovTorsionCoupling)
    (hMissing : Not v.spinningTorsionForceDerived) :
    Not (fullMatterTorsionClosed v) := by
  intro h
  exact hMissing h.right.left

end P0EFTVlasovTorsionCoupling
end JanusFormal
