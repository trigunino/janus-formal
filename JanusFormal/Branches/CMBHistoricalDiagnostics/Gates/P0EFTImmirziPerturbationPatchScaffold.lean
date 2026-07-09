namespace JanusFormal
namespace P0EFTImmirziPerturbationPatchScaffold

set_option autoImplicit false

structure ImmirziPerturbationPatchScaffold where
  backgroundDtaudaHooked : Prop
  poissonConstraintHooked : Prop
  momentumConstraintDerived : Prop
  anisotropicStressDerived : Prop
  photonBaryonSlipDerived : Prop

def consistentImmirziPerturbationSector (s : ImmirziPerturbationPatchScaffold) : Prop :=
  s.backgroundDtaudaHooked /\
  s.poissonConstraintHooked /\
  s.momentumConstraintDerived /\
  s.anisotropicStressDerived /\
  s.photonBaryonSlipDerived

def safeToActivateImmirziBackground (s : ImmirziPerturbationPatchScaffold) : Prop :=
  consistentImmirziPerturbationSector s

theorem missing_momentum_constraint_blocks_consistency
    (s : ImmirziPerturbationPatchScaffold)
    (hMissing : Not s.momentumConstraintDerived) :
    Not (consistentImmirziPerturbationSector s) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_shear_stress_blocks_consistency
    (s : ImmirziPerturbationPatchScaffold)
    (hMissing : Not s.anisotropicStressDerived) :
    Not (consistentImmirziPerturbationSector s) := by
  intro h
  exact hMissing h.right.right.right.left

theorem missing_photon_baryon_slip_blocks_consistency
    (s : ImmirziPerturbationPatchScaffold)
    (hMissing : Not s.photonBaryonSlipDerived) :
    Not (consistentImmirziPerturbationSector s) := by
  intro h
  exact hMissing h.right.right.right.right

end P0EFTImmirziPerturbationPatchScaffold
end JanusFormal
