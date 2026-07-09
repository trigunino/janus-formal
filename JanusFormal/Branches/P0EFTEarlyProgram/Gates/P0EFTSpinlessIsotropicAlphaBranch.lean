import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTActiveStressAlphaDerivation

namespace JanusFormal
namespace P0EFTSpinlessIsotropicAlphaBranch

set_option autoImplicit false

structure SpinlessIsotropicAlphaBranch where
  spinlessVlasovMatter : Prop
  isotropicReceiverMomentumDistribution : Prop
  piZeroConditionally : Prop
  contorsionCombinationComputed : Prop
  torsionEnergyNormalizationDerived : Prop
  alphaIsoFullyDerived : Prop
  generalAnisotropicBranchClosed : Prop

def isotropicBranchDefined (b : SpinlessIsotropicAlphaBranch) : Prop :=
  b.spinlessVlasovMatter /\
  b.isotropicReceiverMomentumDistribution /\
  b.piZeroConditionally /\
  b.contorsionCombinationComputed

def alphaIsoClosed (b : SpinlessIsotropicAlphaBranch) : Prop :=
  isotropicBranchDefined b /\
  b.torsionEnergyNormalizationDerived /\
  b.alphaIsoFullyDerived

theorem isotropic_spinless_branch_starts_alpha
    (b : SpinlessIsotropicAlphaBranch)
    (hSpinless : b.spinlessVlasovMatter)
    (hIso : b.isotropicReceiverMomentumDistribution)
    (hPi : b.piZeroConditionally)
    (hContorsion : b.contorsionCombinationComputed) :
    isotropicBranchDefined b := by
  exact And.intro hSpinless
    (And.intro hIso
      (And.intro hPi hContorsion))

theorem missing_torsion_energy_normalization_blocks_alpha_iso
    (b : SpinlessIsotropicAlphaBranch)
    (hMissing : Not b.torsionEnergyNormalizationDerived) :
    Not (alphaIsoClosed b) := by
  intro h
  exact hMissing h.right.left

end P0EFTSpinlessIsotropicAlphaBranch
end JanusFormal
