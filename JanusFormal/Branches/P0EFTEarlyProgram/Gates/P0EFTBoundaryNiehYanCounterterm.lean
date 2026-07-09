import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTBoundaryCoefficientsLichnerowicz

namespace JanusFormal
namespace P0EFTBoundaryNiehYanCounterterm

set_option autoImplicit false

structure NiehYanCountertermCheck where
  countertermTested : Prop
  cancelsChiralNormalResidue : Prop
  cancelsIdentityResidue : Prop
  generatesGammaFiveCoefficient : Prop
  closesRun1 : Prop

def singleNiehYanSufficient (n : NiehYanCountertermCheck) : Prop :=
  n.countertermTested /\
  n.cancelsChiralNormalResidue /\
  n.cancelsIdentityResidue /\
  n.generatesGammaFiveCoefficient /\
  n.closesRun1

theorem single_nieh_yan_requires_identity_and_gammafive_channels
    (n : NiehYanCountertermCheck)
    (hTested : n.countertermTested)
    (hC : n.cancelsChiralNormalResidue)
    (hI : n.cancelsIdentityResidue)
    (hG : n.generatesGammaFiveCoefficient)
    (hClose : n.closesRun1) :
    singleNiehYanSufficient n := by
  exact And.intro hTested
    (And.intro hC
      (And.intro hI
        (And.intro hG hClose)))

theorem missing_identity_cancellation_blocks_single_nieh_yan
    (n : NiehYanCountertermCheck)
    (hMissing : Not n.cancelsIdentityResidue) :
    Not (singleNiehYanSufficient n) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_gammafive_generation_blocks_single_nieh_yan
    (n : NiehYanCountertermCheck)
    (hMissing : Not n.generatesGammaFiveCoefficient) :
    Not (singleNiehYanSufficient n) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTBoundaryNiehYanCounterterm
end JanusFormal
