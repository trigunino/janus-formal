import JanusFormal.P0EFTBoundaryNiehYanCounterterm

namespace JanusFormal
namespace P0EFTBoundaryCartanGHYConversion

set_option autoImplicit false

structure CartanGHYConversion where
  conversionTermTested : Prop
  generatesGammaFiveChannel : Prop
  cancelsIdentityResidue : Prop
  niehYanCancelsChiralNormalResidue : Prop
  closesRun1 : Prop

def cartanGHYPlusNiehYanCloses (c : CartanGHYConversion) : Prop :=
  c.conversionTermTested /\
  c.generatesGammaFiveChannel /\
  c.cancelsIdentityResidue /\
  c.niehYanCancelsChiralNormalResidue /\
  c.closesRun1

theorem cartan_ghy_needs_identity_cancellation
    (c : CartanGHYConversion)
    (hTested : c.conversionTermTested)
    (hG : c.generatesGammaFiveChannel)
    (hI : c.cancelsIdentityResidue)
    (hNY : c.niehYanCancelsChiralNormalResidue)
    (hClose : c.closesRun1) :
    cartanGHYPlusNiehYanCloses c := by
  exact And.intro hTested
    (And.intro hG
      (And.intro hI
        (And.intro hNY hClose)))

theorem missing_identity_channel_blocks_cartan_ghy_completion
    (c : CartanGHYConversion)
    (hMissing : Not c.cancelsIdentityResidue) :
    Not (cartanGHYPlusNiehYanCloses c) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTBoundaryCartanGHYConversion
end JanusFormal
