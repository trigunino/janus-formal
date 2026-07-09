import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTBoundaryVolumeSolderClosure

namespace JanusFormal
namespace P0EFTVolumeLambdaDerivation

set_option autoImplicit false

structure VolumeLambdaDerivation where
  discontinuousTetradVolume : Prop
  logDetJumpLocalizedOnSigma : Prop
  traceTorsionLinkedToLogVolume : Prop
  palatiniVariationPerformed : Prop
  factorFourDerived : Prop
  lambdaEqualsMinusFourQT : Prop

def lambdaDerivedFromVolumeSolder (d : VolumeLambdaDerivation) : Prop :=
  d.discontinuousTetradVolume /\
  d.logDetJumpLocalizedOnSigma /\
  d.traceTorsionLinkedToLogVolume /\
  d.palatiniVariationPerformed /\
  d.factorFourDerived /\
  d.lambdaEqualsMinusFourQT

theorem volume_palatini_derivation_closes_lambda
    (d : VolumeLambdaDerivation)
    (hVol : d.discontinuousTetradVolume)
    (hJump : d.logDetJumpLocalizedOnSigma)
    (hTrace : d.traceTorsionLinkedToLogVolume)
    (hPalatini : d.palatiniVariationPerformed)
    (hFour : d.factorFourDerived)
    (hLambda : d.lambdaEqualsMinusFourQT) :
    lambdaDerivedFromVolumeSolder d := by
  exact And.intro hVol
    (And.intro hJump
      (And.intro hTrace
        (And.intro hPalatini
          (And.intro hFour hLambda))))

theorem missing_palatini_variation_blocks_lambda_derivation
    (d : VolumeLambdaDerivation)
    (hMissing : Not d.palatiniVariationPerformed) :
    Not (lambdaDerivedFromVolumeSolder d) := by
  intro h
  exact hMissing h.right.right.right.left

theorem missing_factor_four_blocks_lambda_derivation
    (d : VolumeLambdaDerivation)
    (hMissing : Not d.factorFourDerived) :
    Not (lambdaDerivedFromVolumeSolder d) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0EFTVolumeLambdaDerivation
end JanusFormal
