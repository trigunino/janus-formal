import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTKappaBetaGeometricDerivation

namespace JanusFormal
namespace P0EFTKappaBetaDerivationCheck

set_option autoImplicit false

structure KappaBetaCheck where
  kappaClosedByNiehYanPin : Prop
  betaDeltaChiFixedByCartanGHYFlux : Prop
  betaAcceptedAsBoundaryResponseRatio : Prop
  betaDerivedAsStandaloneConstant : Prop

def kappaBetaClosedIfRatioAllowed (c : KappaBetaCheck) : Prop :=
  c.kappaClosedByNiehYanPin /\
  c.betaDeltaChiFixedByCartanGHYFlux /\
  c.betaAcceptedAsBoundaryResponseRatio

def kappaBetaClosedAsConstants (c : KappaBetaCheck) : Prop :=
  c.kappaClosedByNiehYanPin /\
  c.betaDeltaChiFixedByCartanGHYFlux /\
  c.betaDerivedAsStandaloneConstant

theorem beta_ratio_interpretation_closes_conditionally
    (c : KappaBetaCheck)
    (hKappa : c.kappaClosedByNiehYanPin)
    (hFlux : c.betaDeltaChiFixedByCartanGHYFlux)
    (hRatio : c.betaAcceptedAsBoundaryResponseRatio) :
    kappaBetaClosedIfRatioAllowed c := by
  exact And.intro hKappa (And.intro hFlux hRatio)

theorem beta_constant_requires_stronger_derivation
    (c : KappaBetaCheck)
    (hMissing : Not c.betaDerivedAsStandaloneConstant) :
    Not (kappaBetaClosedAsConstants c) := by
  intro h
  exact hMissing h.right.right

end P0EFTKappaBetaDerivationCheck
end JanusFormal
