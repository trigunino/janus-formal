import JanusFormal.Legacy.P0EFT.Gates.P0EFTGrowthNoFitNumericalExport
import JanusFormal.Legacy.P0EFT.Gates.P0EFTMassShellLapseClosure

namespace JanusFormal
namespace P0EFTFriedmannMatterClosure

set_option autoImplicit false

structure FriedmannMatterClosure where
  friedmannConstraintEncoded : Prop
  massShellFluxEntersMatterDensity : Prop
  omegaM0DerivedFromBranch : Prop
  positiveMatterBranch : Prop
  growthBackgroundMatterClosed : Prop
  fullCosmologyPredictionReady : Prop

def matterBackgroundClosed (f : FriedmannMatterClosure) : Prop :=
  f.friedmannConstraintEncoded /\
  f.massShellFluxEntersMatterDensity /\
  f.omegaM0DerivedFromBranch /\
  f.positiveMatterBranch /\
  f.growthBackgroundMatterClosed

def fullCosmologyReadyAfterFriedmannMatter (f : FriedmannMatterClosure) : Prop :=
  matterBackgroundClosed f /\ f.fullCosmologyPredictionReady

theorem friedmann_budget_closes_matter_background
    (f : FriedmannMatterClosure)
    (hFriedmann : f.friedmannConstraintEncoded)
    (hFlux : f.massShellFluxEntersMatterDensity)
    (hOmega : f.omegaM0DerivedFromBranch)
    (hPositive : f.positiveMatterBranch)
    (hClosed : f.growthBackgroundMatterClosed) :
    matterBackgroundClosed f := by
  exact And.intro hFriedmann
    (And.intro hFlux
      (And.intro hOmega
        (And.intro hPositive hClosed)))

theorem nonpositive_matter_branch_blocks_growth_background
    (f : FriedmannMatterClosure)
    (hMissing : Not f.positiveMatterBranch) :
    Not (matterBackgroundClosed f) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTFriedmannMatterClosure
end JanusFormal
