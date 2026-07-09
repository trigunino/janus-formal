import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTGrowthKinkMuFunctions

namespace JanusFormal
namespace P0EFTActiveStressAlphaDerivation

set_option autoImplicit false

structure ActiveStressAlphaDerivation where
  activeStressDefinitionEncoded : Prop
  contorsionQuadraticSourceIdentified : Prop
  alphaDefinitionEncoded : Prop
  poissonMuFormLinked : Prop
  contorsionContractionsComputed : Prop
  piMomentClosed : Prop
  alphaJanusDerived : Prop

def alphaDerivationStarted (a : ActiveStressAlphaDerivation) : Prop :=
  a.activeStressDefinitionEncoded /\
  a.contorsionQuadraticSourceIdentified /\
  a.alphaDefinitionEncoded /\
  a.poissonMuFormLinked

def alphaDerivationClosed (a : ActiveStressAlphaDerivation) : Prop :=
  alphaDerivationStarted a /\
  a.contorsionContractionsComputed /\
  a.piMomentClosed /\
  a.alphaJanusDerived

theorem active_stress_defines_alpha_target
    (a : ActiveStressAlphaDerivation)
    (hStress : a.activeStressDefinitionEncoded)
    (hContorsion : a.contorsionQuadraticSourceIdentified)
    (hAlpha : a.alphaDefinitionEncoded)
    (hPoisson : a.poissonMuFormLinked) :
    alphaDerivationStarted a := by
  exact And.intro hStress
    (And.intro hContorsion
      (And.intro hAlpha hPoisson))

theorem missing_contorsion_contractions_blocks_alpha
    (a : ActiveStressAlphaDerivation)
    (hMissing : Not a.contorsionContractionsComputed) :
    Not (alphaDerivationClosed a) := by
  intro h
  exact hMissing h.right.left

theorem missing_pi_moment_blocks_alpha
    (a : ActiveStressAlphaDerivation)
    (hMissing : Not a.piMomentClosed) :
    Not (alphaDerivationClosed a) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTActiveStressAlphaDerivation
end JanusFormal
