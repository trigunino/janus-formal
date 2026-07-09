import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4FullActionAssemblyTarget

namespace JanusFormal
namespace P0EFTJanusZ4NonlinearResidualFactorization

set_option autoImplicit false

structure NonlinearResidualFactorization where
  residualPairDeclared : Prop
  commonObstructionExtracted : Prop
  determinantReciprocalWeightUsed : Prop
  plusResidualMatchesObstruction : Prop
  minusResidualMatchesWeightedObstruction : Prop
  obstructionVanishingDerived : Prop

def residualFactorizationReady (r : NonlinearResidualFactorization) : Prop :=
  r.residualPairDeclared /\
  r.commonObstructionExtracted /\
  r.determinantReciprocalWeightUsed /\
  r.plusResidualMatchesObstruction /\
  r.minusResidualMatchesWeightedObstruction

def nonlinearResidualClosed (r : NonlinearResidualFactorization) : Prop :=
  residualFactorizationReady r /\
  r.obstructionVanishingDerived

theorem residual_factorization_reduces_minus_channel
    (r : NonlinearResidualFactorization)
    (h : residualFactorizationReady r) :
    r.minusResidualMatchesWeightedObstruction := by
  exact h.right.right.right.right

theorem factorization_does_not_close_obstruction
    (r : NonlinearResidualFactorization)
    (_h : residualFactorizationReady r)
    (hMissing : Not r.obstructionVanishingDerived) :
    Not (nonlinearResidualClosed r) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4NonlinearResidualFactorization
end JanusFormal
