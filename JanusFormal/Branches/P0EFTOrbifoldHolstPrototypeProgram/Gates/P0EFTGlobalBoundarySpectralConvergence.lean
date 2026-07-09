import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTKappaBetaDerivationCheck
import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTBoundaryCoefficientsLichnerowicz

namespace JanusFormal
namespace P0EFTGlobalBoundarySpectralConvergence

set_option autoImplicit false

structure BoundarySpectralConvergence where
  betaAcceptedAsResponseRatio : Prop
  run1BoundaryFactorizationClosed : Prop
  apsRiemannianBoundary : Prop
  run2ZeroModesAbsent : Prop
  apsDomainInvariant : Prop
  etaMod2Zero : Prop

def predictionReadyConditional (c : BoundarySpectralConvergence) : Prop :=
  c.betaAcceptedAsResponseRatio /\
  c.run1BoundaryFactorizationClosed /\
  c.apsRiemannianBoundary /\
  c.run2ZeroModesAbsent /\
  c.apsDomainInvariant /\
  c.etaMod2Zero

theorem run1_run2_give_conditional_prediction_ready
    (c : BoundarySpectralConvergence)
    (hBeta : c.betaAcceptedAsResponseRatio)
    (hRun1 : c.run1BoundaryFactorizationClosed)
    (hAPS : c.apsRiemannianBoundary)
    (hZero : c.run2ZeroModesAbsent)
    (hDomain : c.apsDomainInvariant)
    (hEta : c.etaMod2Zero) :
    predictionReadyConditional c := by
  exact And.intro hBeta
    (And.intro hRun1
      (And.intro hAPS
        (And.intro hZero
          (And.intro hDomain hEta))))

theorem missing_beta_response_blocks_conditional_ready
    (c : BoundarySpectralConvergence)
    (hMissing : Not c.betaAcceptedAsResponseRatio) :
    Not (predictionReadyConditional c) := by
  intro h
  exact hMissing h.left

theorem missing_aps_boundary_blocks_conditional_ready
    (c : BoundarySpectralConvergence)
    (hMissing : Not c.apsRiemannianBoundary) :
    Not (predictionReadyConditional c) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTGlobalBoundarySpectralConvergence
end JanusFormal
