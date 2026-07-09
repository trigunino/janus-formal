import JanusFormal.Legacy.P0EFT.Gates.P0EFTBoundaryRun1CombinedClosure

namespace JanusFormal
namespace P0EFTKappaBetaGeometricDerivation

set_option autoImplicit false

structure KappaBetaDerivation where
  niehYanBoundaryVariationComputed : Prop
  kappaEqualsTwoQADeltaChi : Prop
  cartanGHYBoundaryVariationComputed : Prop
  betaEqualsOrientedFluxRatio : Prop
  betaDeltaChiDenominatorGeometric : Prop

def kappaGeometricallyDerived (d : KappaBetaDerivation) : Prop :=
  d.niehYanBoundaryVariationComputed /\ d.kappaEqualsTwoQADeltaChi

def betaGeometricallyDerived (d : KappaBetaDerivation) : Prop :=
  d.cartanGHYBoundaryVariationComputed /\
  d.betaEqualsOrientedFluxRatio /\
  d.betaDeltaChiDenominatorGeometric

def kappaBetaGeometricallyDerived (d : KappaBetaDerivation) : Prop :=
  kappaGeometricallyDerived d /\ betaGeometricallyDerived d

theorem kappa_derives_from_nieh_yan_boundary_variation
    (d : KappaBetaDerivation)
    (hVar : d.niehYanBoundaryVariationComputed)
    (hKappa : d.kappaEqualsTwoQADeltaChi) :
    kappaGeometricallyDerived d := by
  exact And.intro hVar hKappa

theorem beta_derives_from_cartan_ghy_boundary_variation
    (d : KappaBetaDerivation)
    (hVar : d.cartanGHYBoundaryVariationComputed)
    (hBeta : d.betaEqualsOrientedFluxRatio)
    (hDenom : d.betaDeltaChiDenominatorGeometric) :
    betaGeometricallyDerived d := by
  exact And.intro hVar (And.intro hBeta hDenom)

theorem missing_beta_denominator_geometry_blocks_beta
    (d : KappaBetaDerivation)
    (hMissing : Not d.betaDeltaChiDenominatorGeometric) :
    Not (betaGeometricallyDerived d) := by
  intro h
  exact hMissing h.right.right

end P0EFTKappaBetaGeometricDerivation
end JanusFormal
