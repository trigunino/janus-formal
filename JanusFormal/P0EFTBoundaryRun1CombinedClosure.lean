import JanusFormal.P0EFTVolumeLambdaOrientationClosure

namespace JanusFormal
namespace P0EFTBoundaryRun1CombinedClosure

set_option autoImplicit false

structure Run1CombinedClosure where
  lambdaGeometricallyClosed : Prop
  kappaAlgebraicallyClosed : Prop
  betaAlgebraicallyClosed : Prop
  identityResidueZero : Prop
  chiralNormalResidueZero : Prop
  gammaFiveMatchesOrientedNormal : Prop
  kappaGeometricallyDerived : Prop
  betaGeometricallyDerived : Prop

def run1AlgebraicallyClosed (r : Run1CombinedClosure) : Prop :=
  r.lambdaGeometricallyClosed /\
  r.kappaAlgebraicallyClosed /\
  r.betaAlgebraicallyClosed /\
  r.identityResidueZero /\
  r.chiralNormalResidueZero /\
  r.gammaFiveMatchesOrientedNormal

def run1GeometricallyClosed (r : Run1CombinedClosure) : Prop :=
  run1AlgebraicallyClosed r /\
  r.kappaGeometricallyDerived /\
  r.betaGeometricallyDerived

theorem run1_algebra_closes_after_three_substitutions
    (r : Run1CombinedClosure)
    (hLambda : r.lambdaGeometricallyClosed)
    (hKappa : r.kappaAlgebraicallyClosed)
    (hBeta : r.betaAlgebraicallyClosed)
    (hI : r.identityResidueZero)
    (hC : r.chiralNormalResidueZero)
    (hG : r.gammaFiveMatchesOrientedNormal) :
    run1AlgebraicallyClosed r := by
  exact And.intro hLambda
    (And.intro hKappa
      (And.intro hBeta
        (And.intro hI
          (And.intro hC hG))))

theorem missing_kappa_geometry_blocks_run1_geometric_closure
    (r : Run1CombinedClosure)
    (hMissing : Not r.kappaGeometricallyDerived) :
    Not (run1GeometricallyClosed r) := by
  intro h
  exact hMissing h.right.left

theorem missing_beta_geometry_blocks_run1_geometric_closure
    (r : Run1CombinedClosure)
    (hMissing : Not r.betaGeometricallyDerived) :
    Not (run1GeometricallyClosed r) := by
  intro h
  exact hMissing h.right.right

theorem run1_geometric_closure_after_kappa_beta_derivation
    (r : Run1CombinedClosure)
    (hAlg : run1AlgebraicallyClosed r)
    (hKappa : r.kappaGeometricallyDerived)
    (hBeta : r.betaGeometricallyDerived) :
    run1GeometricallyClosed r := by
  exact And.intro hAlg (And.intro hKappa hBeta)

end P0EFTBoundaryRun1CombinedClosure
end JanusFormal
