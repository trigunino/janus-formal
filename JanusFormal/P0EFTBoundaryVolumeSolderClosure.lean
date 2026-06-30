import JanusFormal.P0EFTBoundaryIdentityObstruction

namespace JanusFormal
namespace P0EFTBoundaryVolumeSolderClosure

set_option autoImplicit false

structure VolumeSolderSource where
  logDetRatioEqualsRadionJump : Prop
  contributesOnlyIdentityChannel : Prop
  lambdaFixedByJanusGeometry : Prop
  lambdaCancelsTraceResidue : Prop

structure FullBoundaryLinearSolution where
  niehYanKappaFixedGeometrically : Prop
  cartanGHYBetaFixedGeometrically : Prop
  volumeLambdaFixedGeometrically : Prop
  chiralNormalResidueCancelled : Prop
  gammaFiveChannelMatched : Prop
  identityResidueCancelled : Prop

def volumeSourceClosesIdentity (v : VolumeSolderSource) : Prop :=
  v.logDetRatioEqualsRadionJump /\
  v.contributesOnlyIdentityChannel /\
  v.lambdaFixedByJanusGeometry /\
  v.lambdaCancelsTraceResidue

def fullBoundarySolutionIsGeometric (s : FullBoundaryLinearSolution) : Prop :=
  s.niehYanKappaFixedGeometrically /\
  s.cartanGHYBetaFixedGeometrically /\
  s.volumeLambdaFixedGeometrically /\
  s.chiralNormalResidueCancelled /\
  s.gammaFiveChannelMatched /\
  s.identityResidueCancelled

theorem volume_solder_source_closes_identity_conditionally
    (v : VolumeSolderSource)
    (hLog : v.logDetRatioEqualsRadionJump)
    (hChannel : v.contributesOnlyIdentityChannel)
    (hLambda : v.lambdaFixedByJanusGeometry)
    (hCancel : v.lambdaCancelsTraceResidue) :
    volumeSourceClosesIdentity v := by
  exact And.intro hLog (And.intro hChannel (And.intro hLambda hCancel))

theorem underived_lambda_blocks_pure_volume_closure
    (v : VolumeSolderSource)
    (hMissing : Not v.lambdaFixedByJanusGeometry) :
    Not (volumeSourceClosesIdentity v) := by
  intro h
  exact hMissing h.right.right.left

theorem geometric_kappa_beta_lambda_close_run1_conditionally
    (s : FullBoundaryLinearSolution)
    (hKappa : s.niehYanKappaFixedGeometrically)
    (hBeta : s.cartanGHYBetaFixedGeometrically)
    (hLambda : s.volumeLambdaFixedGeometrically)
    (hC : s.chiralNormalResidueCancelled)
    (hG : s.gammaFiveChannelMatched)
    (hI : s.identityResidueCancelled) :
    fullBoundarySolutionIsGeometric s := by
  exact And.intro hKappa
    (And.intro hBeta
      (And.intro hLambda
        (And.intro hC
          (And.intro hG hI))))

end P0EFTBoundaryVolumeSolderClosure
end JanusFormal
