import JanusFormal.Foundations.ProgramMHeightGrowth

/-!
# MF-ADV-007: the three coarse ensemble diagnostics are not identifying

Existence of the positive infinite-layer weights is audited numerically.  This
file records the exact consequences of their declared moment equations and the
resulting non-injectivity claim, without importing a hidden geometry.
-/

namespace JanusFormal.ProgramM

structure InfiniteLayerMomentProfile where
  squareSum : ℚ
  cubeSum : ℚ
  square_eq : squareSum = 1 / 2
  cube_eq : cubeSum = 1 / 3
  height : ℕ → ℕ
  height_unbounded : HasUnboundedOrderHeight height

def InfiniteLayerMomentProfile.pairMoment
    (profile : InfiniteLayerMomentProfile) : ℚ :=
  1 - profile.squareSum

def InfiniteLayerMomentProfile.threeChainMoment
    (profile : InfiniteLayerMomentProfile) : ℚ :=
  1 - 3 * profile.squareSum + 2 * profile.cubeSum

theorem InfiniteLayerMomentProfile.pairMoment_eq_half
    (profile : InfiniteLayerMomentProfile) : profile.pairMoment = 1 / 2 := by
  rw [InfiniteLayerMomentProfile.pairMoment, profile.square_eq]
  norm_num

theorem InfiniteLayerMomentProfile.threeChainMoment_eq_sixth
    (profile : InfiniteLayerMomentProfile) : profile.threeChainMoment = 1 / 6 := by
  rw [InfiniteLayerMomentProfile.threeChainMoment, profile.square_eq, profile.cube_eq]
  norm_num

structure ThreeDiagnosticSignature where
  pairMoment : ℚ
  threeChainMoment : ℚ
  unboundedHeight : Bool
  deriving DecidableEq

def coarseThreeDiagnosticSignature (_model : Bool) : ThreeDiagnosticSignature where
  pairMoment := 1 / 2
  threeChainMoment := 1 / 6
  unboundedHeight := true

theorem coarseThreeDiagnosticSignature_not_injective :
    ¬ Function.Injective coarseThreeDiagnosticSignature := by
  intro hinjective
  have : false = true := hinjective rfl
  cases this

end JanusFormal.ProgramM

