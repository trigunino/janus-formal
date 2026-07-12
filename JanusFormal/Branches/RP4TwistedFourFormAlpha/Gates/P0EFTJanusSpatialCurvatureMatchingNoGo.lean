import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpatialCurvatureMatchingNoGo

set_option autoImplicit false

/-- Spatial scalar curvature of a normalized three-dimensional `k = -1` FLRW slice. -/
noncomputable def openFLRWSpatialScalar (scale : ℝ) : ℝ :=
  -6 / scale ^ 2

/-- Spatial scalar curvature of a round three-sphere/projective quotient slice. -/
noncomputable def roundProjectiveSpatialScalar (radius : ℝ) : ℝ :=
  6 / radius ^ 2

/--
A positive-radius open FLRW slice and a positive-radius round projective slice
have opposite scalar-curvature signs.  Therefore the entire three-dimensional
bounce slice of the published `k = -1` exact solution cannot be identified
isometrically with a round `S3/RP3` throat slice merely by setting their radii
equal.
-/
theorem whole_slice_round_matching_is_impossible
    (flrwScale projectiveRadius : ℝ)
    (hFLRW : 0 < flrwScale)
    (hProjective : 0 < projectiveRadius) :
    openFLRWSpatialScalar flrwScale ≠
      roundProjectiveSpatialScalar projectiveRadius := by
  have hOpenNeg : openFLRWSpatialScalar flrwScale < 0 := by
    unfold openFLRWSpatialScalar
    exact div_neg_of_neg_of_pos (by norm_num) (pow_pos hFLRW 2)
  have hRoundPos : 0 < roundProjectiveSpatialScalar projectiveRadius := by
    unfold roundProjectiveSpatialScalar
    exact div_pos (by norm_num) (pow_pos hProjective 2)
  exact ne_of_lt (lt_trans hOpenNeg hRoundPos)

/--
The viable matching object is therefore a finite spherical boundary (or a null
world-volume) with its own junction conditions, not an isometry of the complete
spatial slices.
-/
structure FiniteBoundaryMatchingRequirement where
  publishedOpenFLRWSliceTracked : Prop
  roundProjectiveSliceTracked : Prop
  wholeSliceIdentificationRejected : Prop
  finiteSphericalBoundaryChosen : Prop
  firstFundamentalFormMatched : Prop
  nullOrSecondFundamentalFormLawDerived : Prop


def finiteBoundaryMatchingReady
    (g : FiniteBoundaryMatchingRequirement) : Prop :=
  g.publishedOpenFLRWSliceTracked /\
  g.roundProjectiveSliceTracked /\
  g.wholeSliceIdentificationRejected /\
  g.finiteSphericalBoundaryChosen /\
  g.firstFundamentalFormMatched /\
  g.nullOrSecondFundamentalFormLawDerived

end P0EFTJanusSpatialCurvatureMatchingNoGo
end JanusFormal
