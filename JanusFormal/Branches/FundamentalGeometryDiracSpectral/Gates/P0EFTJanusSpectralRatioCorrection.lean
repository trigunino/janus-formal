import Mathlib

namespace JanusFormal
namespace P0EFTJanusSpectralRatioCorrection

set_option autoImplicit false

/--
An old scalar-mode interpretation assigned `8*A^2=L^2` to the exact-solution
length `A` and the same throat sphere radius `L`.  The Dirac/LL lock instead
gives `A=L`.  The two statements are incompatible at positive radius.
-/
structure ConflictingAlphaRatioClaims where
  alphaSquaredLength : ℝ
  sphereRadius : ℝ
  sphereRadiusPositive : 0 < sphereRadius
  alphaEqualsSphereRadius : alphaSquaredLength = sphereRadius
  oldScalarRatioClaim :
    8 * alphaSquaredLength ^ 2 = sphereRadius ^ 2

/-- The old and new identifications cannot both describe the same two radii. -/
theorem old_scalar_alpha_ratio_conflicts_with_dirac_lock
    (s : ConflictingAlphaRatioClaims) : False := by
  rw [s.alphaEqualsSphereRadius] at s.oldScalarRatioClaim
  have hSquare : 0 < s.sphereRadius ^ 2 :=
    pow_pos s.sphereRadiusPositive 2
  nlinarith [s.oldScalarRatioClaim]

/--
Consistent reinterpretation: the `1/(2*sqrt(2))` ratio belongs to the compact
circle radius `R1` relative to the sphere radius `L`, while `A=L`.
-/
structure CorrectedRadiusAssignment where
  alphaSquaredLength : ℝ
  sphereRadius : ℝ
  circleRadius : ℝ
  alphaEqualsSphere : alphaSquaredLength = sphereRadius
  compactCircleRatio : 8 * circleRadius ^ 2 = sphereRadius ^ 2

/-- The corrected assignment transports the compact-circle ratio to alpha. -/
theorem corrected_ratio_is_circle_to_alpha
    (s : CorrectedRadiusAssignment) :
    8 * s.circleRadius ^ 2 = s.alphaSquaredLength ^ 2 := by
  rw [s.alphaEqualsSphere]
  exact s.compactCircleRatio

/--
Any documentation or downstream observable using the former scalar ratio must
state explicitly which geometric radius is meant before it is promoted.
-/
structure RatioMigrationStatus where
  oldAlphaRatioReferencesLocated : Prop
  circleRadiusSymbolIntroduced : Prop
  sphereRadiusSymbolIntroduced : Prop
  exactSolutionAlphaMappedToSphereRadius : Prop
  spectralRatioMappedToCircleRadius : Prop
  downstreamEquationsReaudited : Prop


def ratioMigrationClosed (s : RatioMigrationStatus) : Prop :=
  s.oldAlphaRatioReferencesLocated /\
  s.circleRadiusSymbolIntroduced /\
  s.sphereRadiusSymbolIntroduced /\
  s.exactSolutionAlphaMappedToSphereRadius /\
  s.spectralRatioMappedToCircleRadius /\
  s.downstreamEquationsReaudited

end P0EFTJanusSpectralRatioCorrection
end JanusFormal
