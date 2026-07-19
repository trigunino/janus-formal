import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEmbeddedHypersurface
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D

/-!
# Canonical throat in Gaussian-normal form

This local gate identifies the one-jet at the canonical latitude throat with
spacelike Gaussian-normal data.  It proves the vanishing normal derivative,
second fundamental form and trace, while retaining the opposite signs of the
two normal lifts.  No global EH/GHY integration statement is made.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D
open P0EFTJanusGaussianNormalEHGHYCancellation
open P0EFTJanusGaussianNormalEmbeddedHypersurface

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev LocalMatrix3 :=
  P0EFTJanusGaussianNormalEmbeddedHypersurface.Matrix3

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

/-- Tangential signature in the order time, two sphere directions. -/
def canonicalThroatTangentialSignature (index : Fin 3) : Real :=
  if index = 0 then -1 else 1

/-- The actual latitude collar tangential metric coefficients: the time
coefficient is fixed and the two sphere coefficients scale by `cos(n)²`. -/
def canonicalLatitudeInducedMetric (normal : Real) : LocalMatrix3 :=
  Matrix.diagonal fun index =>
    if index = 0 then -1 else Real.cos normal ^ 2

/-- Induced metric at the canonical throat. -/
def canonicalThroatInducedMetric : LocalMatrix3 :=
  Matrix.diagonal canonicalThroatTangentialSignature

theorem canonicalLatitudeInducedMetric_zero :
    canonicalLatitudeInducedMetric 0 = canonicalThroatInducedMetric := by
  ext row column
  by_cases h : row = column
  · subst column
    simp [canonicalLatitudeInducedMetric, canonicalThroatInducedMetric,
      canonicalThroatTangentialSignature]
  · simp [canonicalLatitudeInducedMetric, canonicalThroatInducedMetric, h]

/-- The latitude tangential metric has zero normal derivative at the throat. -/
theorem canonicalLatitudeInducedMetric_entry_hasDerivAt_zero
    (row column : Fin 3) :
    HasDerivAt
      (fun normal => canonicalLatitudeInducedMetric normal row column)
      (0 : Real) (0 : Real) := by
  by_cases hDiagonal : row = column
  · subst column
    by_cases hTime : row = 0
    · simpa [canonicalLatitudeInducedMetric, hTime] using
        (hasDerivAt_const (x := (0 : Real)) (c := (-1 : Real)))
    · simpa [canonicalLatitudeInducedMetric, hTime, pow_two] using!
        (Real.hasDerivAt_cos 0).mul (Real.hasDerivAt_cos 0)
  · simpa [canonicalLatitudeInducedMetric, hDiagonal] using
      (hasDerivAt_const (x := (0 : Real)) (c := (0 : Real)))

theorem canonicalThroatTangentialSignature_square (index : Fin 3) :
    canonicalThroatTangentialSignature index *
        canonicalThroatTangentialSignature index = 1 := by
  by_cases h : index = 0 <;>
    simp [canonicalThroatTangentialSignature, h]

/-- Gaussian-normal one-jet supplied by the real latitude collar. -/
def canonicalThroatGaussianData (_period : Real) (_hPeriod : _period ≠ 0) :
    GaussianAffineData where
  signature := .spacelike
  inducedMetric := canonicalThroatInducedMetric
  inducedInverse := canonicalThroatInducedMetric
  normalDerivative := 0
  inducedMetric_symmetric := by
    simp [canonicalThroatInducedMetric]
  normalDerivative_symmetric := by simp
  inverse_mul_induced := by
    rw [canonicalThroatInducedMetric, Matrix.diagonal_mul_diagonal]
    ext row column
    by_cases h : row = column
    · subst column
      simp [canonicalThroatTangentialSignature_square]
    · simp [h]
  induced_mul_inverse := by
    rw [canonicalThroatInducedMetric, Matrix.diagonal_mul_diagonal]
    ext row column
    by_cases h : row = column
    · subst column
      simp [canonicalThroatTangentialSignature_square]
    · simp [h]

@[simp]
theorem canonicalThroatGaussianData_normalDerivative :
    (canonicalThroatGaussianData period hPeriod).normalDerivative = 0 :=
  rfl

/-- The genuine collar metric and the affine Gaussian model have the same
tangential one-jet at `n = 0`. -/
theorem canonicalLatitudeMetric_matchesGaussian_oneJet
    (row column : Fin 3) :
    HasDerivAt
      (fun normal => canonicalLatitudeInducedMetric normal row column)
      ((canonicalThroatGaussianData period hPeriod).normalDerivative row column)
      0 := by
  simpa using canonicalLatitudeInducedMetric_entry_hasDerivAt_zero row column

/-- At the throat, the complete block metric is exactly the Gaussian-normal
metric with unit spacelike lapse and zero shift. -/
theorem canonicalLatitudeMetric_zero_eq_gaussian
    (tangent : TangentCoordinate3) :
    gaussianMetric 1 (canonicalLatitudeInducedMetric 0) =
      spacetimeMetric (canonicalThroatGaussianData period hPeriod)
        (hypersurfaceEmbedding tangent) := by
  rw [spacetimeMetric_on_hypersurface,
    canonicalLatitudeInducedMetric_zero]
  rfl

/-- Both oriented second fundamental forms vanish at the canonical throat. -/
theorem canonicalThroat_secondFundamentalForm_zero
    (convention : SecondFundamentalConvention)
    (orientation : NormalOrientation) :
    secondFundamentalForm convention
      (canonicalThroatGaussianData period hPeriod) orientation = 0 := by
  ext row column
  simp [secondFundamentalForm_eq, canonicalThroatGaussianData]

/-- The sign reversal remains exact before using the zero one-jet. -/
theorem canonicalThroat_secondFundamentalForm_lifts_opposite
    (convention : SecondFundamentalConvention) :
    secondFundamentalForm convention
        (canonicalThroatGaussianData period hPeriod) .decreasing =
      -secondFundamentalForm convention
        (canonicalThroatGaussianData period hPeriod) .increasing := by
  rw [canonicalThroat_secondFundamentalForm_zero,
    canonicalThroat_secondFundamentalForm_zero]
  simp

/-- The mean/extrinsic-curvature trace vanishes for either normal lift. -/
theorem canonicalThroat_extrinsicTrace_zero
    (convention : SecondFundamentalConvention)
    (orientation : NormalOrientation) :
    extrinsicTrace convention
      (canonicalThroatGaussianData period hPeriod) orientation = 0 := by
  rw [extrinsicTrace]
  simp [canonicalThroat_secondFundamentalForm_zero, inducedTrace]

/-- Coordinate zero is the actual fixed throat. -/
theorem canonicalLatitudeCollar_zero
    (anchor : EffectiveThroatCover period hPeriod) :
    normalLatitudeCover period hPeriod anchor 0 =
      fixedThroatCoverInclusion period hPeriod anchor :=
  normalLatitudeCover_zero period hPeriod anchor

/-- Deck transport exchanges the two signed latitude lifts. -/
theorem canonicalLatitudeCollar_lifts_opposite
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    normalLatitudeCover period hPeriod ((1 : Int) +ᵥ anchor) normal =
      (1 : Int) +ᵥ normalLatitudeCover period hPeriod anchor (-normal) :=
  normalLatitudeCover_deck_generator_twist period hPeriod anchor normal

/-- The actual latitude normal is the unit spacelike Gaussian normal. -/
theorem canonicalLatitudeNormal_is_unit_spacelike
    (anchor : EffectiveThroatCover period hPeriod) :
    intrinsicCoverLorentzTensor period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor)
        (coverLatitudeNormalVector period hPeriod anchor) = 1 :=
  intrinsicCoverLorentzTensor_latitudeNormal_square period hPeriod anchor

end
end P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D
end JanusFormal
