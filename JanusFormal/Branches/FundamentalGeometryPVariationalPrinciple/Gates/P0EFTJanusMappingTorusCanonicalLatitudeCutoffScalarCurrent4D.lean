import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCutoffScalarCurrent4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalAtlasFrame4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Coordinate representative, in a genuine quotient tangent chart, of the
cutoff Green current. -/
def cutoffLatitudeScalarCurrentCoordinate
    (field test : SmoothQuotientField period hPeriod Real)
    (anchor : MappingTorus (reflectedSphereData period hPeriod))
    (parameter : CanonicalLatitudeParameter) : CoverCoordinates :=
  canonicalLatitudeScalarGreenCurrent period hPeriod field test
      parameter.1 parameter.2 •
    cutoffCanonicalLatitudeNormalCoordinate period hPeriod anchor parameter

/-- Explicit one-coordinate divergence of the cutoff current.  This is not a
global covariant divergence. -/
def cutoffLatitudeScalarCurrentCoordinateDivergence
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  deriv canonicalLatitudeCollarCutoff normal *
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal +
    canonicalLatitudeCollarCutoff normal *
      (canonicalLatitudeValue period hPeriod field base normal *
          canonicalLatitudeScalarEulerResidual period hPeriod massSquared test base normal -
        canonicalLatitudeScalarEulerResidual period hPeriod massSquared field base normal *
          canonicalLatitudeValue period hPeriod test base normal)

theorem cutoffLatitudeScalarCurrentCoordinate_eq_collar
    (field test : SmoothQuotientField period hPeriod Real)
    (anchor : MappingTorus (reflectedSphereData period hPeriod))
    (parameter : CanonicalLatitudeParameter)
    (hNormal : |parameter.2| ≤ 1 / 2) :
    cutoffLatitudeScalarCurrentCoordinate period hPeriod field test anchor parameter =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test
          parameter.1 parameter.2 •
        canonicalLatitudeNormalCoordinate period hPeriod anchor parameter := by
  rw [cutoffLatitudeScalarCurrentCoordinate,
    cutoffCanonicalLatitudeNormalCoordinate_eq_normal period hPeriod anchor parameter hNormal]

theorem cutoffLatitudeScalarCurrentCoordinate_eq_zero_of_one_le_abs
    (field test : SmoothQuotientField period hPeriod Real)
    (anchor : MappingTorus (reflectedSphereData period hPeriod))
    (parameter : CanonicalLatitudeParameter)
    (hNormal : 1 ≤ |parameter.2|) :
    cutoffLatitudeScalarCurrentCoordinate period hPeriod field test anchor parameter = 0 := by
  rw [cutoffLatitudeScalarCurrentCoordinate, cutoffCanonicalLatitudeNormalCoordinate,
    canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs parameter.2 hNormal,
    zero_smul, smul_zero]

theorem cutoffLatitudeScalarCurrent_hasDerivAt
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    HasDerivAt
      (fun coordinate => canonicalLatitudeCollarCutoff coordinate *
        canonicalLatitudeScalarGreenCurrent period hPeriod field test base coordinate)
      (cutoffLatitudeScalarCurrentCoordinateDivergence period hPeriod massSquared
        field test base normal) normal := by
  have hCut : HasDerivAt canonicalLatitudeCollarCutoff
      (deriv canonicalLatitudeCollarCutoff normal) normal :=
    (canonicalLatitudeCollarCutoff.contDiff.differentiable
      (show (∞ : ℕ∞ω) ≠ 0 by simp)).differentiableAt.hasDerivAt
  unfold cutoffLatitudeScalarCurrentCoordinateDivergence
  exact hCut.mul (canonicalLatitudeScalarGreenCurrent_hasDerivAt period hPeriod massSquared
    field test base normal)

theorem cutoffLatitudeScalarCurrentCoordinateDivergence_eq_green
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : |normal| < 1 / 2) :
    cutoffLatitudeScalarCurrentCoordinateDivergence period hPeriod massSquared
        field test base normal =
      canonicalLatitudeValue period hPeriod field base normal *
          canonicalLatitudeScalarEulerResidual period hPeriod massSquared test base normal -
        canonicalLatitudeScalarEulerResidual period hPeriod massSquared field base normal *
          canonicalLatitudeValue period hPeriod test base normal := by
  have hBall : normal ∈ Metric.ball (0 : Real) canonicalLatitudeCollarCutoff.rIn := by
    change dist normal 0 < 1 / 2
    simpa [Real.dist_eq] using hNormal
  have hEventually := canonicalLatitudeCollarCutoff.eventuallyEq_one_of_mem_ball hBall
  have hDeriv : deriv canonicalLatitudeCollarCutoff normal = 0 := by
    rw [hEventually.deriv_eq]
    exact (hasDerivAt_const normal (1 : Real)).deriv
  rw [cutoffLatitudeScalarCurrentCoordinateDivergence, hDeriv, zero_mul, zero_add,
    canonicalLatitudeCollarCutoff_eq_one normal hNormal.le, one_mul]

end
end P0EFTJanusMappingTorusCanonicalLatitudeCutoffScalarCurrent4D
end JanusFormal
