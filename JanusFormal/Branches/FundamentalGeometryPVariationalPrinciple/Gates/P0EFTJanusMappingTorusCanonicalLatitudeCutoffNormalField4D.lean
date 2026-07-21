import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalAtlasFrame4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalAtlasFrame4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A smooth real cutoff equal to one for `|normal| ≤ 1/2` and supported in
`|normal| < 1`, hence away from the latitude poles `±π/2`. -/
def canonicalLatitudeCollarCutoff : ContDiffBump (0 : Real) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem canonicalLatitudeCollarCutoff_eq_one
    (normal : Real) (hNormal : |normal| ≤ 1 / 2) :
    canonicalLatitudeCollarCutoff normal = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  change dist normal 0 ≤ 1 / 2
  simpa [Real.dist_eq] using hNormal

theorem canonicalLatitudeCollarCutoff_eq_zero_of_one_le_abs
    (normal : Real) (hNormal : 1 ≤ |normal|) :
    canonicalLatitudeCollarCutoff normal = 0 := by
  apply ContDiffBump.zero_of_le_dist
  change 1 ≤ dist normal 0
  simpa [Real.dist_eq] using hNormal

theorem canonicalLatitudeCollarCutoff_contDiff :
    ContDiff Real ∞ canonicalLatitudeCollarCutoff :=
  ContDiffBump.contDiff _

/-- Cutoff local coordinate representative of the canonical latitude normal
in a genuine quotient tangent chart.  It is deliberately local: a global
nonzero normal frame is forbidden by the sign monodromy. -/
def cutoffCanonicalLatitudeNormalCoordinate
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter) : CoverCoordinates :=
  canonicalLatitudeCollarCutoff parameter.2 •
    canonicalLatitudeNormalCoordinate period hPeriod anchor parameter

theorem cutoffCanonicalLatitudeNormalCoordinate_eq_normal
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter) (hNormal : |parameter.2| ≤ 1 / 2) :
    cutoffCanonicalLatitudeNormalCoordinate period hPeriod anchor parameter =
      canonicalLatitudeNormalCoordinate period hPeriod anchor parameter := by
  rw [cutoffCanonicalLatitudeNormalCoordinate,
    canonicalLatitudeCollarCutoff_eq_one parameter.2 hNormal, one_smul]

theorem cutoffCanonicalLatitudeNormalCoordinate_contMDiffOn
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffOn canonicalLatitudeParameterModelWithCorners
      𝓘(Real, CoverCoordinates) ∞
      (cutoffCanonicalLatitudeNormalCoordinate period hPeriod anchor)
      (canonicalLatitudeNormalCoordinateDomain period hPeriod anchor) := by
  exact ((canonicalLatitudeCollarCutoff_contDiff.contMDiff.comp contMDiff_snd).contMDiffOn).smul
    (canonicalLatitudeNormalCoordinate_contMDiffOn period hPeriod anchor)

end
end P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
end JanusFormal
