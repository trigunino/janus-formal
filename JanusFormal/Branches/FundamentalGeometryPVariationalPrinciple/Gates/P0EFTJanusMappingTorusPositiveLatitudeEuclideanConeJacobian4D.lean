import Mathlib.MeasureTheory.Function.Jacobian
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeJacobian4D

/-!
# Positive latitude reduced to an Euclidean cone Jacobian

`MeasureTheory.Function.Jacobian` is formulated for maps between normed vector
spaces.  This gate removes `Measure.toSphere` from the remaining latitude
formula and isolates the corresponding four-dimensional cone-volume identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPositiveLatitudeEuclideanConeJacobian4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory Set
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
open P0EFTJanusMappingTorusPositiveLatitudeJacobian4D

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev StandardEquatorialSphere :=
  Metric.sphere (0 : EuclideanR3) 1

private abbrev positiveLatitudeSourceMeasure :
    Measure (StandardEquatorialSphere × Real) :=
  ((volume : Measure EuclideanR3).toSphere).prod
    canonicalLatitudeUnitNormalMeasure

/-- Euclidean cone over the part of `S³` selected by a measurable test set
and by the positive latitude collar. -/
def canonicalPositiveLatitudeCone (set : Set StandardSphere) : Set EuclideanR4 :=
  Set.Ioo (0 : Real) 1 •
    ((↑) '' (set ∩
      (canonicalPositiveLatitudeMap '' canonicalPositiveLatitudeDomain)))

/-- The primitive residual statement.  It is an ordinary four-dimensional
cone Jacobian identity and contains no target `Measure.toSphere`. -/
def CanonicalPositiveLatitudeEuclideanConeJacobianFormula : Prop :=
  ∀ set : Set StandardSphere, MeasurableSet set →
    (∫⁻ parameter in canonicalPositiveLatitudeMap ⁻¹' set,
      canonicalPositiveLatitudeJacobian parameter
        ∂positiveLatitudeSourceMeasure) =
      (4 : ENNReal) *
        (volume : Measure EuclideanR4)
          (canonicalPositiveLatitudeCone set)

/-- API-ready local-chart data for the remaining Euclidean calculation.  The
last two fields are the polar source-measure identification and the elementary
set image identification; the central equality is then supplied by Mathlib's
Jacobian theorem. -/
structure CanonicalPositiveLatitudeEuclideanChartCertificate where
  chartSet : Set StandardSphere → Set EuclideanR4
  chartMap : EuclideanR4 → EuclideanR4
  chartDerivative : EuclideanR4 → EuclideanR4 →L[Real] EuclideanR4
  chartSet_measurable : ∀ set, MeasurableSet set → MeasurableSet (chartSet set)
  chartMap_hasFDerivWithinAt : ∀ set, MeasurableSet set →
    ∀ point ∈ chartSet set,
      HasFDerivWithinAt chartMap (chartDerivative point) (chartSet set) point
  chartMap_injOn : ∀ set, MeasurableSet set →
    Set.InjOn chartMap (chartSet set)
  sourceIntegral_eq_four_chartJacobian : ∀ set, MeasurableSet set →
    (∫⁻ parameter in canonicalPositiveLatitudeMap ⁻¹' set,
      canonicalPositiveLatitudeJacobian parameter
        ∂positiveLatitudeSourceMeasure) =
      (4 : ENNReal) *
        ∫⁻ point in chartSet set,
          ENNReal.ofReal |(chartDerivative point).det|
            ∂(volume : Measure EuclideanR4)
  chartImage_eq_cone : ∀ set, MeasurableSet set →
    chartMap '' chartSet set = canonicalPositiveLatitudeCone set

/-- Mathlib's Euclidean change-of-variables theorem turns a local chart
certificate into the primitive cone formula. -/
theorem euclideanConeJacobianFormula_of_chartCertificate
    (certificate : CanonicalPositiveLatitudeEuclideanChartCertificate) :
    CanonicalPositiveLatitudeEuclideanConeJacobianFormula := by
  intro set hSet
  rw [certificate.sourceIntegral_eq_four_chartJacobian set hSet]
  rw [lintegral_abs_det_fderiv_eq_addHaar_image
    (volume : Measure EuclideanR4)
    (certificate.chartSet_measurable set hSet)
    (certificate.chartMap_hasFDerivWithinAt set hSet)
    (certificate.chartMap_injOn set hSet)]
  rw [certificate.chartImage_eq_cone set hSet]

/-- The Euclidean cone formula is exactly sufficient for the weighted
latitude pushforward formula. -/
theorem canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone
    (hCone : CanonicalPositiveLatitudeEuclideanConeJacobianFormula) :
    CanonicalPositiveLatitudeWeightedMapFormula := by
  unfold CanonicalPositiveLatitudeWeightedMapFormula
  apply Measure.ext
  intro set hSet
  rw [Measure.map_apply canonicalPositiveLatitudeMap_continuous.measurable hSet]
  change positiveLatitudeSourceMeasure.withDensity
      canonicalPositiveLatitudeJacobian
        (canonicalPositiveLatitudeMap ⁻¹' set) = _
  rw [withDensity_apply _
    (canonicalPositiveLatitudeMap_continuous.measurable hSet)]
  rw [Measure.restrict_apply hSet]
  rw [(volume : Measure EuclideanR4).toSphere_apply'
    (hSet.inter canonicalPositiveLatitudeMap_image_measurable)]
  simpa [canonicalPositiveLatitudeCone] using hCone set hSet

/-- Hence the cone Jacobian identity closes the original unweighted sphere
domination as well. -/
theorem canonicalPositiveLatitudeMeasureDomination_of_euclideanCone
    (hCone : CanonicalPositiveLatitudeEuclideanConeJacobianFormula) :
    CanonicalPositiveLatitudeMeasureDomination :=
  canonicalPositiveLatitudeMeasureDomination_of_weightedMapFormula
    (canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone hCone)

/-- And it closes the complete physical coarea package downstream. -/
def canonicalLatitudeCoareaBoundOfEuclideanCone
    (period : Real) (hPeriod : period ≠ 0)
    (hCone : CanonicalPositiveLatitudeEuclideanConeJacobianFormula) :
    CanonicalLatitudeCoareaBound period hPeriod :=
  canonicalLatitudeCoareaBoundOfWeightedMapFormula period hPeriod
    (canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone hCone)

/-- Direct weighted formula from an API-ready Euclidean chart certificate. -/
theorem canonicalPositiveLatitudeWeightedMapFormula_of_chartCertificate
    (certificate : CanonicalPositiveLatitudeEuclideanChartCertificate) :
    CanonicalPositiveLatitudeWeightedMapFormula :=
  canonicalPositiveLatitudeWeightedMapFormula_of_euclideanCone
    (euclideanConeJacobianFormula_of_chartCertificate certificate)

/-- Direct original domination from the Euclidean chart certificate. -/
theorem canonicalPositiveLatitudeMeasureDomination_of_chartCertificate
    (certificate : CanonicalPositiveLatitudeEuclideanChartCertificate) :
    CanonicalPositiveLatitudeMeasureDomination :=
  canonicalPositiveLatitudeMeasureDomination_of_euclideanCone
    (euclideanConeJacobianFormula_of_chartCertificate certificate)

/-- Direct complete physical coarea package from the Euclidean certificate. -/
def canonicalLatitudeCoareaBoundOfEuclideanChartCertificate
    (period : Real) (hPeriod : period ≠ 0)
    (certificate : CanonicalPositiveLatitudeEuclideanChartCertificate) :
    CanonicalLatitudeCoareaBound period hPeriod :=
  canonicalLatitudeCoareaBoundOfEuclideanCone period hPeriod
    (euclideanConeJacobianFormula_of_chartCertificate certificate)

end

end P0EFTJanusMappingTorusPositiveLatitudeEuclideanConeJacobian4D
end JanusFormal
