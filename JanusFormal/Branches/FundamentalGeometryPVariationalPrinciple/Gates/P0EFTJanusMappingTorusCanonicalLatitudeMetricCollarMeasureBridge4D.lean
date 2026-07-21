import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

/-!
# Exact metric measure of the canonical latitude collar
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeMetricCollarMeasureBridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
open P0EFTJanusMappingTorusPositiveLatitudeJacobian4D
open P0EFTJanusMappingTorusPositiveLatitudeRadialPolarJacobian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev StandardEquatorialSphere := Metric.sphere (0 : EuclideanR3) 1
private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : SFinite canonicalPositiveLatitudeJacobianMeasure := by
  unfold canonicalPositiveLatitudeJacobianMeasure
  infer_instance

/-- Reorder the exact Jacobian source as the public collar parameter. -/
def canonicalLatitudeMetricCollarReassociate
    (parameter : (StandardEquatorialSphere × Real) × Real) :
    CanonicalLatitudeCollarParameter :=
  ((parameter.1.1, parameter.2), parameter.1.2)

theorem canonicalLatitudeMetricCollarReassociate_measurable :
    Measurable canonicalLatitudeMetricCollarReassociate := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

/-- The collar measure carrying the proved metric Jacobian `cos²(normal)`. -/
def canonicalLatitudeMetricCollarMeasure (period : Real) :
    Measure CanonicalLatitudeCollarParameter :=
  Measure.map canonicalLatitudeMetricCollarReassociate
    (canonicalPositiveLatitudeJacobianMeasure.prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))

/-- The corresponding positive-latitude piece of the round-sphere/time
fundamental-domain volume. -/
def canonicalPositiveLatitudeTargetProductMeasure (period : Real) :
    Measure (StandardSphere × Real) :=
  (((volume : Measure EuclideanR4).toSphere).restrict
      (canonicalPositiveLatitudeMap '' canonicalPositiveLatitudeDomain)).prod
    (volume.restrict (canonicalLatitudeTimeInterval period))

/-- Exact Jacobian change of variables before taking the quotient. -/
theorem canonicalLatitudeFundamentalMap_map_metricCollarMeasure :
    Measure.map canonicalLatitudeFundamentalMap
        (canonicalLatitudeMetricCollarMeasure period) =
      canonicalPositiveLatitudeTargetProductMeasure period := by
  rw [canonicalLatitudeMetricCollarMeasure, Measure.map_map
    canonicalLatitudeFundamentalMap_continuous.measurable
    canonicalLatitudeMetricCollarReassociate_measurable]
  calc
    Measure.map (canonicalLatitudeFundamentalMap ∘
        canonicalLatitudeMetricCollarReassociate)
        (canonicalPositiveLatitudeJacobianMeasure.prod
          (volume.restrict (canonicalLatitudeTimeInterval period))) =
        Measure.map (Prod.map canonicalPositiveLatitudeMap id)
          (canonicalPositiveLatitudeJacobianMeasure.prod
            (volume.restrict (canonicalLatitudeTimeInterval period))) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun parameter => rfl
    _ = (Measure.map canonicalPositiveLatitudeMap
          canonicalPositiveLatitudeJacobianMeasure).prod
        (volume.restrict (canonicalLatitudeTimeInterval period)) := by
      rw [← Measure.map_prod_map _ _
        canonicalPositiveLatitudeMap_continuous.measurable measurable_id,
        Measure.map_id]
    _ = _ := by
      rw [canonicalPositiveLatitudeWeightedMapFormula_radialPolar]
      rfl

/-- Intrinsic quotient volume restricted at the fundamental-domain level to
the positive canonical latitude collar. -/
def intrinsicCanonicalPositiveLatitudeVolumeMeasure :
    Measure (EffectiveQuotient period hPeriod) :=
  Measure.map (canonicalLatitudeQuotientMap period hPeriod)
    (canonicalPositiveLatitudeTargetProductMeasure period)

/-- The metric collar pushforward is exactly that intrinsic volume piece. -/
theorem map_canonicalLatitudeMetricCollarMeasure_eq_intrinsicPositiveLatitude :
    Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeMetricCollarMeasure period) =
      intrinsicCanonicalPositiveLatitudeVolumeMeasure period hPeriod := by
  calc
    Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeMetricCollarMeasure period) =
        Measure.map (canonicalLatitudeQuotientMap period hPeriod)
          (Measure.map canonicalLatitudeFundamentalMap
            (canonicalLatitudeMetricCollarMeasure period)) := by
      rw [Measure.map_map
        (canonicalLatitudeQuotientMap_continuous period hPeriod).measurable
        canonicalLatitudeFundamentalMap_continuous.measurable]
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun parameter =>
        canonicalLatitudeCollarMap_factorization period hPeriod parameter
    _ = _ := by
      rw [canonicalLatitudeFundamentalMap_map_metricCollarMeasure]
      rfl

private theorem Measure.prod_mono_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} (τ : Measure β) [SFinite τ]
    (hμν : μ ≤ ν) : μ.prod τ ≤ ν.prod τ := by
  rw [Measure.le_iff]
  intro set hSet
  rw [Measure.prod_apply hSet, Measure.prod_apply hSet]
  exact lintegral_mono' hμν le_rfl

/-- The exact collar piece is a submeasure of the complete intrinsic Lorentz
volume; the earlier unweighted collar measure is not equal to this measure. -/
theorem intrinsicCanonicalPositiveLatitudeVolumeMeasure_le_intrinsic :
    intrinsicCanonicalPositiveLatitudeVolumeMeasure period hPeriod ≤
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [intrinsicCanonicalPositiveLatitudeVolumeMeasure,
    intrinsicCanonicalLorentzVolumeMeasure_eq_fundamentalMap]
  apply Measure.map_mono
  · exact Measure.prod_mono_left _ Measure.restrict_le_self
  exact (canonicalLatitudeQuotientMap_continuous period hPeriod).measurable

end
end P0EFTJanusMappingTorusCanonicalLatitudeMetricCollarMeasureBridge4D
end JanusFormal
