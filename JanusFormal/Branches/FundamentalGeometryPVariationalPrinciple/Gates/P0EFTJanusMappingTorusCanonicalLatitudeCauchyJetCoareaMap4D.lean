import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetLocalInverseReduction4D

/-!
# Measure-preserving coarea map for the physical Cauchy jet

The exact spherical coarea theorem is combined with one fundamental time
interval.  The resulting parameter space is

`(S² × latitude angle) × time`.

Its measure is the weighted latitude measure `cos² nu dnu dσ₂` times Lebesgue
measure on one period.  The map

`((u,nu),t) ↦ [(sin nu, cos nu • u), t]`

preserves this measure and the canonical physical Lorentz bulk measure.  On the
supported latitude strip, the pullback of the global Cauchy candidate is exactly
the local Cauchy-jet formula at base `(u,t)` and normal `nu`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCoareaMap4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMeasureToSphereEquatorialCoarea4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalCandidate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetLocalInverseReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1
private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1
private abbrev LatitudeAngle := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Coarea parameter ordering: `((equatorial point, normal angle), time)`. -/
abbrev CanonicalLatitudeCauchyJetCoareaParameter :=
  (StandardSphere2 × Real) × Real

/-- Weighted latitude measure times one fundamental time interval. -/
def canonicalLatitudeCauchyJetCoareaMeasure :
    Measure CanonicalLatitudeCauchyJetCoareaParameter :=
  standardLatitudeParameterMeasure.prod
    (volume.restrict (canonicalLatitudeTimeInterval period))

/-- Standard sphere/time fundamental-domain point associated to one coarea
parameter. -/
def canonicalLatitudeCauchyJetStandardFundamentalMap
    (parameter : CanonicalLatitudeCauchyJetCoareaParameter) :
    StandardSphere3 × Real :=
  (standardEquatorialLatitude parameter.1, parameter.2)

/-- Physical bulk point associated to one coarea parameter. -/
def canonicalLatitudeCauchyJetPhysicalMap
    (parameter : CanonicalLatitudeCauchyJetCoareaParameter) :
    EffectiveQuotient period hPeriod :=
  canonicalLorentzFundamentalDomainMap period hPeriod
    (canonicalLatitudeCauchyJetStandardFundamentalMap parameter)

/-- The weighted latitude map preserves the round sphere surface measure. -/
theorem standardEquatorialLatitude_measurePreserving :
    MeasurePreserving standardEquatorialLatitude
      standardLatitudeParameterMeasure
      ((volume : Measure EuclideanR4).toSphere) :=
  ⟨standardEquatorialLatitude_continuous.measurable,
    standardEquatorialLatitude_weighted_map⟩

local instance standardLatitudeParameterMeasure_isFinite :
    IsFiniteMeasure standardLatitudeParameterMeasure := by
  letI : IsFiniteMeasure
      (Measure.map standardEquatorialLatitude
        standardLatitudeParameterMeasure) := by
    rw [standardEquatorialLatitude_measurePreserving.map_eq]
    infer_instance
  exact Measure.isFiniteMeasure_of_map
    standardEquatorialLatitude_measurePreserving.aemeasurable

/-- Adding the unchanged time coordinate preserves the product measures. -/
theorem canonicalLatitudeCauchyJetStandardFundamentalMap_measurePreserving :
    MeasurePreserving canonicalLatitudeCauchyJetStandardFundamentalMap
      (canonicalLatitudeCauchyJetCoareaMeasure period)
      (canonicalLorentzFundamentalProductMeasure period) := by
  change MeasurePreserving (Prod.map standardEquatorialLatitude id)
    (standardLatitudeParameterMeasure.prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
    ((volume : Measure EuclideanR4).toSphere.prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact MeasurePreserving.prod
    standardEquatorialLatitude_measurePreserving
    (MeasurePreserving.id
      (volume.restrict (canonicalLatitudeTimeInterval period)))

/-- The public fundamental-domain map preserves its source measure and the
physical Lorentz volume by definition of the latter pushforward. -/
theorem canonicalLorentzFundamentalDomainMap_measurePreserving :
    MeasurePreserving
      (canonicalLorentzFundamentalDomainMap period hPeriod)
      (canonicalLorentzFundamentalProductMeasure period)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  refine ⟨(canonicalLorentzFundamentalDomainMap_continuous
    period hPeriod).measurable, ?_⟩
  exact intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap period hPeriod

/-- Exact measure preservation from coarea parameters to the physical bulk. -/
theorem canonicalLatitudeCauchyJetPhysicalMap_measurePreserving :
    MeasurePreserving (canonicalLatitudeCauchyJetPhysicalMap period hPeriod)
      (canonicalLatitudeCauchyJetCoareaMeasure period)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact (canonicalLorentzFundamentalDomainMap_measurePreserving
    period hPeriod).comp
      (canonicalLatitudeCauchyJetStandardFundamentalMap_measurePreserving period)

/-- Reordering a coarea parameter into the local extension parameter. -/
def canonicalLatitudeCauchyJetLocalParameter
    (parameter : CanonicalLatitudeCauchyJetCoareaParameter) :
    CanonicalLatitudeParameter :=
  ((parameter.1.1, parameter.2), parameter.1.2)

/-- On the supported open latitude strip, the coarea physical map is the
physical tubular map. -/
theorem canonicalLatitudeCauchyJetPhysicalMap_eq_tubular
    (parameter : CanonicalLatitudeCauchyJetCoareaParameter)
    (hNormal : parameter.1.2 ∈ LatitudeAngle) :
    canonicalLatitudeCauchyJetPhysicalMap period hPeriod parameter =
      canonicalLatitudeTubularPhysicalMap period hPeriod
        ((parameter.1.1, parameter.2), ⟨parameter.1.2, hNormal⟩) := by
  unfold canonicalLatitudeCauchyJetPhysicalMap
    canonicalLatitudeCauchyJetStandardFundamentalMap
    canonicalLorentzFundamentalDomainMap
    canonicalLatitudeTubularPhysicalMap
    canonicalLatitudeTubularCoverMap
  apply congrArg (mappingTorusMk (sphereData period hPeriod))
  apply MappingTorusCover.ext
  · apply unitThreeSphereHomeomorph.injective
    rfl
  · rfl

namespace CanonicalLatitudeDeckCauchyData

/-- Pullback of the global Cauchy candidate to coarea coordinates. -/
theorem _root_.JanusFormal.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCollarQuotient4D.CanonicalLatitudeDeckCauchyData.globalCandidate_coarea
    (data : CanonicalLatitudeDeckCauchyData period)
    (parameter : CanonicalLatitudeCauchyJetCoareaParameter)
    (hNormal : parameter.1.2 ∈ LatitudeAngle) :
    canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data
        (canonicalLatitudeCauchyJetPhysicalMap period hPeriod parameter) =
      canonicalLatitudeLocalCauchyExtension
        (data.value, data.normal)
        (canonicalLatitudeCauchyJetLocalParameter parameter) := by
  rw [canonicalLatitudeCauchyJetPhysicalMap_eq_tubular
    period hPeriod parameter hNormal]
  exact canonicalLatitudeCauchyJetGlobalCandidate_tubularPhysicalMap
    period hPeriod data
      ((parameter.1.1, parameter.2), ⟨parameter.1.2, hNormal⟩)

end CanonicalLatitudeDeckCauchyData

/-- Almost every coarea parameter lies in the open latitude strip. -/
theorem ae_coarea_normal_mem_latitudeAngle :
    ∀ᵐ parameter ∂canonicalLatitudeCauchyJetCoareaMeasure period,
      parameter.1.2 ∈ LatitudeAngle := by
  unfold canonicalLatitudeCauchyJetCoareaMeasure
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_Ioo.preimage
      (measurable_snd.comp measurable_fst))).2
  have hBase :
      ∀ᵐ parameter ∂((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict LatitudeAngle)),
        parameter.2 ∈ LatitudeAngle := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioo.preimage measurable_snd)).2
    refine Filter.Eventually.of_forall fun _sphere => ?_
    exact ae_restrict_mem measurableSet_Ioo
  have hWeighted :
      ∀ᵐ parameter ∂standardLatitudeParameterMeasure,
        parameter.2 ∈ LatitudeAngle := by
    unfold standardLatitudeParameterMeasure
    exact (withDensity_absolutelyContinuous
      ((volume : Measure EuclideanR3).toSphere.prod
        (volume.restrict LatitudeAngle))
      (fun parameter => realLatitudeWeight parameter.2)) hBase
  filter_upwards [hWeighted] with parameter hParameter
  exact Filter.Eventually.of_forall fun _time => hParameter

/-- Coarea-map certificate. -/
theorem canonicalLatitudeCauchyJetCoareaMap_certificate :
    MeasurePreserving (canonicalLatitudeCauchyJetPhysicalMap period hPeriod)
        (canonicalLatitudeCauchyJetCoareaMeasure period)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      (∀ data : CanonicalLatitudeDeckCauchyData period,
        ∀ᵐ parameter ∂canonicalLatitudeCauchyJetCoareaMeasure period,
          canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data
              (canonicalLatitudeCauchyJetPhysicalMap period hPeriod parameter) =
            canonicalLatitudeLocalCauchyExtension
              (data.value, data.normal)
              (canonicalLatitudeCauchyJetLocalParameter parameter)) := by
  refine ⟨canonicalLatitudeCauchyJetPhysicalMap_measurePreserving
      period hPeriod, ?_⟩
  intro data
  filter_upwards [ae_coarea_normal_mem_latitudeAngle period]
    with parameter hNormal
  exact data.globalCandidate_coarea period hPeriod parameter hNormal

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCoareaMap4D
end JanusFormal
