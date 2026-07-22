import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCoareaMap4D

/-!
# Product-ordered Cauchy coarea coordinates

For estimates it is preferable to order the coarea parameters as

`(boundary base, normal angle)`.

The source measure then factors exactly as the canonical boundary-base measure
times the weighted normal-angle measure.  A measure-preserving reassociation
connects this ordering with the already constructed physical coarea map.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMeasureToSphereEquatorialCoarea4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCoareaMap4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev LatitudeAngle := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
private abbrev EffectiveQuotient :=
  P0EFTJanusMappingTorusQuotient.MappingTorus
    (P0EFTJanusMappingTorusQuotient.reflectedSphereData period hPeriod)

/-- Weighted one-dimensional normal-angle measure. -/
def canonicalLatitudeCauchyJetNormalMeasure : Measure Real :=
  (volume.restrict LatitudeAngle).withDensity realLatitudeWeight

/-- Boundary-base times normal-angle parameter space. -/
abbrev CanonicalLatitudeCauchyJetProductParameter :=
  CanonicalLatitudeBase × Real

/-- Exact product source measure. -/
def canonicalLatitudeCauchyJetProductMeasure :
    Measure CanonicalLatitudeCauchyJetProductParameter :=
  (canonicalLatitudeBaseMeasure period).prod
    canonicalLatitudeCauchyJetNormalMeasure

/-- Reassociate `(S² × time) × normal` to `(S² × normal) × time`. -/
def canonicalLatitudeCauchyJetParameterReassociate
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    CanonicalLatitudeCauchyJetCoareaParameter :=
  ((parameter.1.1, parameter.2), parameter.1.2)

/-- The reassociation preserves the two presentations of the coarea source
measure. -/
theorem canonicalLatitudeCauchyJetParameterReassociate_measurePreserving :
    MeasurePreserving canonicalLatitudeCauchyJetParameterReassociate
      (canonicalLatitudeCauchyJetProductMeasure period)
      (canonicalLatitudeCauchyJetCoareaMeasure period) := by
  unfold canonicalLatitudeCauchyJetProductMeasure
    canonicalLatitudeCauchyJetNormalMeasure
    canonicalLatitudeBaseMeasure
    canonicalLatitudeCauchyJetCoareaMeasure
    standardLatitudeParameterMeasure
  rw [prod_withDensity_right realLatitudeWeight_measurable]
  let firstMeasure : Measure (Metric.sphere (0 : EuclideanR3) 1) :=
    (volume : Measure EuclideanR3).toSphere
  let timeMeasure : Measure Real :=
    volume.restrict (canonicalLatitudeTimeInterval period)
  let normalMeasure : Measure Real :=
    (volume.restrict LatitudeAngle).withDensity realLatitudeWeight
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        ((Metric.sphere (0 : EuclideanR3) 1 × Real) × Real) ≃ₘ
          Metric.sphere (0 : EuclideanR3) 1 × (Real × Real))
      ((firstMeasure.prod timeMeasure).prod normalMeasure)
      (firstMeasure.prod (timeMeasure.prod normalMeasure)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hSwap : MeasurePreserving
      (Prod.map id Prod.swap :
        Metric.sphere (0 : EuclideanR3) 1 × (Real × Real) →
          Metric.sphere (0 : EuclideanR3) 1 × (Real × Real))
      (firstMeasure.prod (timeMeasure.prod normalMeasure))
      (firstMeasure.prod (normalMeasure.prod timeMeasure)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.map_prod_map firstMeasure
      (timeMeasure.prod normalMeasure) measurable_id measurable_swap]
    simp [Measure.prod_swap]
  have hAssocBack : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        Metric.sphere (0 : EuclideanR3) 1 × (Real × Real) ≃ₘ
          ((Metric.sphere (0 : EuclideanR3) 1 × Real) × Real))
      (firstMeasure.prod (normalMeasure.prod timeMeasure))
      ((firstMeasure.prod normalMeasure).prod timeMeasure) :=
    MeasurePreserving.symm MeasurableEquiv.prodAssoc
      ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  simpa [canonicalLatitudeCauchyJetParameterReassociate,
    firstMeasure, timeMeasure, normalMeasure, Function.comp_def] using
    hAssocBack.comp (hSwap.comp hAssoc)

/-- Physical map in product-ordered coarea coordinates. -/
def canonicalLatitudeCauchyJetProductPhysicalMap
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    EffectiveQuotient period hPeriod :=
  canonicalLatitudeCauchyJetPhysicalMap period hPeriod
    (canonicalLatitudeCauchyJetParameterReassociate parameter)

/-- Exact measure preservation from boundary-times-normal coordinates to the
physical bulk. -/
theorem canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving :
    MeasurePreserving
      (canonicalLatitudeCauchyJetProductPhysicalMap period hPeriod)
      (canonicalLatitudeCauchyJetProductMeasure period)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (canonicalLatitudeCauchyJetPhysicalMap_measurePreserving period hPeriod).comp
    (canonicalLatitudeCauchyJetParameterReassociate_measurePreserving period)

namespace CanonicalLatitudeDeckCauchyData

/-- Pullback of the global Cauchy candidate in product-ordered coordinates. -/
theorem globalCandidate_productCoarea
    (data : CanonicalLatitudeDeckCauchyData period)
    (parameter : CanonicalLatitudeCauchyJetProductParameter)
    (hNormal : parameter.2 ∈ LatitudeAngle) :
    canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data
        (canonicalLatitudeCauchyJetProductPhysicalMap
          period hPeriod parameter) =
      canonicalLatitudeLocalCauchyExtension
        (data.value, data.normal) parameter := by
  exact data.globalCandidate_coarea period hPeriod
    (canonicalLatitudeCauchyJetParameterReassociate parameter) hNormal

end CanonicalLatitudeDeckCauchyData

/-- Almost every product parameter lies in the supported normal strip. -/
theorem ae_productCoarea_normal_mem_latitudeAngle :
    ∀ᵐ parameter ∂canonicalLatitudeCauchyJetProductMeasure period,
      parameter.2 ∈ LatitudeAngle := by
  unfold canonicalLatitudeCauchyJetProductMeasure
    canonicalLatitudeCauchyJetNormalMeasure
  rw [Measure.prod_ae_iff]
  filter_upwards [] with base
  exact (Measure.withDensity_absolutelyContinuous
    (volume.restrict LatitudeAngle) realLatitudeWeight)
      (ae_restrict_mem measurableSet_Ioo)

/-- Product-coarea certificate. -/
theorem canonicalLatitudeCauchyJetProductCoarea_certificate :
    MeasurePreserving
        (canonicalLatitudeCauchyJetProductPhysicalMap period hPeriod)
        (canonicalLatitudeCauchyJetProductMeasure period)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      (∀ data : CanonicalLatitudeDeckCauchyData period,
        ∀ᵐ parameter ∂canonicalLatitudeCauchyJetProductMeasure period,
          canonicalLatitudeCauchyJetGlobalCandidate period hPeriod data
              (canonicalLatitudeCauchyJetProductPhysicalMap
                period hPeriod parameter) =
            canonicalLatitudeLocalCauchyExtension
              (data.value, data.normal) parameter) := by
  refine ⟨canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving
      period hPeriod, ?_⟩
  intro data
  filter_upwards [ae_productCoarea_normal_mem_latitudeAngle period]
    with parameter hNormal
  exact data.globalCandidate_productCoarea
    period hPeriod parameter hNormal

end
end P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
end JanusFormal
