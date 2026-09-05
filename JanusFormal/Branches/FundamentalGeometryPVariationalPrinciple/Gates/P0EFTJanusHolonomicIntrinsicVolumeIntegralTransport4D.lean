import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalHolonomicIntrinsicMetricVolume4D
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Real integral transport in the intrinsic holonomic volume chart

The exact image-volume formula determines the pushforward of the restricted
coordinate measure. This transports real integrals without requiring the
holonomic chart to be injective outside its local domain.
-/

namespace JanusFormal
namespace P0EFTJanusHolonomicIntrinsicVolumeIntegralTransport4D

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusCanonicalHolonomicStereographicOverlap4D
open P0EFTJanusCanonicalHolonomicIntrinsicMetricVolume4D

private abbrev Vector4 := Fin 4 → Real
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The literal intrinsic metric density times Lebesgue coordinate measure. -/
def holonomicIntrinsicCoordinateVolume (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Measure Vector4 :=
  volume.withDensity (fun current => ENNReal.ofReal (localMetricVolumeFactor period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current))

/-- Exact image volumes determine the restricted chart pushforward. -/
theorem holonomicIntrinsicCoordinateVolume_map
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (domain : Set Vector4) (hDomain : MeasurableSet domain)
    (hImageVolume : ∀ subset : Set Vector4, MeasurableSet subset → subset ⊆ domain →
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
        ∫⁻ current in subset, ENNReal.ofReal (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current)) :
    Measure.map patch.coordinateMap ((holonomicIntrinsicCoordinateVolume period hPeriod patch).restrict domain) =
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict (patch.coordinateMap '' domain) := by
  have hChart := patch.coordinateMap_contMDiff.continuous.measurable
  ext target hTarget
  rw [Measure.map_apply hChart hTarget,
    Measure.restrict_apply (hChart hTarget), holonomicIntrinsicCoordinateVolume,
    withDensity_apply _ ((hChart hTarget).inter hDomain), Measure.restrict_apply hTarget]
  rw [← hImageVolume (patch.coordinateMap ⁻¹' target ∩ domain)
    ((hChart hTarget).inter hDomain) inter_subset_right,
    image_preimage_inter]

/-- Continuous real functions have the exact density-weighted coordinate
integral on the image of a measured holonomic domain. -/
theorem holonomicIntrinsicVolume_integral_transport
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (domain : Set Vector4) (hDomain : MeasurableSet domain)
    (hImageVolume : ∀ subset : Set Vector4, MeasurableSet subset → subset ⊆ domain →
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
        ∫⁻ current in subset, ENNReal.ofReal (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current))
    (integrand : EffectiveQuotient period hPeriod → Real) (hIntegrand : Continuous integrand) :
    (∫ point in patch.coordinateMap '' domain, integrand point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ current in domain, localMetricVolumeFactor period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current *
          integrand (patch.coordinateMap current) := by
  rw [← holonomicIntrinsicCoordinateVolume_map period hPeriod patch domain hDomain hImageVolume,
    integral_map_of_stronglyMeasurable patch.coordinateMap_contMDiff.continuous.measurable
      hIntegrand.stronglyMeasurable,
    holonomicIntrinsicCoordinateVolume]
  have hDensity := (localMetricVolumeFactor_contDiff period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch).continuous.measurable.ennreal_ofReal
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hDensity
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
    (fun current => integrand (patch.coordinateMap current)) hDomain]
  apply integral_congr_ae
  filter_upwards [] with current
  rw [ENNReal.toReal_ofReal
    (localMetricVolumeFactor_pos period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current).le]
  rfl

/-- The measured neighborhood may be chosen within the target of the fixed
holonomic local inverse used to extend coordinate tests. -/
theorem exists_holonomicLocalInverse_target_volume_domain
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    ∃ domain : Set Vector4,
      coordinate ∈ domain ∧ IsOpen domain ∧ InjOn patch.coordinateMap domain ∧
      domain ⊆ (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target ∧
      ∀ subset : Set Vector4, MeasurableSet subset → subset ⊆ domain →
        intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
          ∫⁻ current in subset, ENNReal.ofReal (localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current) := by
  obtain ⟨original, hCoordinate, hOpen, hInjective, hVolume⟩ :=
    canonical_holonomic_intrinsic_metric_volume_gate period hPeriod patch coordinate
  refine ⟨original ∩ (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target,
    ⟨hCoordinate, (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_mem_target⟩,
    hOpen.inter (holonomicCoordinateLocalInverse period hPeriod patch coordinate).open_target,
    hInjective.mono inter_subset_left, inter_subset_right, ?_⟩
  intro subset hSubset hInDomain
  exact hVolume subset hSubset (hInDomain.trans inter_subset_left)

/-- Every holonomic coordinate has a neighborhood compatible with its local
inverse and with both exact measure and real integral transport. -/
theorem holonomic_intrinsic_volume_integral_transport_gate
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    ∃ domain : Set Vector4,
      coordinate ∈ domain ∧ IsOpen domain ∧ InjOn patch.coordinateMap domain ∧
      domain ⊆ (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target ∧
      Measure.map patch.coordinateMap ((holonomicIntrinsicCoordinateVolume period hPeriod patch).restrict domain) =
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict (patch.coordinateMap '' domain) ∧
      ∀ integrand : EffectiveQuotient period hPeriod → Real, Continuous integrand →
        (∫ point in patch.coordinateMap '' domain, integrand point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
          ∫ current in domain, localMetricVolumeFactor period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current *
              integrand (patch.coordinateMap current) := by
  obtain ⟨domain, hCoordinate, hOpen, hInjective, hTarget, hVolume⟩ :=
    exists_holonomicLocalInverse_target_volume_domain period hPeriod patch coordinate
  refine ⟨domain, hCoordinate, hOpen, hInjective, hTarget,
    holonomicIntrinsicCoordinateVolume_map period hPeriod patch domain hOpen.measurableSet hVolume,
    ?_⟩
  intro integrand hIntegrand
  exact holonomicIntrinsicVolume_integral_transport period hPeriod patch domain hOpen.measurableSet
    hVolume integrand hIntegrand

end
end P0EFTJanusHolonomicIntrinsicVolumeIntegralTransport4D
end JanusFormal
