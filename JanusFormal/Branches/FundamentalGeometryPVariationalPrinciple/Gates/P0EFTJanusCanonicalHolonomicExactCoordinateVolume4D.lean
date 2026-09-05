import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalHolonomicStereographicInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D

/-! # Exact canonical volume in the concrete holonomic overlap

The time-first linear coordinate identification preserves Lebesgue measure.
It transports Gate571 to the actual inverse transition constructed in Gate573.
The density below remains the determinant of the transported stereographic
matrix; its identification with the intrinsic holonomic metric is separate.
-/

namespace JanusFormal
namespace P0EFTJanusCanonicalHolonomicExactCoordinateVolume4D

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusCanonicalStereographicCoordinateTransport4D
open P0EFTJanusCanonicalHolonomicStereographicInverse4D

private abbrev Coordinates := EuclideanSpace Real (Fin 3) × Real
private abbrev Vector4 := Fin 4 → Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

/-- Reading time first and the three spatial entries next preserves volume. -/
theorem holonomicCoordinateEquiv_measurePreserving :
    MeasurePreserving holonomicCoordinateEquiv
      (volume : Measure Coordinates) (volume : Measure Vector4) := by
  have hSpatial := (PiLp.volume_preserving_ofLp (Fin 3)).prod
    (MeasurePreserving.id (volume : Measure Real))
  have hSwap := Measure.measurePreserving_swap
    (μ := (volume : Measure (Fin 3 → Real))) (ν := (volume : Measure Real))
  have hInsert :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => Real) 0).symm
  have hComposite := hInsert.comp (hSwap.comp hSpatial)
  convert hComposite using 1 <;> try rfl
  funext vector index
  change holonomicVectorCoefficient vector index =
    Fin.insertNth (α := fun _ : Fin 4 => Real) 0 vector.2 (WithLp.ofLp vector.1) index
  rw [Fin.insertNth_zero']
  refine Fin.cases ?_ (fun spatial => ?_) index <;> rfl

/-- The Gate571 metric determinant expressed in time-first holonomic coordinates. -/
def holonomicStereographicTransitionMetricDensity
    (transition : Vector4 → Coordinates) (coordinate : Vector4) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt |(stereographicTransitionLorentzMatrix
    (transition ∘ holonomicCoordinateEquiv) (holonomicCoordinateEquiv.symm coordinate)).det|)

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Exact image volume for a holonomic chart with an actual stereographic transition. -/
theorem holonomicCoordinateMap_image_volume
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (shift : Real) (pole : StandardSphere)
    (transition : Vector4 → Coordinates) (subset : Set Vector4)
    (hSubset : MeasurableSet subset)
    (hDerivative : ∀ coordinate ∈ subset, DifferentiableAt Real transition coordinate)
    (hInjective : InjOn transition subset)
    (hStrip : MapsTo transition subset
      (range (canonicalInteriorStereographicCoordinateInclusion period)))
    (hAgreement : EqOn
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘ transition)
      patch.coordinateMap subset) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
      ∫⁻ coordinate in subset, holonomicStereographicTransitionMetricDensity transition coordinate := by
  let reparametrized := transition ∘ holonomicCoordinateEquiv
  let source := holonomicCoordinateEquiv ⁻¹' subset
  have hSource : MeasurableSet source :=
    hSubset.preimage holonomicCoordinateEquiv.continuous.measurable
  have hReparametrized : ∀ point ∈ source, DifferentiableAt Real reparametrized point := by
    intro point hPoint
    exact (hDerivative _ hPoint).comp point holonomicCoordinateEquiv.differentiableAt
  have hReparametrizedInjective : InjOn reparametrized source := by
    intro first hFirst second hSecond hEqual
    exact holonomicCoordinateEquiv.injective (hInjective hFirst hSecond hEqual)
  have hReparametrizedStrip : reparametrized '' source ⊆
      range (canonicalInteriorStereographicCoordinateInclusion period) := by
    rintro _ ⟨point, hPoint, rfl⟩
    exact hStrip hPoint
  have hImage :
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘ reparametrized) ''
          source = patch.coordinateMap '' subset := by
    apply Subset.antisymm
    · rintro _ ⟨point, hPoint, rfl⟩
      exact ⟨holonomicCoordinateEquiv point, hPoint, (hAgreement hPoint).symm⟩
    · rintro _ ⟨coordinate, hCoordinate, rfl⟩
      refine ⟨holonomicCoordinateEquiv.symm coordinate, ?_, ?_⟩
      · change holonomicCoordinateEquiv (holonomicCoordinateEquiv.symm coordinate) ∈ subset
        rwa [holonomicCoordinateEquiv.apply_symm_apply]
      · change shiftedStereographicPhysicalMapAmbient period hPeriod shift pole
          (transition (holonomicCoordinateEquiv (holonomicCoordinateEquiv.symm coordinate))) = _
        rw [holonomicCoordinateEquiv.apply_symm_apply]
        exact hAgreement hCoordinate
  have hVolume := canonicalVolume_local_metric_coordinate_change period hPeriod shift pole
    reparametrized source hSource hReparametrized hReparametrizedInjective hReparametrizedStrip
  rw [hImage] at hVolume
  rw [hVolume]
  simpa only [source, reparametrized, holonomicStereographicTransitionMetricDensity,
    holonomicCoordinateEquiv.symm_apply_apply] using
    holonomicCoordinateEquiv_measurePreserving.setLIntegral_comp_preimage_emb
      holonomicCoordinateEquiv.toHomeomorph.measurableEmbedding
      (holonomicStereographicTransitionMetricDensity transition) subset

/-- Every holonomic coordinate has a neighborhood on which all measurable
subsets have the exact transported metric volume. -/
theorem canonical_holonomic_exact_coordinate_volume_gate
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    ∃ (shift : Real) (pole : StandardSphere) (domain : Set Vector4)
        (transition : Vector4 → Coordinates),
      coordinate ∈ domain ∧ IsOpen domain ∧ ContDiffOn Real ∞ transition domain ∧
      InjOn transition domain ∧
      MapsTo transition domain (range (canonicalInteriorStereographicCoordinateInclusion period)) ∧
      EqOn (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole ∘ transition)
        patch.coordinateMap domain ∧
      ∀ subset : Set Vector4, MeasurableSet subset → subset ⊆ domain →
        intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
          ∫⁻ current in subset, holonomicStereographicTransitionMetricDensity transition current := by
  obtain ⟨shift, pole, domain, transition, hCoordinate, hOpen, hSmooth,
    hInjective, hStrip, hAgreement⟩ :=
      canonical_holonomic_stereographic_inverse_gate period hPeriod patch coordinate
  refine ⟨shift, pole, domain, transition, hCoordinate, hOpen, hSmooth,
    hInjective, hStrip, hAgreement, ?_⟩
  intro subset hSubset hInDomain
  exact holonomicCoordinateMap_image_volume period hPeriod patch shift pole transition subset
    hSubset (fun current hCurrent =>
      (hSmooth.contDiffAt (hOpen.mem_nhds (hInDomain hCurrent))).differentiableAt (by simp))
    (hInjective.mono hInDomain) (hStrip.mono_left hInDomain) (EqOn.mono hInDomain hAgreement)

end
end P0EFTJanusCanonicalHolonomicExactCoordinateVolume4D
end JanusFormal
