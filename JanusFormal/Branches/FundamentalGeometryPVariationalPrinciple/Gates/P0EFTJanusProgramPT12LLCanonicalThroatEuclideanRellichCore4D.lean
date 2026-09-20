import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-! # Local Euclidean Rellich core on the actual LL throat -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-- Hilbert coordinate presentation of the three-dimensional throat chart. -/
abbrev CanonicalThroatChartHilbertCoordinates :=
  EuclideanSpace Real (Fin 3)

local instance canonicalThroatChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalThroatChartHilbertCoordinates :=
  borel CanonicalThroatChartHilbertCoordinates

local instance canonicalThroatChartHilbertBorelSpace :
    BorelSpace CanonicalThroatChartHilbertCoordinates where
  measurable_eq := rfl

/-- Fixed continuous linear identification with the throat product chart. -/
def canonicalThroatChartHilbertEquivCoverCoordinates :
    CanonicalThroatChartHilbertCoordinates ≃L[Real]
      ThroatCoverCoordinates :=
  (LinearEquiv.ofFinrankEq
    CanonicalThroatChartHilbertCoordinates ThroatCoverCoordinates (by
      simp [CanonicalThroatChartHilbertCoordinates,
        ThroatCoverCoordinates]))
    |>.toContinuousLinearEquiv

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Image of one actual closed throat partition support in its preferred
three-dimensional chart. -/
def finiteThroatGeneratorPatchCoordinateSupport
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Set ThroatCoverCoordinates :=
  extChartAt throatCoverModelWithCorners patch.1 ''
    finiteThroatGeneratorClosedPatch period hPeriod patch

theorem finiteThroatGeneratorPatchCoordinateSupport_isCompact
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsCompact
      (finiteThroatGeneratorPatchCoordinateSupport
        period hPeriod patch) := by
  apply
    (finiteThroatGeneratorClosedPatch_isCompact
      period hPeriod patch).image_of_continuousOn
  apply (continuousOn_extChartAt patch.1).mono
  intro point hPoint
  rw [extChartAt_source,
    ← finiteThroatGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteThroatGeneratorClosedPatch_subset_openPatch
    period hPeriod patch hPoint

theorem finiteThroatGeneratorPatchCoordinateSupport_measurable
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    MeasurableSet
      (finiteThroatGeneratorPatchCoordinateSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchCoordinateSupport_isCompact
    period hPeriod patch).isClosed.measurableSet

/-- The same compact support in the Euclidean Hilbert presentation. -/
def finiteThroatGeneratorPatchHilbertSupport
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Set CanonicalThroatChartHilbertCoordinates :=
  canonicalThroatChartHilbertEquivCoverCoordinates.symm ''
    finiteThroatGeneratorPatchCoordinateSupport period hPeriod patch

theorem finiteThroatGeneratorPatchHilbertSupport_isCompact
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsCompact
      (finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchCoordinateSupport_isCompact
    period hPeriod patch).image
      canonicalThroatChartHilbertEquivCoverCoordinates.symm.continuous

theorem finiteThroatGeneratorPatchHilbertSupport_measurable
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    MeasurableSet
      (finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchHilbertSupport_isCompact
    period hPeriod patch).isClosed.measurableSet

/-! ## Exact transport of one actual compact throat patch -/

/-- The compact throat patch as a subtype. -/
abbrev FiniteThroatGeneratorPatchDomain
    (patch : FiniteThroatGeneratorPatch period hPeriod) :=
  ↥(finiteThroatGeneratorClosedPatch period hPeriod patch)

/-- Actual throat chart followed by the fixed Hilbert identification. -/
def finiteThroatGeneratorPatchHilbertCoordinate
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    FiniteThroatGeneratorPatchDomain period hPeriod patch →
      CanonicalThroatChartHilbertCoordinates :=
  fun point =>
    canonicalThroatChartHilbertEquivCoverCoordinates.symm
      (extChartAt throatCoverModelWithCorners patch.1 point.1)

theorem finiteThroatGeneratorPatchHilbertCoordinate_continuous
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Continuous
      (finiteThroatGeneratorPatchHilbertCoordinate
        period hPeriod patch) := by
  apply canonicalThroatChartHilbertEquivCoverCoordinates.symm.continuous.comp
  apply ContinuousOn.restrict
  apply (continuousOn_extChartAt patch.1).mono
  intro point hPoint
  rw [extChartAt_source,
    ← finiteThroatGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteThroatGeneratorClosedPatch_subset_openPatch
    period hPeriod patch hPoint

theorem finiteThroatGeneratorPatchHilbertCoordinate_range
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Set.range
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch) =
      finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch := by
  ext coordinate
  constructor
  · rintro ⟨point, rfl⟩
    exact ⟨extChartAt throatCoverModelWithCorners patch.1 point.1,
      ⟨point.1, point.2, rfl⟩, rfl⟩
  · rintro ⟨chartCoordinate, ⟨point, hPoint, rfl⟩, rfl⟩
    exact ⟨⟨point, hPoint⟩, rfl⟩

theorem finiteThroatGeneratorPatchHilbertCoordinate_injective
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Function.Injective
      (finiteThroatGeneratorPatchHilbertCoordinate
        period hPeriod patch) := by
  intro point₁ point₂ hCoordinate
  apply Subtype.ext
  apply (extChartAt throatCoverModelWithCorners patch.1).injOn
  · rw [extChartAt_source,
      ← finiteThroatGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteThroatGeneratorClosedPatch_subset_openPatch
      period hPeriod patch point₁.2
  · rw [extChartAt_source,
      ← finiteThroatGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteThroatGeneratorClosedPatch_subset_openPatch
      period hPeriod patch point₂.2
  · exact canonicalThroatChartHilbertEquivCoverCoordinates.symm.injective
      (by simpa [finiteThroatGeneratorPatchHilbertCoordinate]
        using hCoordinate)

theorem finiteThroatGeneratorPatchHilbertCoordinate_isClosedEmbedding
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Topology.IsClosedEmbedding
      (finiteThroatGeneratorPatchHilbertCoordinate
        period hPeriod patch) := by
  letI : CompactSpace
      (FiniteThroatGeneratorPatchDomain period hPeriod patch) :=
    isCompact_iff_compactSpace.mp
      (finiteThroatGeneratorClosedPatch_isCompact
        period hPeriod patch)
  exact
    (finiteThroatGeneratorPatchHilbertCoordinate_continuous
      period hPeriod patch).isClosedEmbedding
        (finiteThroatGeneratorPatchHilbertCoordinate_injective
          period hPeriod patch)

/-- The actual compact throat patch is homeomorphic to its Hilbert support. -/
def finiteThroatGeneratorPatchHilbertHomeomorph
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    FiniteThroatGeneratorPatchDomain period hPeriod patch ≃ₜ
      ↥(finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchHilbertCoordinate_isClosedEmbedding
      period hPeriod patch).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (finiteThroatGeneratorPatchHilbertCoordinate_range
        period hPeriod patch))

/-- Measurable form of the compact throat chart equivalence. -/
def finiteThroatGeneratorPatchHilbertMeasurableEquiv
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    FiniteThroatGeneratorPatchDomain period hPeriod patch ≃ᵐ
      ↥(finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchHilbertHomeomorph
    period hPeriod patch).toMeasurableEquiv

/-- Canonical throat volume pulled back to the compact patch subtype. -/
def finiteThroatGeneratorPatchCanonicalSourceMeasure
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Measure (FiniteThroatGeneratorPatchDomain period hPeriod patch) :=
  (intrinsicCanonicalThroatVolumeMeasure period hPeriod).comap Subtype.val

theorem finiteThroatGeneratorPatchCanonicalSourceMeasure_map_subtype
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Measure.map Subtype.val
        (finiteThroatGeneratorPatchCanonicalSourceMeasure
          period hPeriod patch) =
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
        (finiteThroatGeneratorClosedPatch period hPeriod patch) := by
  exact map_comap_subtype_coe
    (finiteThroatGeneratorClosedPatch_isCompact
      period hPeriod patch).isClosed.measurableSet _

local instance finiteThroatGeneratorPatchCanonicalSourceMeasure_isFinite
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsFiniteMeasure
      (finiteThroatGeneratorPatchCanonicalSourceMeasure
        period hPeriod patch) := by
  letI := intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  unfold finiteThroatGeneratorPatchCanonicalSourceMeasure
  infer_instance

/-- Exact coordinate pushforward of canonical throat volume on one patch. -/
def finiteThroatGeneratorPatchCanonicalCoordinateMeasure
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    Measure CanonicalThroatChartHilbertCoordinates :=
  (finiteThroatGeneratorPatchCanonicalSourceMeasure
      period hPeriod patch).map
    (finiteThroatGeneratorPatchHilbertCoordinate period hPeriod patch)

local instance finiteThroatGeneratorPatchCanonicalCoordinateMeasure_isFinite
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsFiniteMeasure
      (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch) := by
  unfold finiteThroatGeneratorPatchCanonicalCoordinateMeasure
  infer_instance

theorem finiteThroatGeneratorPatchHilbertCoordinate_measurePreserving
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    MeasurePreserving
      (finiteThroatGeneratorPatchHilbertCoordinate period hPeriod patch)
      (finiteThroatGeneratorPatchCanonicalSourceMeasure
        period hPeriod patch)
      (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch) :=
  (finiteThroatGeneratorPatchHilbertCoordinate_continuous
    period hPeriod patch).measurable.measurePreserving _

theorem finiteThroatGeneratorPatchCanonicalCoordinateMeasure_compl_support
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch
        (finiteThroatGeneratorPatchHilbertSupport
          period hPeriod patch)ᶜ = 0 := by
  rw [finiteThroatGeneratorPatchCanonicalCoordinateMeasure,
    Measure.map_apply
      (finiteThroatGeneratorPatchHilbertCoordinate_continuous
        period hPeriod patch).measurable
      (finiteThroatGeneratorPatchHilbertSupport_measurable
        period hPeriod patch).compl]
  have hPreimage :
      finiteThroatGeneratorPatchHilbertCoordinate period hPeriod patch ⁻¹'
          (finiteThroatGeneratorPatchHilbertSupport
            period hPeriod patch)ᶜ = ∅ := by
    rw [← finiteThroatGeneratorPatchHilbertCoordinate_range]
    simp
  rw [hPreimage, measure_empty]

theorem finiteThroatGeneratorPatchCanonicalCoordinateMeasure_restrict_support
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
        (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch) =
      finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact mem_ae_iff.mpr
    (finiteThroatGeneratorPatchCanonicalCoordinateMeasure_compl_support
      period hPeriod patch)

/-- Finite two-sided domination between canonical throat volume and
Lebesgue volume on one compact chart support. -/
structure FiniteThroatGeneratorPatchCanonicalLebesgueComparison
    (patch : FiniteThroatGeneratorPatch period hPeriod) where
  lebesgueBound : ENNReal
  lebesgueBound_ne_top : lebesgueBound ≠ (⊤ : ENNReal)
  lebesgue_le_canonical :
    (volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
        (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch) ≤
      lebesgueBound •
        finiteThroatGeneratorPatchCanonicalCoordinateMeasure
          period hPeriod patch
  canonicalBound : ENNReal
  canonicalBound_ne_top : canonicalBound ≠ (⊤ : ENNReal)
  canonical_le_lebesgue :
    finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch ≤
      canonicalBound •
        (volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
          (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)

/-- Stronger chart-volume certificate by a continuous positive density. -/
structure FiniteThroatGeneratorPatchCanonicalLebesgueDensity
    (patch : FiniteThroatGeneratorPatch period hPeriod) where
  density : CanonicalThroatChartHilbertCoordinates → NNReal
  density_continuous : Continuous density
  density_pos :
    ∀ coordinate ∈
      finiteThroatGeneratorPatchHilbertSupport period hPeriod patch,
      0 < density coordinate
  coordinateMeasure_eq :
    finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch =
      ((volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
        (finiteThroatGeneratorPatchHilbertSupport
          period hPeriod patch)).withDensity
            fun coordinate => density coordinate

namespace FiniteThroatGeneratorPatchCanonicalLebesgueDensity

/-- Compactness turns a positive continuous density into finite two-sided
measure comparison constants. -/
def toComparison
    {patch : FiniteThroatGeneratorPatch period hPeriod}
    (data : FiniteThroatGeneratorPatchCanonicalLebesgueDensity
      period hPeriod patch) :
    FiniteThroatGeneratorPatchCanonicalLebesgueComparison
      period hPeriod patch := by
  classical
  let support :=
    finiteThroatGeneratorPatchHilbertSupport period hPeriod patch
  let canonical :=
    finiteThroatGeneratorPatchCanonicalCoordinateMeasure
      period hPeriod patch
  let lebesgue :=
    (volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
      support
  by_cases hSupport : support.Nonempty
  · let hMinimumExists :=
      (finiteThroatGeneratorPatchHilbertSupport_isCompact
        period hPeriod patch).exists_isMinOn
          hSupport data.density_continuous.continuousOn
    let minimum := Classical.choose hMinimumExists
    have hMinimumSpec := Classical.choose_spec hMinimumExists
    have hMinimumSupport : minimum ∈ support := hMinimumSpec.1
    have hMinimum : IsMinOn data.density support minimum :=
      hMinimumSpec.2
    let hMaximumExists :=
      (finiteThroatGeneratorPatchHilbertSupport_isCompact
        period hPeriod patch).exists_isMaxOn
          hSupport data.density_continuous.continuousOn
    let maximum := Classical.choose hMaximumExists
    have hMaximumSpec := Classical.choose_spec hMaximumExists
    have hMaximumSupport : maximum ∈ support := hMaximumSpec.1
    have hMaximum : IsMaxOn data.density support maximum :=
      hMaximumSpec.2
    have hMinimumPos : 0 < data.density minimum :=
      data.density_pos minimum hMinimumSupport
    have hLower :
        (data.density minimum : ENNReal) • lebesgue ≤ canonical := by
      rw [show canonical =
          lebesgue.withDensity
            (fun coordinate => data.density coordinate) by
        exact data.coordinateMeasure_eq]
      rw [← withDensity_const]
      apply withDensity_mono
      exact (ae_restrict_mem
        (finiteThroatGeneratorPatchHilbertSupport_measurable
          period hPeriod patch)).mono fun coordinate hCoordinate => by
            have hDensity :
                data.density minimum ≤ data.density coordinate :=
              hMinimum hCoordinate
            change (data.density minimum : ENNReal) ≤
              (data.density coordinate : ENNReal)
            exact ENNReal.coe_le_coe.2 hDensity
    refine
      { lebesgueBound := (data.density minimum : ENNReal)⁻¹
        lebesgueBound_ne_top := by simp [hMinimumPos.ne']
        lebesgue_le_canonical := ?_
        canonicalBound := data.density maximum
        canonicalBound_ne_top := by simp
        canonical_le_lebesgue := ?_ }
    · intro measurableSet
      have hLowerSet := hLower measurableSet
      rw [Measure.smul_apply] at hLowerSet
      rw [Measure.smul_apply]
      calc
        lebesgue measurableSet =
            (data.density minimum : ENNReal)⁻¹ *
              ((data.density minimum : ENNReal) *
                lebesgue measurableSet) := by
              rw [← mul_assoc,
                ENNReal.inv_mul_cancel
                  (by exact_mod_cast hMinimumPos.ne')
                  (by simp),
                one_mul]
        _ ≤ (data.density minimum : ENNReal)⁻¹ *
              canonical measurableSet :=
          mul_le_mul_left' hLowerSet _
    · change canonical ≤
        (data.density maximum : ENNReal) • lebesgue
      rw [show canonical =
          lebesgue.withDensity
            (fun coordinate => data.density coordinate) by
        exact data.coordinateMeasure_eq]
      calc
        lebesgue.withDensity
            (fun coordinate => (data.density coordinate : ENNReal)) ≤
          lebesgue.withDensity
            (fun _ => (data.density maximum : ENNReal)) := by
              apply withDensity_mono
              exact (ae_restrict_mem
                (finiteThroatGeneratorPatchHilbertSupport_measurable
                  period hPeriod patch)).mono
                    fun coordinate hCoordinate => by
                      have hDensity :
                          data.density coordinate ≤
                            data.density maximum :=
                        hMaximum hCoordinate
                      change (data.density coordinate : ENNReal) ≤
                        (data.density maximum : ENNReal)
                      exact ENNReal.coe_le_coe.2 hDensity
        _ = (data.density maximum : ENNReal) • lebesgue :=
          withDensity_const _
  · have hSupportEmpty : support = ∅ :=
      not_nonempty_iff_eq_empty.mp hSupport
    have hLebesgueZero : lebesgue = 0 := by
      simp [lebesgue, hSupportEmpty]
    have hCanonicalZero : canonical = 0 := by
      rw [show canonical =
          lebesgue.withDensity
            (fun coordinate => data.density coordinate) by
        exact data.coordinateMeasure_eq,
        hLebesgueZero]
      exact withDensity_zero_left _
    exact
      { lebesgueBound := 1
        lebesgueBound_ne_top := by simp
        lebesgue_le_canonical := by
          change lebesgue ≤ (1 : ENNReal) • canonical
          simp [hLebesgueZero, hCanonicalZero]
        canonicalBound := 1
        canonicalBound_ne_top := by simp
        canonical_le_lebesgue := by
          change canonical ≤ (1 : ENNReal) • lebesgue
          simp [hLebesgueZero, hCanonicalZero] }

end FiniteThroatGeneratorPatchCanonicalLebesgueDensity

/-- Supported scalar Euclidean `H¹` attached to one actual throat patch. -/
abbrev FiniteThroatGeneratorPatchEuclideanH1
    (patch : FiniteThroatGeneratorPatch period hPeriod) :=
  ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On
    (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertSupport_measurable
      period hPeriod patch))

/-- Ambient scalar `L²` on the three-dimensional Euclidean model. -/
abbrev FiniteThroatGeneratorPatchEuclideanL2 :=
  CanonicalThroatChartHilbertCoordinates →₂[
    (volume : Measure CanonicalThroatChartHilbertCoordinates)] Real

/-- Local supported `H¹ → L²` inclusion for one actual throat patch. -/
def finiteThroatGeneratorPatchEuclideanRellichEmbedding
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    FiniteThroatGeneratorPatchEuclideanH1 period hPeriod patch →L[Real]
      FiniteThroatGeneratorPatchEuclideanL2 :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2
    (E := CanonicalThroatChartHilbertCoordinates)
    (finiteThroatGeneratorPatchHilbertSupport period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertSupport_measurable
      period hPeriod patch)

/-- Euclidean Rellich compactness on every selected actual throat patch. -/
theorem finiteThroatGeneratorPatchEuclideanRellichEmbedding_isCompact
    (patch : FiniteThroatGeneratorPatch period hPeriod) :
    IsCompactOperator
      (finiteThroatGeneratorPatchEuclideanRellichEmbedding
        period hPeriod patch) :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2
    (finiteThroatGeneratorPatchHilbertSupport_isCompact
      period hPeriod patch)
    (finiteThroatGeneratorPatchHilbertSupport_measurable
      period hPeriod patch)

end
end P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
end JanusFormal
