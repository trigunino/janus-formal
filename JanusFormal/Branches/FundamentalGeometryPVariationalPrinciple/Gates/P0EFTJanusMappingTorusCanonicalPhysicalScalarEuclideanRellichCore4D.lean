import RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich
import RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D

/-!
# Euclidean Rellich core in dimension four

The analytic local theorem is now available on the Hilbert coordinate model
`EuclideanSpace ℝ (Fin 4)`: the fixed-support Euclidean `H¹ → L²` inclusion
is compact. Transport from the equivalent product chart model
`CoverCoordinates = ℝ³ × ℝ` and from quotient patches remains a separate
geometric measure-and-localization step.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D

/-- Hilbert coordinate presentation of the four-dimensional chart model. -/
abbrev CanonicalChartHilbertCoordinates :=
  EuclideanSpace Real (Fin 4)

local instance canonicalChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalChartHilbertCoordinates :=
  borel CanonicalChartHilbertCoordinates

local instance canonicalChartHilbertBorelSpace :
    BorelSpace CanonicalChartHilbertCoordinates where
  measurable_eq := rfl

/-- Abstract continuous linear identification with the product chart model
used by the quotient atlas. No measure-preservation claim is bundled into
this norm-equivalence. -/
def canonicalChartHilbertEquivCoverCoordinates :
    CanonicalChartHilbertCoordinates ≃L[Real] CoverCoordinates :=
  (LinearEquiv.ofFinrankEq
    CanonicalChartHilbertCoordinates CoverCoordinates (by
      simp [CanonicalChartHilbertCoordinates, CoverCoordinates]))
    |>.toContinuousLinearEquiv

/-- A compact support in the product chart, transported to Hilbert
coordinates. -/
def coverSupportInCanonicalChartHilbert
    (K : Set CoverCoordinates) :
    Set CanonicalChartHilbertCoordinates :=
  canonicalChartHilbertEquivCoverCoordinates.symm '' K

theorem coverSupportInCanonicalChartHilbert_isCompact
    {K : Set CoverCoordinates}
    (hK : IsCompact K) :
    IsCompact (coverSupportInCanonicalChartHilbert K) :=
  hK.image canonicalChartHilbertEquivCoverCoordinates.symm.continuous

/-- Rellich compactness on every compact measurable subset of the actual
four-dimensional Hilbert coordinate model. -/
theorem canonicalChartHilbert_h1OnToL2_isCompact
    {K : Set CanonicalChartHilbertCoordinates}
    (hK : IsCompact K)
    (hKm : MeasurableSet K) :
    IsCompactOperator
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2
        (E := CanonicalChartHilbertCoordinates) K hKm) :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2
    hK hKm

/-- The Euclidean compact inclusion attached to any compact support coming
from a quotient product chart. -/
theorem coverSupport_hilbertRellich_isCompact
    {K : Set CoverCoordinates}
    (hK : IsCompact K) :
    IsCompactOperator
      (RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2
        (E := CanonicalChartHilbertCoordinates)
        (coverSupportInCanonicalChartHilbert K)
        (coverSupportInCanonicalChartHilbert_isCompact hK).isClosed.measurableSet) :=
  canonicalChartHilbert_h1OnToL2_isCompact
    (coverSupportInCanonicalChartHilbert_isCompact hK)
    (coverSupportInCanonicalChartHilbert_isCompact hK).isClosed.measurableSet

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Image of one actual closed partition support in its fixed product chart. -/
def finiteTangentPatchCoverSupport
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Set CoverCoordinates :=
  extChartAt coverModelWithCorners patch.1 ''
    finiteTangentGeneratorClosedPatch period hPeriod patch

theorem finiteTangentPatchCoverSupport_isCompact
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsCompact (finiteTangentPatchCoverSupport period hPeriod patch) := by
  apply
    (finiteTangentGeneratorClosedPatch_isClosed
      period hPeriod patch).isCompact.image_of_continuousOn
  apply (continuousOn_extChartAt patch.1).mono
  intro point hPoint
  rw [extChartAt_source,
    ← finiteTangentGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod patch hPoint

/-- Compact Hilbert-coordinate support attached to one actual Janus patch. -/
def finiteTangentPatchHilbertSupport
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Set CanonicalChartHilbertCoordinates :=
  coverSupportInCanonicalChartHilbert
    (finiteTangentPatchCoverSupport period hPeriod patch)

theorem finiteTangentPatchHilbertSupport_isCompact
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsCompact (finiteTangentPatchHilbertSupport period hPeriod patch) :=
  coverSupportInCanonicalChartHilbert_isCompact
    (finiteTangentPatchCoverSupport_isCompact period hPeriod patch)

theorem finiteTangentPatchHilbertSupport_measurable
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    MeasurableSet (finiteTangentPatchHilbertSupport period hPeriod patch) :=
  (finiteTangentPatchHilbertSupport_isCompact
    period hPeriod patch).isClosed.measurableSet

/-! ## Exact canonical-measure transport to one compact chart -/

/-- The compact quotient patch as a measured subtype. -/
abbrev FiniteTangentPatchDomain
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  ↥(finiteTangentGeneratorClosedPatch period hPeriod patch)

/-- Actual quotient chart followed by the fixed linear identification with
the Euclidean Hilbert model. -/
def finiteTangentPatchHilbertCoordinate
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchDomain period hPeriod patch →
      CanonicalChartHilbertCoordinates :=
  fun point =>
    canonicalChartHilbertEquivCoverCoordinates.symm
      (extChartAt coverModelWithCorners patch.1 point.1)

theorem finiteTangentPatchHilbertCoordinate_continuous
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Continuous
      (finiteTangentPatchHilbertCoordinate period hPeriod patch) := by
  apply canonicalChartHilbertEquivCoverCoordinates.symm.continuous.comp
  apply ContinuousOn.restrict
  apply (continuousOn_extChartAt patch.1).mono
  intro point hPoint
  rw [extChartAt_source,
    ← finiteTangentGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod patch hPoint

theorem finiteTangentPatchHilbertCoordinate_range
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Set.range (finiteTangentPatchHilbertCoordinate period hPeriod patch) =
      finiteTangentPatchHilbertSupport period hPeriod patch := by
  ext coordinate
  constructor
  · rintro ⟨point, rfl⟩
    exact ⟨extChartAt coverModelWithCorners patch.1 point.1,
      ⟨point.1, point.2, rfl⟩, rfl⟩
  · rintro ⟨chartCoordinate, ⟨point, hPoint, rfl⟩, rfl⟩
    exact ⟨⟨point, hPoint⟩, rfl⟩

theorem finiteTangentPatchHilbertCoordinate_injective
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Function.Injective
      (finiteTangentPatchHilbertCoordinate period hPeriod patch) := by
  intro point₁ point₂ hCoordinate
  apply Subtype.ext
  apply (extChartAt coverModelWithCorners patch.1).injOn
  · rw [extChartAt_source,
      ← finiteTangentGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch point₁.2
  · rw [extChartAt_source,
      ← finiteTangentGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch point₂.2
  · exact canonicalChartHilbertEquivCoverCoordinates.symm.injective
      (by simpa [finiteTangentPatchHilbertCoordinate] using hCoordinate)

theorem finiteTangentPatchHilbertCoordinate_isClosedEmbedding
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Topology.IsClosedEmbedding
      (finiteTangentPatchHilbertCoordinate period hPeriod patch) := by
  letI : CompactSpace (FiniteTangentPatchDomain period hPeriod patch) :=
    isCompact_iff_compactSpace.mp
      (finiteTangentGeneratorClosedPatch_isClosed
        period hPeriod patch).isCompact
  exact
    (finiteTangentPatchHilbertCoordinate_continuous
      period hPeriod patch).isClosedEmbedding
        (finiteTangentPatchHilbertCoordinate_injective
          period hPeriod patch)

/-- The compact quotient patch and its Hilbert-coordinate support are
homeomorphic through the actual quotient chart. -/
def finiteTangentPatchHilbertHomeomorph
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchDomain period hPeriod patch ≃ₜ
      ↥(finiteTangentPatchHilbertSupport period hPeriod patch) :=
  (finiteTangentPatchHilbertCoordinate_isClosedEmbedding
      period hPeriod patch).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr
      (finiteTangentPatchHilbertCoordinate_range
        period hPeriod patch))

/-- Measurable form of the actual compact-patch chart equivalence. -/
def finiteTangentPatchHilbertMeasurableEquiv
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchDomain period hPeriod patch ≃ᵐ
      ↥(finiteTangentPatchHilbertSupport period hPeriod patch) :=
  (finiteTangentPatchHilbertHomeomorph
    period hPeriod patch).toMeasurableEquiv

/-- Canonical quotient volume pulled back to the compact patch subtype. -/
def finiteTangentPatchCanonicalSourceMeasure
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Measure (FiniteTangentPatchDomain period hPeriod patch) :=
  (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).comap Subtype.val

/-- The subtype measure is exactly the canonical quotient volume restricted
to the closed patch; in particular the `comap` above is not the undefined
zero branch. -/
theorem finiteTangentPatchCanonicalSourceMeasure_map_subtype
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Measure.map Subtype.val
        (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch) =
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
        (finiteTangentGeneratorClosedPatch period hPeriod patch) := by
  exact map_comap_subtype_coe
    (finiteTangentGeneratorClosedPatch_isClosed
      period hPeriod patch).measurableSet _

local instance finiteTangentPatchCanonicalSourceMeasure_isFinite
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsFiniteMeasure
      (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch) := by
  letI :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  unfold finiteTangentPatchCanonicalSourceMeasure
  infer_instance

/-- Canonical patch volume written on the compact Hilbert-coordinate
subtype. -/
def finiteTangentPatchCanonicalSupportMeasure
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Measure ↥(finiteTangentPatchHilbertSupport period hPeriod patch) :=
  (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch).map
    (finiteTangentPatchHilbertMeasurableEquiv period hPeriod patch)

local instance finiteTangentPatchCanonicalSupportMeasure_isFinite
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsFiniteMeasure
      (finiteTangentPatchCanonicalSupportMeasure
        period hPeriod patch) := by
  unfold finiteTangentPatchCanonicalSupportMeasure
  infer_instance

/-- The patch chart is exactly measure-preserving for the canonical support
measure defined above. -/
theorem finiteTangentPatchHilbertMeasurableEquiv_measurePreserving
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    MeasurePreserving
      (finiteTangentPatchHilbertMeasurableEquiv period hPeriod patch)
      (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch)
      (finiteTangentPatchCanonicalSupportMeasure
        period hPeriod patch) :=
  (finiteTangentPatchHilbertMeasurableEquiv
    period hPeriod patch).measurable.measurePreserving _

/-- The inverse chart is also exactly measure-preserving. -/
theorem finiteTangentPatchHilbertMeasurableEquiv_symm_measurePreserving
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    MeasurePreserving
      (finiteTangentPatchHilbertMeasurableEquiv
        period hPeriod patch).symm
      (finiteTangentPatchCanonicalSupportMeasure period hPeriod patch)
      (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch) :=
  MeasurePreserving.symm
    (finiteTangentPatchHilbertMeasurableEquiv period hPeriod patch)
    (finiteTangentPatchHilbertMeasurableEquiv_measurePreserving
      period hPeriod patch)

/-- Canonical `L²` space on the quotient patch subtype. -/
abbrev FiniteTangentPatchCanonicalSourceL2
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  FiniteTangentPatchDomain period hPeriod patch →₂[
    finiteTangentPatchCanonicalSourceMeasure period hPeriod patch] Real

/-- Canonical `L²` space on the corresponding Hilbert-coordinate support. -/
abbrev FiniteTangentPatchCanonicalSupportL2
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  ↥(finiteTangentPatchHilbertSupport period hPeriod patch) →₂[
    finiteTangentPatchCanonicalSupportMeasure period hPeriod patch] Real

/-- Exact isometric transport of canonical patch `L²` classes into Hilbert
coordinates. -/
def finiteTangentPatchCanonicalSourceToSupportL2
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchCanonicalSourceL2 period hPeriod patch →ₗᵢ[Real]
      FiniteTangentPatchCanonicalSupportL2 period hPeriod patch :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    (𝕜 := Real) (E := Real) (p := (2 : ENNReal))
    (μ := finiteTangentPatchCanonicalSupportMeasure
      period hPeriod patch)
    (μb := finiteTangentPatchCanonicalSourceMeasure
      period hPeriod patch)
    (f := (finiteTangentPatchHilbertMeasurableEquiv
      period hPeriod patch).symm)
    (finiteTangentPatchHilbertMeasurableEquiv_symm_measurePreserving
      period hPeriod patch)

/-- Exact inverse isometric transport from Hilbert coordinates back to the
canonical quotient patch. -/
def finiteTangentPatchCanonicalSupportToSourceL2
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchCanonicalSupportL2 period hPeriod patch →ₗᵢ[Real]
      FiniteTangentPatchCanonicalSourceL2 period hPeriod patch :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    (𝕜 := Real) (E := Real) (p := (2 : ENNReal))
    (μ := finiteTangentPatchCanonicalSourceMeasure
      period hPeriod patch)
    (μb := finiteTangentPatchCanonicalSupportMeasure
      period hPeriod patch)
    (f := finiteTangentPatchHilbertMeasurableEquiv
      period hPeriod patch)
    (finiteTangentPatchHilbertMeasurableEquiv_measurePreserving
      period hPeriod patch)

theorem finiteTangentPatchCanonicalSupportToSourceL2_leftInverse
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (field : FiniteTangentPatchCanonicalSourceL2
      period hPeriod patch) :
    finiteTangentPatchCanonicalSupportToSourceL2 period hPeriod patch
        (finiteTangentPatchCanonicalSourceToSupportL2
          period hPeriod patch field) =
      field := by
  change
    MeasureTheory.Lp.compMeasurePreserving
        (finiteTangentPatchHilbertMeasurableEquiv period hPeriod patch)
        (finiteTangentPatchHilbertMeasurableEquiv_measurePreserving
          period hPeriod patch)
        (MeasureTheory.Lp.compMeasurePreserving
          (finiteTangentPatchHilbertMeasurableEquiv
            period hPeriod patch).symm
          (finiteTangentPatchHilbertMeasurableEquiv_symm_measurePreserving
            period hPeriod patch) field) =
      field
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply
    field
    (finiteTangentPatchHilbertMeasurableEquiv_symm_measurePreserving
      period hPeriod patch)
    (finiteTangentPatchHilbertMeasurableEquiv_measurePreserving
      period hPeriod patch)]
  convert MeasureTheory.Lp.compMeasurePreserving_id_apply field using 1
  all_goals simp

theorem finiteTangentPatchCanonicalSourceToSupportL2_rightInverse
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (field : FiniteTangentPatchCanonicalSupportL2
      period hPeriod patch) :
    finiteTangentPatchCanonicalSourceToSupportL2 period hPeriod patch
        (finiteTangentPatchCanonicalSupportToSourceL2
          period hPeriod patch field) =
      field := by
  change
    MeasureTheory.Lp.compMeasurePreserving
        (finiteTangentPatchHilbertMeasurableEquiv
          period hPeriod patch).symm
        (finiteTangentPatchHilbertMeasurableEquiv_symm_measurePreserving
          period hPeriod patch)
        (MeasureTheory.Lp.compMeasurePreserving
          (finiteTangentPatchHilbertMeasurableEquiv period hPeriod patch)
          (finiteTangentPatchHilbertMeasurableEquiv_measurePreserving
            period hPeriod patch) field) =
      field
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply
    field
    (finiteTangentPatchHilbertMeasurableEquiv_measurePreserving
      period hPeriod patch)
    (finiteTangentPatchHilbertMeasurableEquiv_symm_measurePreserving
      period hPeriod patch)]
  convert MeasureTheory.Lp.compMeasurePreserving_id_apply field using 1
  all_goals simp

/-- Canonical patch `L²` is linearly isometric to its exact
Hilbert-coordinate presentation. -/
def finiteTangentPatchCanonicalL2Equiv
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchCanonicalSourceL2 period hPeriod patch ≃ₗᵢ[Real]
      FiniteTangentPatchCanonicalSupportL2 period hPeriod patch where
  toLinearEquiv :=
    { toLinearMap :=
        (finiteTangentPatchCanonicalSourceToSupportL2
          period hPeriod patch).toLinearMap
      invFun :=
        finiteTangentPatchCanonicalSupportToSourceL2
          period hPeriod patch
      left_inv :=
        finiteTangentPatchCanonicalSupportToSourceL2_leftInverse
          period hPeriod patch
      right_inv :=
        finiteTangentPatchCanonicalSourceToSupportL2_rightInverse
          period hPeriod patch }
  norm_map' :=
    (finiteTangentPatchCanonicalSourceToSupportL2
      period hPeriod patch).norm_map

/-- Exact coordinate pushforward of the canonical quotient volume on one
actual compact patch. -/
def finiteTangentPatchCanonicalCoordinateMeasure
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Measure CanonicalChartHilbertCoordinates :=
  (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch).map
    (finiteTangentPatchHilbertCoordinate period hPeriod patch)

local instance finiteTangentPatchCanonicalCoordinateMeasure_isFinite
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsFiniteMeasure
      (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch) := by
  unfold finiteTangentPatchCanonicalCoordinateMeasure
  infer_instance

/-- The actual quotient chart preserves the pulled-back canonical measure by
construction; this statement contains no unproved Jacobian assumption. -/
theorem finiteTangentPatchHilbertCoordinate_measurePreserving
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    MeasurePreserving
      (finiteTangentPatchHilbertCoordinate period hPeriod patch)
      (finiteTangentPatchCanonicalSourceMeasure period hPeriod patch)
      (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch) :=
  (finiteTangentPatchHilbertCoordinate_continuous
    period hPeriod patch).measurable.measurePreserving _

/-- The transported canonical measure is carried by the same compact support
used by the Euclidean Rellich theorem. -/
theorem finiteTangentPatchCanonicalCoordinateMeasure_compl_support
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    finiteTangentPatchCanonicalCoordinateMeasure period hPeriod patch
        (finiteTangentPatchHilbertSupport period hPeriod patch)ᶜ = 0 := by
  rw [finiteTangentPatchCanonicalCoordinateMeasure,
    Measure.map_apply
      (finiteTangentPatchHilbertCoordinate_continuous
        period hPeriod patch).measurable
      (finiteTangentPatchHilbertSupport_measurable
        period hPeriod patch).compl]
  have hPreimage :
      finiteTangentPatchHilbertCoordinate period hPeriod patch ⁻¹'
          (finiteTangentPatchHilbertSupport period hPeriod patch)ᶜ =
        ∅ := by
    rw [← finiteTangentPatchHilbertCoordinate_range]
    simp
  rw [hPreimage, measure_empty]

/-- Restricting the transported canonical measure to its compact chart
support changes nothing. -/
theorem finiteTangentPatchCanonicalCoordinateMeasure_restrict_support
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
        (finiteTangentPatchHilbertSupport period hPeriod patch) =
      finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact mem_ae_iff.mpr
    (finiteTangentPatchCanonicalCoordinateMeasure_compl_support
      period hPeriod patch)

/-- Canonical coordinate `L²` space on one compact patch. -/
abbrev FiniteTangentPatchCanonicalCoordinateL2
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  CanonicalChartHilbertCoordinates →₂[
    finiteTangentPatchCanonicalCoordinateMeasure
      period hPeriod patch] Real

/-- Lebesgue `L²` space restricted to the same compact patch support. -/
abbrev FiniteTangentPatchRestrictedLebesgueL2
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  CanonicalChartHilbertCoordinates →₂[
    (volume : Measure CanonicalChartHilbertCoordinates).restrict
      (finiteTangentPatchHilbertSupport period hPeriod patch)] Real

/-- Pullback from canonical chart coordinates to the quotient patch is an
exact linear isometry. -/
def finiteTangentPatchCanonicalCoordinateToSourceL2
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchCanonicalCoordinateL2 period hPeriod patch →ₗᵢ[Real]
      FiniteTangentPatchCanonicalSourceL2 period hPeriod patch :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ
    (𝕜 := Real) (E := Real) (p := (2 : ENNReal))
    (μ := finiteTangentPatchCanonicalSourceMeasure
      period hPeriod patch)
    (μb := finiteTangentPatchCanonicalCoordinateMeasure
      period hPeriod patch)
    (f := finiteTangentPatchHilbertCoordinate period hPeriod patch)
    (finiteTangentPatchHilbertCoordinate_measurePreserving
      period hPeriod patch)

/-- The precise quantitative chart-volume statement needed after exact
topological and measure transport: on the compact support, canonical
coordinate volume and Lebesgue volume dominate each other by finite
constants. This is proof data, not an axiom. -/
structure FiniteTangentPatchCanonicalLebesgueComparison
    (patch : FiniteTangentGeneratorPatch period hPeriod) where
  lebesgueBound : ENNReal
  lebesgueBound_ne_top : lebesgueBound ≠ (⊤ : ENNReal)
  lebesgue_le_canonical :
    (volume : Measure CanonicalChartHilbertCoordinates).restrict
        (finiteTangentPatchHilbertSupport period hPeriod patch) ≤
      lebesgueBound •
        finiteTangentPatchCanonicalCoordinateMeasure
          period hPeriod patch
  canonicalBound : ENNReal
  canonicalBound_ne_top : canonicalBound ≠ (⊤ : ENNReal)
  canonical_le_lebesgue :
    finiteTangentPatchCanonicalCoordinateMeasure period hPeriod patch ≤
      canonicalBound •
        (volume : Measure CanonicalChartHilbertCoordinates).restrict
          (finiteTangentPatchHilbertSupport period hPeriod patch)

/-- A stronger and geometrically natural certificate: the transported
canonical volume has a continuous strictly positive density against
Lebesgue measure on the compact chart support. -/
structure FiniteTangentPatchCanonicalLebesgueDensity
    (patch : FiniteTangentGeneratorPatch period hPeriod) where
  density : CanonicalChartHilbertCoordinates → NNReal
  density_continuous : Continuous density
  density_pos :
    ∀ coordinate ∈
      finiteTangentPatchHilbertSupport period hPeriod patch,
      0 < density coordinate
  coordinateMeasure_eq :
    finiteTangentPatchCanonicalCoordinateMeasure period hPeriod patch =
      ((volume : Measure CanonicalChartHilbertCoordinates).restrict
        (finiteTangentPatchHilbertSupport period hPeriod patch)).withDensity
          fun coordinate => density coordinate

namespace FiniteTangentPatchCanonicalLebesgueDensity

/-- Compactness turns a continuous positive chart density into finite
two-sided measure bounds. -/
def toComparison
    {patch : FiniteTangentGeneratorPatch period hPeriod}
    (data : FiniteTangentPatchCanonicalLebesgueDensity
      period hPeriod patch) :
    FiniteTangentPatchCanonicalLebesgueComparison
      period hPeriod patch := by
  classical
  let support :=
    finiteTangentPatchHilbertSupport period hPeriod patch
  let canonical :=
    finiteTangentPatchCanonicalCoordinateMeasure period hPeriod patch
  let lebesgue :=
    (volume : Measure CanonicalChartHilbertCoordinates).restrict support
  by_cases hSupport : support.Nonempty
  · let hMinimumExists :=
      (finiteTangentPatchHilbertSupport_isCompact
        period hPeriod patch).exists_isMinOn
          hSupport data.density_continuous.continuousOn
    let minimum := Classical.choose hMinimumExists
    have hMinimumSpec := Classical.choose_spec hMinimumExists
    have hMinimumSupport : minimum ∈ support := hMinimumSpec.1
    have hMinimum : IsMinOn data.density support minimum :=
      hMinimumSpec.2
    let hMaximumExists :=
      (finiteTangentPatchHilbertSupport_isCompact
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
        (finiteTangentPatchHilbertSupport_measurable
          period hPeriod patch)).mono fun coordinate hCoordinate => by
            have hDensity :
                data.density minimum ≤ data.density coordinate :=
              hMinimum hCoordinate
            change (data.density minimum : ENNReal) ≤
              (data.density coordinate : ENNReal)
            exact ENNReal.coe_le_coe.2 hDensity
    refine
      { lebesgueBound := (data.density minimum : ENNReal)⁻¹
        lebesgueBound_ne_top := by
          simp [hMinimumPos.ne']
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
                (finiteTangentPatchHilbertSupport_measurable
                  period hPeriod patch)).mono
                    fun coordinate hCoordinate => by
                      have hDensity :
                          data.density coordinate ≤ data.density maximum :=
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

end FiniteTangentPatchCanonicalLebesgueDensity

namespace FiniteTangentPatchCanonicalLebesgueComparison

/-- Mutual finite domination gives the exact bounded change of `L²`
measure used by the local Rellich transport. -/
def coordinateL2EquivRestrictedLebesgue
    {patch : FiniteTangentGeneratorPatch period hPeriod}
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    FiniteTangentPatchCanonicalCoordinateL2 period hPeriod patch ≃L[Real]
      FiniteTangentPatchRestrictedLebesgueL2
        period hPeriod patch :=
  MeasureTheory.Lp.changeMeasureEquiv
    (μ := finiteTangentPatchCanonicalCoordinateMeasure
      period hPeriod patch)
    (ν := (volume : Measure CanonicalChartHilbertCoordinates).restrict
      (finiteTangentPatchHilbertSupport period hPeriod patch))
    (E := Real) (p := (2 : ENNReal))
    comparison.lebesgueBound_ne_top
    comparison.canonicalBound_ne_top
    comparison.lebesgue_le_canonical
    comparison.canonical_le_lebesgue
    (by simp)

/-- Canonical coordinate classes become ambient Lebesgue classes by bounded
measure change followed by extension by zero. -/
def coordinateToAmbientLebesgueL2
    {patch : FiniteTangentGeneratorPatch period hPeriod}
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    FiniteTangentPatchCanonicalCoordinateL2 period hPeriod patch →L[Real]
      (CanonicalChartHilbertCoordinates →₂[
        (volume : Measure CanonicalChartHilbertCoordinates)] Real) :=
  (MeasureTheory.Lp.extendByZeroₗᵢ
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (E := Real) (p := (2 : ENNReal))
      (s := finiteTangentPatchHilbertSupport period hPeriod patch)
      (finiteTangentPatchHilbertSupport_measurable
        period hPeriod patch)).toContinuousLinearMap.comp
    (comparison.coordinateL2EquivRestrictedLebesgue
      period hPeriod).toContinuousLinearMap

/-- An ambient Lebesgue class restricts to the patch and then changes to
canonical coordinate measure. -/
def ambientLebesgueToCoordinateL2
    {patch : FiniteTangentGeneratorPatch period hPeriod}
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    (CanonicalChartHilbertCoordinates →₂[
      (volume : Measure CanonicalChartHilbertCoordinates)] Real) →L[Real]
      FiniteTangentPatchCanonicalCoordinateL2 period hPeriod patch :=
  (comparison.coordinateL2EquivRestrictedLebesgue
      period hPeriod).symm.toContinuousLinearMap.comp
    (MeasureTheory.Lp.changeMeasureL
      (μ := (volume : Measure CanonicalChartHilbertCoordinates))
      (ν := (volume : Measure CanonicalChartHilbertCoordinates).restrict
        (finiteTangentPatchHilbertSupport period hPeriod patch))
      (E := Real) (p := (2 : ENNReal)) (c := 1)
      (by simp)
      (by simpa using
        (Measure.restrict_le_self :
          (volume : Measure CanonicalChartHilbertCoordinates).restrict
              (finiteTangentPatchHilbertSupport period hPeriod patch) ≤
            volume))
      (by simp))

/-- Complete bounded `L²` transport from a Euclidean chart class back to
the actual canonical quotient patch. -/
def ambientLebesgueToCanonicalSourceL2
    {patch : FiniteTangentGeneratorPatch period hPeriod}
    (comparison :
      FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) :
    (CanonicalChartHilbertCoordinates →₂[
      (volume : Measure CanonicalChartHilbertCoordinates)] Real) →L[Real]
      FiniteTangentPatchCanonicalSourceL2 period hPeriod patch :=
  (finiteTangentPatchCanonicalCoordinateToSourceL2
      period hPeriod patch).toContinuousLinearMap.comp
    (comparison.ambientLebesgueToCoordinateL2 period hPeriod)

end FiniteTangentPatchCanonicalLebesgueComparison

/-- Euclidean `H¹` space attached to one actual Janus patch. -/
abbrev FiniteTangentPatchEuclideanH1
    (patch : FiniteTangentGeneratorPatch period hPeriod) :=
  ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On
    (finiteTangentPatchHilbertSupport period hPeriod patch)
    (finiteTangentPatchHilbertSupport_measurable period hPeriod patch))

/-- Euclidean `L²` target attached to one actual Janus patch. -/
abbrev FiniteTangentPatchEuclideanL2
    (_patch : FiniteTangentGeneratorPatch period hPeriod) :=
  CanonicalChartHilbertCoordinates →₂[(volume :
    Measure CanonicalChartHilbertCoordinates)] Real

/-- Euclidean Rellich inclusion attached to one actual finite tangent patch. -/
def finiteTangentPatchEuclideanRellichEmbedding
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    FiniteTangentPatchEuclideanH1 period hPeriod patch →L[Real]
      FiniteTangentPatchEuclideanL2 period hPeriod patch :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2
    (E := CanonicalChartHilbertCoordinates)
    (finiteTangentPatchHilbertSupport period hPeriod patch)
    (finiteTangentPatchHilbertSupport_measurable period hPeriod patch)

/-- Unconditional Euclidean Rellich theorem for every actual finite tangent
patch selected by Janus. -/
theorem finiteTangentPatch_hilbertRellich_isCompact
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsCompactOperator
      (finiteTangentPatchEuclideanRellichEmbedding
        period hPeriod patch) :=
  canonicalChartHilbert_h1OnToL2_isCompact
    (finiteTangentPatchHilbertSupport_isCompact period hPeriod patch)
    (finiteTangentPatchHilbertSupport_measurable period hPeriod patch)

/-- Finite union of all actual patch supports in the common Hilbert model. -/
def finiteAtlasHilbertSupport :
    Set CanonicalChartHilbertCoordinates :=
  ⋃ patch : FiniteTangentGeneratorPatch period hPeriod,
    finiteTangentPatchHilbertSupport period hPeriod patch

theorem finiteAtlasHilbertSupport_isCompact :
    IsCompact (finiteAtlasHilbertSupport period hPeriod) := by
  apply isCompact_iUnion
  exact finiteTangentPatchHilbertSupport_isCompact period hPeriod

theorem finiteAtlasHilbertSupport_measurable :
    MeasurableSet (finiteAtlasHilbertSupport period hPeriod) :=
  (finiteAtlasHilbertSupport_isCompact
    period hPeriod).isClosed.measurableSet

/-- One Euclidean `H¹` space large enough for every localized patch. -/
abbrev FiniteAtlasEuclideanH1 :=
  ↥(RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1On
    (finiteAtlasHilbertSupport period hPeriod)
    (finiteAtlasHilbertSupport_measurable period hPeriod))

/-- Common Euclidean `L²` target for the finite atlas. -/
abbrev FiniteAtlasEuclideanL2 :=
  CanonicalChartHilbertCoordinates →₂[(volume :
    Measure CanonicalChartHilbertCoordinates)] Real

/-- Euclidean Rellich inclusion on the finite union of all patch supports. -/
def finiteAtlasEuclideanRellichEmbedding :
    FiniteAtlasEuclideanH1 period hPeriod →L[Real]
      FiniteAtlasEuclideanL2 :=
  RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.h1OnToL2
    (E := CanonicalChartHilbertCoordinates)
    (finiteAtlasHilbertSupport period hPeriod)
    (finiteAtlasHilbertSupport_measurable period hPeriod)

/-- Rellich compactness on the single support containing the finite atlas. -/
theorem finiteAtlasEuclideanRellichEmbedding_isCompact :
    IsCompactOperator
      (finiteAtlasEuclideanRellichEmbedding period hPeriod) :=
  canonicalChartHilbert_h1OnToL2_isCompact
    (finiteAtlasHilbertSupport_isCompact period hPeriod)
    (finiteAtlasHilbertSupport_measurable period hPeriod)

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D
end JanusFormal
