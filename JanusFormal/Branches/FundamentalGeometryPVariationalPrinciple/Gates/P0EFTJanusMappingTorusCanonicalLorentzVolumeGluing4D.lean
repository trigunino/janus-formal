import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Canonical Lorentz-volume gluing contract on the effective D8 quotient

Mathlib currently has no manifold density bundle or construction of the
canonical measure of a varying pseudo-Riemannian metric.  For the present
intrinsic metric the geometry is nevertheless explicit: Mathlib's canonical
round-sphere surface measure is multiplied by Lebesgue measure on one time
period and pushed to the mapping-torus quotient.  Certified Lorentz frames
then instantiate the finite density atlas and its overlap laws.

The overlap law is sufficient: disjointing the finite cover constructs a
finite, nonzero global measure.  Its restriction to every chart is the stated
local metric volume, so the construction is independent of the disjointing
order and can be consumed by the frame-free scalar action.  No Dirac or zero
measure is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicScalarAction4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

/-- A symmetric fundamental interval, independent of the sign convention for
the translation period. -/
private def fundamentalTimeInterval : Set Real :=
  Set.Ioc (min 0 period) (max 0 period)

/-- Surface measure on the round unit three-sphere times Lebesgue measure on
one fundamental time interval.  `Measure.toSphere` is Mathlib's polar-change
construction of the genuine surface measure, rather than ambient measure
restricted to the sphere. -/
private def fundamentalProductMeasure : Measure (StandardSphere × Real) :=
  ((volume : Measure EuclideanR4).toSphere).prod
    (volume.restrict (fundamentalTimeInterval period))

/-- Map one round-sphere/time fundamental domain to the actual mapping-torus
quotient. -/
private def fundamentalDomainMap (point : StandardSphere × Real) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    ((coverHomeomorphProd (sphereData period hPeriod)).symm
      (unitThreeSphereHomeomorph.symm point.1, point.2))

private theorem fundamentalDomainMap_continuous :
    Continuous (fundamentalDomainMap period hPeriod) := by
  have hProduct : Continuous
      (fun point : StandardSphere × Real =>
        (unitThreeSphereHomeomorph.symm point.1, point.2)) :=
    (unitThreeSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (sphereData period hPeriod)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (sphereData period hPeriod)).symm.continuous.comp hProduct)

private theorem fundamentalProductMeasure_isFinite :
    IsFiniteMeasure (fundamentalProductMeasure period) := by
  unfold fundamentalProductMeasure fundamentalTimeInterval
  infer_instance

private theorem fundamentalProductMeasure_ne_zero
    (hPeriod : period ≠ 0) :
    fundamentalProductMeasure period ≠ 0 := by
  have hSphere : (volume : Measure EuclideanR4).toSphere ≠ 0 :=
    Measure.toSphere_ne_zero (volume : Measure EuclideanR4)
  have hTime : volume.restrict (fundamentalTimeInterval period) ≠ 0 := by
    intro hZero
    have hVolumeZero := Measure.restrict_eq_zero.mp hZero
    rw [fundamentalTimeInterval, Real.volume_Ioc,
      max_sub_min_eq_abs] at hVolumeZero
    apply (ENNReal.ofReal_pos.mpr (abs_pos.mpr hPeriod)).ne'
    simpa using hVolumeZero
  rw [← Measure.measure_univ_ne_zero]
  rw [show (Set.univ : Set (StandardSphere × Real)) =
      (Set.univ : Set StandardSphere) ×ˢ (Set.univ : Set Real) by simp]
  unfold fundamentalProductMeasure
  rw [Measure.prod_prod]
  exact mul_ne_zero
    ((Measure.measure_univ_ne_zero).2 hSphere)
    ((Measure.measure_univ_ne_zero).2 hTime)

/-- Canonical product Lorentz volume on the actual quotient.  It is the
pushforward of round `S³` surface measure times one period of Lebesgue measure.
The quotient identification changes only the null boundary of the chosen
half-open fundamental interval. -/
def intrinsicCanonicalLorentzVolumeMeasure :
    Measure (EffectiveQuotient period hPeriod) :=
  (fundamentalProductMeasure period).map (fundamentalDomainMap period hPeriod)

theorem intrinsicCanonicalLorentzVolumeMeasure_isFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI := fundamentalProductMeasure_isFinite period
  exact Measure.isFiniteMeasure_map _ _

theorem intrinsicCanonicalLorentzVolumeMeasure_ne_zero :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod ≠ 0 := by
  exact (Measure.map_ne_zero_iff
    (fundamentalDomainMap_continuous period hPeriod).measurable.aemeasurable).2
      (fundamentalProductMeasure_ne_zero period hPeriod)

/-- One chart contribution to the intrinsic Lorentz volume.  The reference
measure may be supplied either in local coordinates or, as below, by the
explicit round-sphere-times-time quotient measure. -/
structure LocalLorentzDensityChart where
  domain : Set (EffectiveQuotient period hPeriod)
  measurableDomain : MeasurableSet domain
  coordinateMeasure : Measure (EffectiveQuotient period hPeriod)
  frame : ∀ point, Fin 4 → TangentFiber period hPeriod point
  densityMeasurable : Measurable fun point => ENNReal.ofReal
    (fiberMetricVolumeDensity period hPeriod
      ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point)
      (frame point))

/-- The local `sqrt |det g|` weight in a supplied coordinate frame. -/
def LocalLorentzDensityChart.metricDensity
    (chart : LocalLorentzDensityChart period hPeriod)
    (point : EffectiveQuotient period hPeriod) : ENNReal :=
  ENNReal.ofReal
    (fiberMetricVolumeDensity period hPeriod
      ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point)
      (chart.frame point))

/-- Coordinate measure weighted by the intrinsic Lorentz determinant. -/
def LocalLorentzDensityChart.metricMeasure
    (chart : LocalLorentzDensityChart period hPeriod) :
    Measure (EffectiveQuotient period hPeriod) :=
  chart.coordinateMeasure.withDensity (chart.metricDensity period hPeriod)

private def certifiedLorentzFrameEquiv
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real] CoverCoordinates :=
  Classical.choose
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).lorentzian point)

private theorem certifiedLorentzFrameEquiv_pair
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor point
        first second =
      modelMinkowskiPair
        (certifiedLorentzFrameEquiv period hPeriod point first)
        (certifiedLorentzFrameEquiv period hPeriod point second) :=
  Classical.choose_spec
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).lorentzian point)
      first second

private def modelLorentzBasisVector (index : Fin 4) : CoverCoordinates :=
  ![(0, 1),
    (EuclideanSpace.single 0 1, 0),
    (EuclideanSpace.single 1 1, 0),
    (EuclideanSpace.single 2 1, 0)] index

private def modelLorentzSign (index : Fin 4) : Real :=
  ![-1, 1, 1, 1] index

private theorem modelLorentzBasisVector_pair (first second : Fin 4) :
    modelMinkowskiPair (modelLorentzBasisVector first)
        (modelLorentzBasisVector second) =
      Matrix.diagonal modelLorentzSign first second := by
  fin_cases first <;> fin_cases second <;>
    simp [modelMinkowskiPair, modelLorentzBasisVector, modelLorentzSign,
      EuclideanSpace.inner_single_left]

private def certifiedLorentzFrame
    (point : EffectiveQuotient period hPeriod) :
    Fin 4 → TangentFiber period hPeriod point :=
  fun index => (certifiedLorentzFrameEquiv period hPeriod point).symm
    (modelLorentzBasisVector index)

private theorem certifiedLorentzFrame_density_eq_one
    (point : EffectiveQuotient period hPeriod) :
    fiberMetricVolumeDensity period hPeriod
        ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point)
        (certifiedLorentzFrame period hPeriod point) = 1 := by
  have hGram :
      fiberGramMatrix period hPeriod
          ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point)
          (certifiedLorentzFrame period hPeriod point) =
        Matrix.diagonal modelLorentzSign := by
    ext first second
    change (intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point
        (certifiedLorentzFrame period hPeriod point first)
        (certifiedLorentzFrame period hPeriod point second) = _
    have hMetricPair := congrArg
      (fun musical => musical
        (certifiedLorentzFrame period hPeriod point first)
        (certifiedLorentzFrame period hPeriod point second))
      ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical_eq_tensor
        point)
    calc
      _ = (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          point (certifiedLorentzFrame period hPeriod point first)
            (certifiedLorentzFrame period hPeriod point second) := hMetricPair
      _ = modelMinkowskiPair
          (certifiedLorentzFrameEquiv period hPeriod point
            (certifiedLorentzFrame period hPeriod point first))
          (certifiedLorentzFrameEquiv period hPeriod point
            (certifiedLorentzFrame period hPeriod point second)) :=
        certifiedLorentzFrameEquiv_pair period hPeriod point _ _
      _ = modelMinkowskiPair (modelLorentzBasisVector first)
          (modelLorentzBasisVector second) := by
        simp only [certifiedLorentzFrame,
          ContinuousLinearEquiv.apply_symm_apply]
      _ = Matrix.diagonal modelLorentzSign first second :=
        modelLorentzBasisVector_pair first second
  rw [fiberMetricVolumeDensity, hGram, Matrix.det_diagonal]
  norm_num [modelLorentzSign, Fin.prod_univ_succ]

private def finitePatchEquivFin :
    FiniteTangentGeneratorPatch period hPeriod ≃
      Fin (Fintype.card (FiniteTangentGeneratorPatch period hPeriod)) :=
  Fintype.equivFin (FiniteTangentGeneratorPatch period hPeriod)

private def intrinsicLocalLorentzChart
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    LocalLorentzDensityChart period hPeriod where
  domain := finiteTangentGeneratorClosedPatch period hPeriod patch
  measurableDomain :=
    (finiteTangentGeneratorClosedPatch_isClosed period hPeriod patch).measurableSet
  coordinateMeasure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  frame := certifiedLorentzFrame period hPeriod
  densityMeasurable := by
    have hDensity : (fun point : EffectiveQuotient period hPeriod =>
        ENNReal.ofReal
          (fiberMetricVolumeDensity period hPeriod
            ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical point)
            (certifiedLorentzFrame period hPeriod point))) = fun _ => 1 := by
      funext point
      rw [certifiedLorentzFrame_density_eq_one]
      simp
    rw [hDensity]
    exact measurable_const

private theorem intrinsicLocalLorentzChart_metricDensity_eq_one
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    (intrinsicLocalLorentzChart period hPeriod patch).metricDensity
      period hPeriod = 1 := by
  funext point
  simp [LocalLorentzDensityChart.metricDensity,
    intrinsicLocalLorentzChart, certifiedLorentzFrame_density_eq_one]

private theorem intrinsicLocalLorentzChart_metricMeasure
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    (intrinsicLocalLorentzChart period hPeriod patch).metricMeasure
        period hPeriod =
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).withDensity
      ((intrinsicLocalLorentzChart period hPeriod patch).metricDensity
        period hPeriod) = _
  rw [intrinsicLocalLorentzChart_metricDensity_eq_one]
  simp

/-- The exact finite-atlas contract missing from Mathlib.  Compatibility is
equality of the weighted measures on overlaps, not merely equality of their
pointwise representatives. -/
structure FiniteLorentzDensityAtlas where
  patchCount : Nat
  chart : Fin patchCount → LocalLorentzDensityChart period hPeriod
  covers : (⋃ index, (chart index).domain) = Set.univ
  overlapCompatible : ∀ first second,
    ((chart first).metricMeasure period hPeriod).restrict
        ((chart first).domain ∩ (chart second).domain) =
      ((chart second).metricMeasure period hPeriod).restrict
        ((chart first).domain ∩ (chart second).domain)
  localFinite : ∀ index, IsFiniteMeasure
    (((chart index).metricMeasure period hPeriod).restrict
      (chart index).domain)
  someLocalNonzero : ∃ index,
    ((chart index).metricMeasure period hPeriod).restrict
      (chart index).domain ≠ 0

/-- The finite tangent-trivialization cover, equipped with the canonical
round-sphere-times-time quotient volume and certified Lorentz-orthonormal
frames, realizes the density-atlas contract without extra input. -/
def intrinsicFiniteLorentzDensityAtlas :
    FiniteLorentzDensityAtlas period hPeriod where
  patchCount := Fintype.card (FiniteTangentGeneratorPatch period hPeriod)
  chart index := intrinsicLocalLorentzChart period hPeriod
    ((finitePatchEquivFin period hPeriod).symm index)
  covers := by
    ext point
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨patch, hPatch⟩ :=
      finiteTangentGeneratorClosedPatch_covers period hPeriod point
    exact ⟨finitePatchEquivFin period hPeriod patch, by
      simpa [intrinsicLocalLorentzChart] using hPatch⟩
  overlapCompatible first second := by
    rw [intrinsicLocalLorentzChart_metricMeasure,
      intrinsicLocalLorentzChart_metricMeasure]
  localFinite index := by
    rw [intrinsicLocalLorentzChart_metricMeasure]
    letI := intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
    infer_instance
  someLocalNonzero := by
    let μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
    have hUnion :
        (⋃ index : Fin
            (Fintype.card (FiniteTangentGeneratorPatch period hPeriod)),
          (intrinsicLocalLorentzChart period hPeriod
            ((finitePatchEquivFin period hPeriod).symm index)).domain) =
          Set.univ := by
      ext point
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨patch, hPatch⟩ :=
        finiteTangentGeneratorClosedPatch_covers period hPeriod point
      exact ⟨finitePatchEquivFin period hPeriod patch, by
        simpa [intrinsicLocalLorentzChart] using hPatch⟩
    have hUnionNonzero : μ (⋃ index : Fin
        (Fintype.card (FiniteTangentGeneratorPatch period hPeriod)),
        (intrinsicLocalLorentzChart period hPeriod
          ((finitePatchEquivFin period hPeriod).symm index)).domain) ≠ 0 := by
      rw [hUnion]
      exact (Measure.measure_univ_ne_zero).2
        (intrinsicCanonicalLorentzVolumeMeasure_ne_zero period hPeriod)
    obtain ⟨index, hIndex⟩ :=
      exists_measure_pos_of_not_measure_iUnion_null hUnionNonzero
    refine ⟨index, ?_⟩
    rw [intrinsicLocalLorentzChart_metricMeasure]
    intro hZero
    exact (ne_of_gt hIndex) (Measure.restrict_eq_zero.mp hZero)

private def patchDomain
    (atlas : FiniteLorentzDensityAtlas period hPeriod) :
    Fin atlas.patchCount → Set (EffectiveQuotient period hPeriod) :=
  fun index => (atlas.chart index).domain

private def patchCell
    (atlas : FiniteLorentzDensityAtlas period hPeriod)
    (index : Fin atlas.patchCount) : Set (EffectiveQuotient period hPeriod) :=
  disjointed (patchDomain period hPeriod atlas) index

private theorem patchCell_measurable
    (atlas : FiniteLorentzDensityAtlas period hPeriod)
    (index : Fin atlas.patchCount) :
    MeasurableSet (patchCell period hPeriod atlas index) := by
  rw [patchCell, disjointed_eq_inter_compl]
  exact (atlas.chart index).measurableDomain.inter
    (MeasurableSet.iInter fun current => MeasurableSet.iInter fun _ =>
      (atlas.chart current).measurableDomain.compl)

private theorem patchCell_subset
    (atlas : FiniteLorentzDensityAtlas period hPeriod)
    (index : Fin atlas.patchCount) :
    patchCell period hPeriod atlas index ⊆ (atlas.chart index).domain :=
  disjointed_subset (patchDomain period hPeriod atlas) index

/-- Canonical global measure obtained by assigning each point to the first
chart containing it.  The next theorem proves that this bookkeeping choice
does not affect any local restriction. -/
def canonicalLorentzVolumeMeasure
    (atlas : FiniteLorentzDensityAtlas period hPeriod) :
    Measure (EffectiveQuotient period hPeriod) :=
  Measure.sum fun index =>
    ((atlas.chart index).metricMeasure period hPeriod).restrict
      (patchCell period hPeriod atlas index)

/-- The constructed measure restricts to the prescribed metric volume on
every chart.  This is the local independence/gluing theorem. -/
theorem canonicalLorentzVolumeMeasure_restrict
    (atlas : FiniteLorentzDensityAtlas period hPeriod)
    (fixed : Fin atlas.patchCount) :
    (canonicalLorentzVolumeMeasure period hPeriod atlas).restrict
        (atlas.chart fixed).domain =
      ((atlas.chart fixed).metricMeasure period hPeriod).restrict
        (atlas.chart fixed).domain := by
  rw [canonicalLorentzVolumeMeasure, Measure.restrict_sum _
    (atlas.chart fixed).measurableDomain]
  have hTerm : ∀ index : Fin atlas.patchCount,
      (((atlas.chart index).metricMeasure period hPeriod).restrict
          (patchCell period hPeriod atlas index)).restrict
          (atlas.chart fixed).domain =
        ((atlas.chart fixed).metricMeasure period hPeriod).restrict
          ((atlas.chart fixed).domain ∩
            patchCell period hPeriod atlas index) := by
    intro index
    rw [Measure.restrict_restrict (atlas.chart fixed).measurableDomain]
    apply Measure.restrict_congr_mono
      (t := (atlas.chart index).domain ∩ (atlas.chart fixed).domain)
    · intro point hPoint
      exact ⟨patchCell_subset period hPeriod atlas index hPoint.2, hPoint.1⟩
    · exact atlas.overlapCompatible index fixed
  rw [show (fun index =>
      (((atlas.chart index).metricMeasure period hPeriod).restrict
        (patchCell period hPeriod atlas index)).restrict
        (atlas.chart fixed).domain) =
      (fun index =>
        ((atlas.chart fixed).metricMeasure period hPeriod).restrict
          ((atlas.chart fixed).domain ∩
            patchCell period hPeriod atlas index)) by
    funext index
    exact hTerm index]
  rw [← Measure.restrict_iUnion]
  · congr 1
    have hCellsCover :
        (⋃ index, patchCell period hPeriod atlas index) = Set.univ := by
      calc
        _ = ⋃ index, patchDomain period hPeriod atlas index :=
          iUnion_disjointed
        _ = Set.univ := by simpa [patchDomain] using atlas.covers
    calc
      _ = (atlas.chart fixed).domain ∩
          (⋃ index, patchCell period hPeriod atlas index) :=
        (Set.inter_iUnion _ _).symm
      _ = (atlas.chart fixed).domain := by rw [hCellsCover, Set.inter_univ]
  · exact (disjoint_disjointed (patchDomain period hPeriod atlas)).mono
      fun _ _ hDisjoint =>
        hDisjoint.mono Set.inter_subset_right Set.inter_subset_right
  · intro index
    exact (atlas.chart fixed).measurableDomain.inter
      (patchCell_measurable period hPeriod atlas index)

/-- A measure with the prescribed chart restrictions is necessarily the
constructed one. -/
theorem canonicalLorentzVolumeMeasure_unique
    (atlas : FiniteLorentzDensityAtlas period hPeriod)
    (candidate : Measure (EffectiveQuotient period hPeriod))
    (hCandidate : ∀ index,
      candidate.restrict (atlas.chart index).domain =
        ((atlas.chart index).metricMeasure period hPeriod).restrict
          (atlas.chart index).domain) :
    candidate = canonicalLorentzVolumeMeasure period hPeriod atlas := by
  apply Measure.ext_of_iUnion_eq_univ atlas.covers
  intro index
  exact (hCandidate index).trans
    (canonicalLorentzVolumeMeasure_restrict period hPeriod atlas index).symm

/-- The abstract disjointed-cover construction applied to the intrinsic atlas
recovers exactly the geometric product-quotient measure. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_eq_glued :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod =
      canonicalLorentzVolumeMeasure period hPeriod
        (intrinsicFiniteLorentzDensityAtlas period hPeriod) := by
  apply canonicalLorentzVolumeMeasure_unique period hPeriod
  intro index
  dsimp only [intrinsicFiniteLorentzDensityAtlas]
  rw [intrinsicLocalLorentzChart_metricMeasure]

/-- Finiteness follows from the finite cover and finite local pieces. -/
theorem canonicalLorentzVolumeMeasure_isFinite
    (atlas : FiniteLorentzDensityAtlas period hPeriod) :
    IsFiniteMeasure (canonicalLorentzVolumeMeasure period hPeriod atlas) := by
  let localPart : Fin atlas.patchCount →
      Measure (EffectiveQuotient period hPeriod) := fun index =>
    ((atlas.chart index).metricMeasure period hPeriod).restrict
      (patchCell period hPeriod atlas index)
  letI : ∀ index, IsFiniteMeasure (localPart index) := fun index => by
    letI := atlas.localFinite index
    change IsFiniteMeasure
      (((atlas.chart index).metricMeasure period hPeriod).restrict
        (patchCell period hPeriod atlas index))
    rw [← Measure.restrict_restrict_of_subset
      (patchCell_subset period hPeriod atlas index)]
    infer_instance
  change IsFiniteMeasure (Measure.sum localPart)
  infer_instance

/-- Nonzeroness is inherited from any nonzero chart restriction. -/
theorem canonicalLorentzVolumeMeasure_ne_zero
    (atlas : FiniteLorentzDensityAtlas period hPeriod) :
    canonicalLorentzVolumeMeasure period hPeriod atlas ≠ 0 := by
  intro hZero
  obtain ⟨index, hLocal⟩ := atlas.someLocalNonzero
  apply hLocal
  have hRestriction :=
    canonicalLorentzVolumeMeasure_restrict period hPeriod atlas index
  rw [hZero] at hRestriction
  simpa using hRestriction.symm

/-- The canonical glued volume in the exact interface required by the
frame-free scalar action. -/
def canonicalLorentzActionMeasure
    (atlas : FiniteLorentzDensityAtlas period hPeriod) :
    FiniteNonzeroActionMeasure period hPeriod where
  measure := canonicalLorentzVolumeMeasure period hPeriod atlas
  finite := canonicalLorentzVolumeMeasure_isFinite period hPeriod atlas
  nonzero := canonicalLorentzVolumeMeasure_ne_zero period hPeriod atlas

/-- Unconditional canonical action measure for the intrinsic quotient metric. -/
def intrinsicCanonicalLorentzActionMeasure :
    FiniteNonzeroActionMeasure period hPeriod :=
  canonicalLorentzActionMeasure period hPeriod
    (intrinsicFiniteLorentzDensityAtlas period hPeriod)

theorem intrinsicCanonicalLorentzActionMeasure_eq_product :
    (intrinsicCanonicalLorentzActionMeasure period hPeriod).measure =
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  exact (intrinsicCanonicalLorentzVolumeMeasure_eq_glued
    period hPeriod).symm

/-- Frame-free intrinsic scalar action with the canonically glued volume. -/
def canonicalFrameFreeScalarAction
    (atlas : FiniteLorentzDensityAtlas period hPeriod)
    (massSquared : Real)
    (data : IntrinsicRegularScalar period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)) : Real :=
  frameFreeScalarAction period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared data
    (canonicalLorentzActionMeasure period hPeriod atlas)

/-- Frame-free scalar action with no external measure or atlas hypothesis. -/
def intrinsicCanonicalFrameFreeScalarAction
    (massSquared : Real)
    (data : IntrinsicRegularScalar period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)) : Real :=
  frameFreeScalarAction period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared data
    (intrinsicCanonicalLorentzActionMeasure period hPeriod)

theorem canonicalFrameFreeScalarDensity_integrable
    (atlas : FiniteLorentzDensityAtlas period hPeriod)
    (massSquared : Real)
    (data : IntrinsicRegularScalar period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)) :
    Integrable
      (frameFreeScalarDensity period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared data)
      (canonicalLorentzVolumeMeasure period hPeriod atlas) := by
  exact frameFreeScalarDensity_integrable period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared data
    (canonicalLorentzActionMeasure period hPeriod atlas)

/-- The canonical construction gives a genuinely nonzero integrated branch
for a nonzero massive constant field. -/
theorem canonicalIntrinsicMetric_constantAction_nonzero
    (atlas : FiniteLorentzDensityAtlas period hPeriod) :
    canonicalFrameFreeScalarAction period hPeriod atlas 2
      (constantIntrinsicRegularScalar period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) 1) ≠ 0 := by
  exact intrinsicMetric_constantAction_nonzero period hPeriod
    (canonicalLorentzActionMeasure period hPeriod atlas)

theorem intrinsicCanonicalMetric_constantAction_nonzero :
    intrinsicCanonicalFrameFreeScalarAction period hPeriod 2
      (constantIntrinsicRegularScalar period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) 1) ≠ 0 := by
  exact intrinsicMetric_constantAction_nonzero period hPeriod
    (intrinsicCanonicalLorentzActionMeasure period hPeriod)

end

end P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
end JanusFormal
