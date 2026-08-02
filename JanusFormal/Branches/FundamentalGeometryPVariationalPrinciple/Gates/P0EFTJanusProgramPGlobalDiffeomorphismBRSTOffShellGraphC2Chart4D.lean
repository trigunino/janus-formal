import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D

/-!
# Mono-metric global diffeomorphism BRST off-shell graph

This gate constructs the complete single-metric graph without choosing how
the two Candidate-A metric conditions couple to the unique diagonal
diffeomorphism triple.  Its BRST differential is the real-linearized model
with `s c = 0`; no Grassmann-graded algebra is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalLorentzVolumeOpenPos :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod

private abbrev frame :=
  finiteSmoothTangentFrame period hPeriod

private abbrev deDonderBackground :=
  generalMetricDivergenceBackground period hPeriod

private abbrev GeneratorIndex :=
  FiniteTangentGeneratorIndex period hPeriod

private abbrev generatorIndexEquivFrameIndex :
    GeneratorIndex period hPeriod ≃ Fin (frame period hPeriod).count :=
  finiteTangentGeneratorIndexEquivFin period hPeriod

abbrev GlobalDiffeomorphismVectorL2 :=
  GlobalGeneralMetricDeDonderFrameL2 period hPeriod

/- The canonical `PiLp` instances are retained to keep all later product
instances definitionally coherent.
local instance globalDiffeomorphismVectorL2NormedSpace :
    NormedSpace Real (GlobalDiffeomorphismVectorL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalDiffeomorphismVectorL2 period hPeriod)).toNormedSpace

local instance globalDiffeomorphismVectorL2Module :
    Module Real (GlobalDiffeomorphismVectorL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalDiffeomorphismVectorL2 period hPeriod)).toNormedSpace.toModule
-/

/-! ## Generic covector/vector feature maps -/

def globalSmoothCovectorFrameL2LinearMap :
    EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod) →ₗ[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod where
  toFun := fun covector =>
    WithLp.toLp 2 fun index =>
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (globalSmoothCovectorFrameCoefficient
          period hPeriod covector index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalSmoothCovectorFrameCoefficientLinearMap
          period hPeriod index)
    exact component.map_add first second
  map_smul' scalar covector := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalSmoothCovectorFrameCoefficientLinearMap
          period hPeriod index)
    exact component.map_smul scalar covector

def globalNormalizedVectorCoordinate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : EffectiveD8SmoothVectorField
      (deDonderBackground period hPeriod))
    (index : Fin (frame period hPeriod).count) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    globalGeneralMetricDeDonderPairingNormalization
        period hPeriod metric point *
      globalFiniteTangentWeightedLocalCoefficient
        period hPeriod field
          ((generatorIndexEquivFrameIndex period hPeriod).symm index) point
  contMDiff_toFun := by
    exact
      (globalGeneralMetricDeDonderPairingNormalization
        period hPeriod metric).contMDiff_toFun.mul
      (globalFiniteTangentWeightedLocalCoefficient
        period hPeriod field
          ((generatorIndexEquivFrameIndex period hPeriod).symm index)
      ).contMDiff_toFun

@[simp]
theorem globalNormalizedVectorCoordinate_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : EffectiveD8SmoothVectorField
      (deDonderBackground period hPeriod))
    (index : Fin (frame period hPeriod).count)
    (point : EffectiveQuotient period hPeriod) :
    globalNormalizedVectorCoordinate period hPeriod metric field index point =
      globalGeneralMetricDeDonderPairingNormalization
          period hPeriod metric point *
        (finiteTangentGeneratorWeight period hPeriod
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).1 point *
          finiteTangentGeneratorLocalCoefficient period hPeriod
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).1
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).2 point (field point)) :=
  rfl

def globalNormalizedVectorCoordinateLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (frame period hPeriod).count) :
    SmoothTangentField period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun := fun field =>
    globalNormalizedVectorCoordinate
      period hPeriod metric field index
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change
      globalNormalizedVectorCoordinate period hPeriod metric
          (first + second) index point =
        globalNormalizedVectorCoordinate period hPeriod metric first index
            point +
          globalNormalizedVectorCoordinate period hPeriod metric second index
            point
    rw [globalNormalizedVectorCoordinate_apply,
      globalNormalizedVectorCoordinate_apply,
      globalNormalizedVectorCoordinate_apply]
    unfold finiteTangentGeneratorLocalCoefficient
    simp only [ContMDiffSection.coe_add, Pi.add_apply, map_add]
    ring
  map_smul' scalar field := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change
      globalNormalizedVectorCoordinate period hPeriod metric
          (scalar • field) index point =
        scalar *
          globalNormalizedVectorCoordinate period hPeriod metric field index
            point
    rw [globalNormalizedVectorCoordinate_apply,
      globalNormalizedVectorCoordinate_apply]
    unfold finiteTangentGeneratorLocalCoefficient
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, map_smul,
      smul_eq_mul]
    ring

def globalNormalizedVectorFrameL2LinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothTangentField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod where
  toFun := fun field =>
    WithLp.toLp 2 fun index =>
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (globalNormalizedVectorCoordinate
          period hPeriod metric field index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalNormalizedVectorCoordinateLinearMap
          period hPeriod metric index)
    exact component.map_add first second
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalNormalizedVectorCoordinateLinearMap
          period hPeriod metric index)
    exact component.map_smul scalar field

theorem globalNormalizedVectorFrameL2LinearMap_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalNormalizedVectorFrameL2LinearMap
        period hPeriod metric) := by
  intro first second hEqual
  apply ContMDiffSection.ext
  intro point
  obtain ⟨patch, hPatchWeight⟩ :=
    exists_finiteTangentGeneratorWeight_ge_inv_card
      period hPeriod point
  have hCard :
      0 < Fintype.card
        (FiniteTangentGeneratorPatch period hPeriod) :=
    Fintype.card_pos_iff.mpr ⟨patch⟩
  have hInverse :
      0 <
        1 / (Fintype.card
          (FiniteTangentGeneratorPatch period hPeriod) : Real) :=
    one_div_pos.mpr (by exact_mod_cast hCard)
  have hWeightPos :
      0 < finiteTangentGeneratorWeight
        period hPeriod patch point :=
    lt_of_lt_of_le hInverse hPatchWeight
  have hPointPatch :
      point ∈ finiteTangentGeneratorOpenPatch
        period hPeriod patch := by
    have hSupport :
        point ∈ Function.support
          (finiteTangentGeneratorWeight period hPeriod patch) :=
      ne_of_gt hWeightPos
    exact finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch (subset_closure hSupport)
  have hNormalizationPos :
      0 < globalGeneralMetricDeDonderPairingNormalization
        period hPeriod metric point := by
    change
      0 < globalMetricVolumeRatio period hPeriod metric point /
        globalFiniteTangentWeightSquareSum period hPeriod point
    exact div_pos
      (globalMetricVolumeRatio_pos period hPeriod metric point)
      (globalFiniteTangentWeightSquareSum_pos period hPeriod point)
  have hCoefficient
      (basisIndex : FiniteTangentGeneratorBasisIndex) :
      finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
          point (first point) =
        finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
          point (second point) := by
    let index := generatorIndexEquivFrameIndex
      period hPeriod (patch, basisIndex)
    have hL2 := congrArg
      (fun value : GlobalDiffeomorphismVectorL2 period hPeriod =>
        value index) hEqual
    change
      smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (globalNormalizedVectorCoordinate
            period hPeriod metric first index) =
        smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (globalNormalizedVectorCoordinate
            period hPeriod metric second index)
      at hL2
    have hField :=
      smoothFieldToL2_injective period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) hL2
    have hPoint := congrArg
      (fun field : SmoothQuotientField period hPeriod Real => field point)
      hField
    rw [globalNormalizedVectorCoordinate_apply,
      globalNormalizedVectorCoordinate_apply] at hPoint
    dsimp only [index] at hPoint
    simp only [Equiv.symm_apply_apply] at hPoint
    have hAfterNormalization :=
      mul_left_cancel₀ (ne_of_gt hNormalizationPos) hPoint
    exact mul_left_cancel₀ (ne_of_gt hWeightPos) hAfterNormalization
  calc
    first point =
        ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
          finiteTangentGeneratorLocalCoefficient period hPeriod patch
              basisIndex point (first point) •
            finiteTangentGeneratorLocalVector period hPeriod patch basisIndex
              point :=
      finiteTangentGeneratorLocalVector_reconstructs
        period hPeriod patch point hPointPatch (first point)
    _ =
        ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
          finiteTangentGeneratorLocalCoefficient period hPeriod patch
              basisIndex point (second point) •
            finiteTangentGeneratorLocalVector period hPeriod patch basisIndex
              point := by
      apply Finset.sum_congr rfl
      intro basisIndex _
      rw [hCoefficient basisIndex]
    _ = second point :=
      (finiteTangentGeneratorLocalVector_reconstructs
        period hPeriod patch point hPointPatch (second point)).symm

private theorem finiteTangentWeight_eq_zero_of_not_mem
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hPoint :
      point ∉ finiteTangentGeneratorOpenPatch period hPeriod patch) :
    finiteTangentGeneratorWeight period hPeriod patch point = 0 := by
  by_contra hNonzero
  have hSupport :
      point ∈ Function.support
        (finiteTangentGeneratorWeight period hPeriod patch) :=
    hNonzero
  have hClosedSupport :
      point ∈ finiteTangentGeneratorClosedPatch
        period hPeriod patch :=
    subset_closure hSupport
  exact hPoint
    (finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch hClosedSupport)

@[simp]
private theorem frame_vectorAt_generator
    (point : EffectiveQuotient period hPeriod)
    (index : GeneratorIndex period hPeriod) :
    (frame period hPeriod).vectorAt point
        (generatorIndexEquivFrameIndex period hPeriod index) =
      finiteTangentGeneratorWeight period hPeriod index.1 point •
        finiteTangentGeneratorLocalVector
          period hPeriod index.1 index.2 point := by
  convert
    finiteSmoothTangentFrame_vectorAt_generator
      period hPeriod point index using 1;
    rfl

/-- Public-index copy of the installed exact finite-frame factorization. -/
theorem globalFiniteTangentPairingFactorizationPublic
    (point : EffectiveQuotient period hPeriod)
    (covector :
      TangentSpace coverModelWithCorners point →L[Real] Real)
    (vector : TangentSpace coverModelWithCorners point) :
    (∑ index : Fin (frame period hPeriod).count,
      covector ((frame period hPeriod).vectorAt point index) *
        (finiteTangentGeneratorWeight period hPeriod
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).1 point *
          finiteTangentGeneratorLocalCoefficient period hPeriod
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).1
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).2 point vector)) =
      globalFiniteTangentWeightSquareSum period hPeriod point *
        covector vector := by
  rw [← (generatorIndexEquivFrameIndex period hPeriod).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  change
    (∑ patch : FiniteTangentGeneratorPatch period hPeriod,
      ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
        covector ((frame period hPeriod).vectorAt point
          (generatorIndexEquivFrameIndex
            period hPeriod (patch, basisIndex))) *
          (finiteTangentGeneratorWeight period hPeriod patch point *
            finiteTangentGeneratorLocalCoefficient period hPeriod
              patch basisIndex point vector)) =
      (∑ patch : FiniteTangentGeneratorPatch period hPeriod,
        finiteTangentGeneratorWeight period hPeriod patch point ^ 2) *
        covector vector
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro patch _
  by_cases hPoint :
      point ∈ finiteTangentGeneratorOpenPatch
        period hPeriod patch
  · have hReconstruct :=
      finiteTangentGeneratorLocalVector_reconstructs
        period hPeriod patch point hPoint vector
    have hApplied := congrArg covector hReconstruct
    rw [map_sum] at hApplied
    simp only [map_smul, smul_eq_mul] at hApplied
    calc
      (∑ basisIndex : FiniteTangentGeneratorBasisIndex,
        covector
            ((frame period hPeriod).vectorAt point
              (generatorIndexEquivFrameIndex
                period hPeriod (patch, basisIndex))) *
          (finiteTangentGeneratorWeight period hPeriod patch point *
            finiteTangentGeneratorLocalCoefficient period hPeriod
              patch basisIndex point vector)) =
          finiteTangentGeneratorWeight period hPeriod patch point ^ 2 *
            (∑ basisIndex : FiniteTangentGeneratorBasisIndex,
              finiteTangentGeneratorLocalCoefficient period hPeriod
                  patch basisIndex point vector *
                covector
                  (finiteTangentGeneratorLocalVector
                    period hPeriod patch basisIndex point)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro basisIndex _
        rw [frame_vectorAt_generator]
        simp only [map_smul, smul_eq_mul]
        ring
      _ = finiteTangentGeneratorWeight period hPeriod patch point ^ 2 *
          covector vector := by
        rw [← hApplied]
  · have hWeight :=
      finiteTangentWeight_eq_zero_of_not_mem
        period hPeriod patch point hPoint
    simp [hWeight]

/-- Smooth metric lowering for a global tangent field. -/
def globalSmoothMetricFlat
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothTangentField period hPeriod) :
    EffectiveD8SmoothCovectorField
      (deDonderBackground period hPeriod) where
  toFun := fun point => metric.tensor.tensor point (field point)
  contMDiff_toFun :=
    metric.tensor.tensor.contMDiff.clm_bundle_apply field.contMDiff

@[simp]
theorem globalSmoothMetricFlat_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (tangent : TangentSpace coverModelWithCorners point) :
    globalSmoothMetricFlat period hPeriod metric field point tangent =
      metric.tensor.tensor point (field point) tangent :=
  rfl

def globalSmoothMetricFlatLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothTangentField period hPeriod →ₗ[Real]
      EffectiveD8SmoothCovectorField
        (deDonderBackground period hPeriod) where
  toFun := globalSmoothMetricFlat period hPeriod metric
  map_add' first second := by
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro tangent
    simp
  map_smul' scalar field := by
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro tangent
    simp

def globalSmoothMetricFlatFrameL2LinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothTangentField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalSmoothCovectorFrameL2LinearMap period hPeriod).comp
    (globalSmoothMetricFlatLinearMap period hPeriod metric)

def globalDiffeomorphismFPL2LinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalSmoothCovectorFrameL2LinearMap period hPeriod).comp
    (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
      period hPeriod metric)

/-! ## Exact integrated pairing identity -/

def globalCovectorVectorPairingField
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point => covector point (vector point)
  contMDiff_toFun := by
    have hApplied := covector.contMDiff.clm_bundle_apply vector.contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem globalCovectorVectorPairingField_apply
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalCovectorVectorPairingField
        period hPeriod covector vector point =
      covector point (vector point) :=
  rfl

theorem globalCovectorVectorPairingField_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod) :
    Integrable
      (globalCovectorVectorPairingField
        period hPeriod covector vector)
      (generalLorentzVolumeMeasure period hPeriod metric) := by
  letI := generalLorentzVolumeMeasure_isFinite period hPeriod metric
  exact
    (globalCovectorVectorPairingField period hPeriod covector vector)
      |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

def globalIntegratedCovectorVectorPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod) : Real :=
  ∫ point,
    globalCovectorVectorPairingField
      period hPeriod covector vector point
    ∂generalLorentzVolumeMeasure period hPeriod metric

private theorem smoothCanonicalPhysicalBulkL2_inner
    (first second : SmoothQuotientField period hPeriod Real) :
    inner Real
        (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
        (smoothToCanonicalPhysicalBulkL2 period hPeriod second) =
      ∫ point, first point * second point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) first,
     smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) second]
    with point hFirst hSecond
  change inner Real
      ((smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) first :
          EffectiveQuotient period hPeriod → Real) point)
      ((smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) second :
          EffectiveQuotient period hPeriod → Real) point) = _
  rw [hFirst, hSecond]
  exact Real.inner_apply _ _

private theorem covectorVectorFeatureProduct_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod)
    (index : Fin (frame period hPeriod).count) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        globalSmoothCovectorFrameCoefficient
            period hPeriod covector index point *
          globalNormalizedVectorCoordinate
            period hPeriod metric vector index point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact
    ((globalSmoothCovectorFrameCoefficient period hPeriod
        covector index).contMDiff_toFun.continuous.mul
      (globalNormalizedVectorCoordinate
        period hPeriod metric vector index).contMDiff_toFun.continuous
    ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod) :
    inner Real
        (globalSmoothCovectorFrameL2LinearMap
          period hPeriod covector)
        (globalNormalizedVectorFrameL2LinearMap
          period hPeriod metric vector) =
      globalIntegratedCovectorVectorPairing
        period hPeriod metric covector vector := by
  unfold globalIntegratedCovectorVectorPairing
  rw [integral_generalLorentzVolumeMeasure_eq_reference]
  simp only [PiLp.inner_apply]
  change
    (∑ index : Fin (frame period hPeriod).count,
      inner Real
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (globalSmoothCovectorFrameCoefficient
            period hPeriod covector index))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (globalNormalizedVectorCoordinate
            period hPeriod metric vector index))) =
      ∫ point,
        globalMetricVolumeRatio period hPeriod metric point *
          covector point (vector point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  simp_rw [smoothCanonicalPhysicalBulkL2_inner]
  rw [← integral_finsetSum Finset.univ
    (fun index _ =>
      covectorVectorFeatureProduct_integrable
        period hPeriod metric covector vector index)]
  apply integral_congr_ae
  filter_upwards [] with point
  have hFactorPublic :=
    globalFiniteTangentPairingFactorizationPublic
      period hPeriod point (covector point) (vector point)
  have hWeightNe :
      globalFiniteTangentWeightSquareSum period hPeriod point ≠ 0 :=
    ne_of_gt (globalFiniteTangentWeightSquareSum_pos
      period hPeriod point)
  calc
    (∑ index : Fin (frame period hPeriod).count,
      globalSmoothCovectorFrameCoefficient
          period hPeriod covector index point *
        globalNormalizedVectorCoordinate
          period hPeriod metric vector index point) =
        globalGeneralMetricDeDonderPairingNormalization
            period hPeriod metric point *
          (∑ index : Fin (frame period hPeriod).count,
            covector point ((frame period hPeriod).vectorAt point index) *
              (finiteTangentGeneratorWeight period hPeriod
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).1 point *
                finiteTangentGeneratorLocalCoefficient period hPeriod
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).1
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).2 point (vector point))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      change
        covector point ((frame period hPeriod).vectorAt point index) *
            (globalGeneralMetricDeDonderPairingNormalization
                period hPeriod metric point *
              (finiteTangentGeneratorWeight period hPeriod
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).1 point *
                finiteTangentGeneratorLocalCoefficient period hPeriod
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).1
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).2 point (vector point))) = _
      ring
    _ = globalGeneralMetricDeDonderPairingNormalization
          period hPeriod metric point *
        (globalFiniteTangentWeightSquareSum period hPeriod point *
          covector point (vector point)) := by
      simpa only [] using congrArg
        (fun value : Real =>
          globalGeneralMetricDeDonderPairingNormalization
          period hPeriod metric point * value) hFactorPublic
    _ = globalMetricVolumeRatio period hPeriod metric point *
        covector point (vector point) := by
      change
        (globalMetricVolumeRatio period hPeriod metric point /
            globalFiniteTangentWeightSquareSum period hPeriod point) *
            (globalFiniteTangentWeightSquareSum period hPeriod point *
              covector point (vector point)) = _
      rw [← mul_assoc, div_mul_cancel₀ _ hWeightNe]

theorem globalIntegratedCovectorVectorPairing_sub_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod) :
    globalIntegratedCovectorVectorPairing period hPeriod metric
        (first - second) vector =
      globalIntegratedCovectorVectorPairing period hPeriod metric
          first vector -
        globalIntegratedCovectorVectorPairing period hPeriod metric
          second vector := by
  rw [← globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing,
    (globalSmoothCovectorFrameL2LinearMap period hPeriod).map_sub,
    inner_sub_left,
    globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing,
    globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing]

theorem globalIntegratedCovectorVectorPairing_smul_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (vector : SmoothTangentField period hPeriod) :
    globalIntegratedCovectorVectorPairing period hPeriod metric
        (scalar • covector) vector =
      scalar *
        globalIntegratedCovectorVectorPairing period hPeriod metric
          covector vector := by
  rw [← globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing,
    (globalSmoothCovectorFrameL2LinearMap period hPeriod).map_smul,
    inner_smul_left,
    globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing]
  rfl

/-! ## Mono-metric linearized BRST state and integrated `sΨ` -/

@[ext]
structure GlobalDiffeomorphismBRSTState where
  metricPerturbation :
    SmoothSymmetricCovariantTwoTensor period hPeriod
  nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod

def globalDiffeomorphismBRSTStateEquiv :
    GlobalDiffeomorphismBRSTState period hPeriod ≃
      SmoothSymmetricCovariantTwoTensor period hPeriod ×
        GlobalDiffeomorphismNonminimalFields period hPeriod where
  toFun state := (state.metricPerturbation, state.nonminimal)
  invFun state := ⟨state.1, state.2⟩
  left_inv state := by cases state; rfl
  right_inv state := by cases state; rfl

instance globalDiffeomorphismBRSTStateAddCommGroup :
    AddCommGroup (GlobalDiffeomorphismBRSTState period hPeriod) :=
  Equiv.addCommGroup
    (globalDiffeomorphismBRSTStateEquiv period hPeriod)

instance globalDiffeomorphismBRSTStateModule :
    Module Real (GlobalDiffeomorphismBRSTState period hPeriod) :=
  Equiv.module Real
    (globalDiffeomorphismBRSTStateEquiv period hPeriod)

def zeroGlobalDiffeomorphismBRSTState :
    GlobalDiffeomorphismBRSTState period hPeriod where
  metricPerturbation := 0
  nonminimal := zeroGlobalDiffeomorphismNonminimalFields period hPeriod

def globalDiffeomorphismMetricPerturbationProjectionLinearMap :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      SmoothSymmetricCovariantTwoTensor period hPeriod where
  toFun := GlobalDiffeomorphismBRSTState.metricPerturbation
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalDiffeomorphismNonminimalProjectionLinearMap :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalDiffeomorphismNonminimalFields period hPeriod where
  toFun := GlobalDiffeomorphismBRSTState.nonminimal
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalDiffeomorphismGhostProjectionLinearMap :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalDiffeomorphismGhostField period hPeriod where
  toFun := fun state => state.nonminimal.ghost
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalDiffeomorphismGhostFieldProjectionLinearMap :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      SmoothTangentField period hPeriod where
  toFun := fun state => state.nonminimal.ghost.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalDiffeomorphismAntighostFieldProjectionLinearMap :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      SmoothTangentField period hPeriod where
  toFun := fun state => state.nonminimal.antighost.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalDiffeomorphismBFieldProjectionLinearMap :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      SmoothTangentField period hPeriod where
  toFun := fun state => state.nonminimal.nakanishiLautrup.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linearized convention selected by the displayed action:
`s h = L_c g`, `s c = 0`, `s c̄ = B`, `s B = 0`. -/
def globalDiffeomorphismBRST
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    GlobalDiffeomorphismBRSTState period hPeriod where
  metricPerturbation :=
    globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod metric state.nonminimal.ghost
  nonminimal :=
    globalDiffeomorphismNonminimalBRST
      period hPeriod state.nonminimal

theorem globalDiffeomorphismBRST_square_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismBRST period hPeriod metric
        (globalDiffeomorphismBRST period hPeriod metric state) =
      zeroGlobalDiffeomorphismBRSTState period hPeriod := by
  apply GlobalDiffeomorphismBRSTState.ext
  · change
      globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
          period hPeriod metric
          (zeroGlobalDiffeomorphismGhostField period hPeriod) = 0
    exact
      (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
        period hPeriod metric).map_zero
  · exact globalDiffeomorphismNonminimalBRST_square_zero
      period hPeriod state.nonminimal

def globalDiffeomorphismGaugeConditionLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      EffectiveD8SmoothCovectorField
        (deDonderBackground period hPeriod) :=
  (globalGeneralMetricDeDonderLinearMap period hPeriod metric).comp
      (globalDiffeomorphismMetricPerturbationProjectionLinearMap
        period hPeriod) -
    (1 / 2 : Real) •
      ((globalSmoothMetricFlatLinearMap period hPeriod metric).comp
        (globalDiffeomorphismBFieldProjectionLinearMap
          period hPeriod))

@[simp]
theorem globalDiffeomorphismGaugeConditionLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismGaugeConditionLinearMap
        period hPeriod metric state =
      globalGeneralMetricDeDonderLinearMap period hPeriod metric
          state.metricPerturbation -
        (1 / 2 : Real) •
          globalSmoothMetricFlat period hPeriod metric
            state.nonminimal.nakanishiLautrup.field :=
  rfl

theorem globalDiffeomorphismGaugeCondition_BRST
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismGaugeConditionLinearMap period hPeriod metric
        (globalDiffeomorphismBRST period hPeriod metric state) =
      globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
        period hPeriod metric state.nonminimal.ghost := by
  rw [globalDiffeomorphismGaugeConditionLinearMap_apply]
  change
    globalGeneralMetricDeDonderLinearMap period hPeriod metric
        (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
          period hPeriod metric state.nonminimal.ghost) -
      (1 / 2 : Real) •
        globalSmoothMetricFlat period hPeriod metric 0 = _
  have hFlat :
      globalSmoothMetricFlat period hPeriod metric 0 = 0 :=
    (globalSmoothMetricFlatLinearMap period hPeriod metric).map_zero
  have hSmul :
      (1 / 2 : Real) •
          (0 : EffectiveD8SmoothCovectorField
            (deDonderBackground period hPeriod)) = 0 := by
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro tangent
    change (1 / 2 : Real) * 0 = 0
    ring
  rw [hFlat, hSmul, sub_zero]
  rfl

/-- The odd gauge fermion `Ψ = <c̄, D h - B♭/2>`. -/
def globalDiffeomorphismGaugeFermion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) : Real :=
  globalIntegratedCovectorVectorPairing period hPeriod metric
    (globalDiffeomorphismGaugeConditionLinearMap
      period hPeriod metric state)
    state.nonminimal.antighost.field

/-- Graded variation of the displayed odd gauge fermion. -/
def globalDiffeomorphismGaugeFermionBRSTVariation
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) : Real :=
  globalIntegratedCovectorVectorPairing period hPeriod metric
      (globalDiffeomorphismGaugeConditionLinearMap
        period hPeriod metric state)
      (globalDiffeomorphismBRST period hPeriod metric state
        ).nonminimal.antighost.field -
    globalIntegratedCovectorVectorPairing period hPeriod metric
      (globalDiffeomorphismGaugeConditionLinearMap period hPeriod metric
        (globalDiffeomorphismBRST period hPeriod metric state))
      state.nonminimal.antighost.field

def globalDiffeomorphismGaugeFermionBRSTMixedAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalDiffeomorphismBRSTState period hPeriod) : Real :=
  globalIntegratedCovectorVectorPairing period hPeriod metric
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric
        second.metricPerturbation)
      first.nonminimal.nakanishiLautrup.field -
    (1 / 2 : Real) *
      globalIntegratedCovectorVectorPairing period hPeriod metric
        (globalSmoothMetricFlat period hPeriod metric
          first.nonminimal.nakanishiLautrup.field)
        second.nonminimal.nakanishiLautrup.field -
    globalIntegratedCovectorVectorPairing period hPeriod metric
      (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
        period hPeriod metric second.nonminimal.ghost)
      first.nonminimal.antighost.field

theorem globalDiffeomorphismGaugeFermionBRSTVariation_formula
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod metric state =
      globalDiffeomorphismGaugeFermionBRSTMixedAction
        period hPeriod metric state state := by
  unfold globalDiffeomorphismGaugeFermionBRSTVariation
  change
    globalIntegratedCovectorVectorPairing period hPeriod metric
        (globalDiffeomorphismGaugeConditionLinearMap
          period hPeriod metric state)
        state.nonminimal.nakanishiLautrup.field -
      globalIntegratedCovectorVectorPairing period hPeriod metric
        (globalDiffeomorphismGaugeConditionLinearMap period hPeriod metric
          (globalDiffeomorphismBRST period hPeriod metric state))
        state.nonminimal.antighost.field = _
  rw [globalDiffeomorphismGaugeConditionLinearMap_apply,
    globalDiffeomorphismGaugeCondition_BRST,
    globalIntegratedCovectorVectorPairing_sub_left,
    globalIntegratedCovectorVectorPairing_smul_left]
  rfl

def globalDiffeomorphismGaugeFermionBRSTPolarizationAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalDiffeomorphismBRSTState period hPeriod) : Real :=
  globalDiffeomorphismGaugeFermionBRSTMixedAction
      period hPeriod metric first second +
    globalDiffeomorphismGaugeFermionBRSTMixedAction
      period hPeriod metric second first

/-! ## Faithful closed off-shell graph -/

abbrev GlobalDiffeomorphismOffShellTail4 :=
  WithLp 2
    (GlobalDiffeomorphismVectorL2 period hPeriod ×
      GlobalDiffeomorphismVectorL2 period hPeriod)

abbrev GlobalDiffeomorphismOffShellTail3 :=
  WithLp 2
    (GlobalDiffeomorphismVectorL2 period hPeriod ×
      GlobalDiffeomorphismOffShellTail4 period hPeriod)

abbrev GlobalDiffeomorphismOffShellTail2 :=
  WithLp 2
    (GlobalDiffeomorphismVectorL2 period hPeriod ×
      GlobalDiffeomorphismOffShellTail3 period hPeriod)

abbrev GlobalDiffeomorphismOffShellTail1 :=
  WithLp 2
    (GlobalDiffeomorphismVectorL2 period hPeriod ×
      GlobalDiffeomorphismOffShellTail2 period hPeriod)

abbrev GlobalDiffeomorphismOffShellFeatureIndex := Fin 5

abbrev GlobalDiffeomorphismOffShellFeatureTail :=
  PiLp 2 (fun _ : GlobalDiffeomorphismOffShellFeatureIndex =>
    GlobalDiffeomorphismVectorL2 period hPeriod)

abbrev GlobalDiffeomorphismOffShellAmbient
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  WithLp 2
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric ×
      GlobalDiffeomorphismOffShellFeatureTail period hPeriod)

local instance deDonderBaseGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderGraphHilbert
      period hPeriod metric)).toNormedSpace

local instance deDonderBaseGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderGraphHilbert
      period hPeriod metric)).toNormedSpace.toModule

local instance deDonderBaseGraphCompleteSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  globalGeneralMetricDeDonderGraphCompleteSpace
    period hPeriod metric

local instance deDonderPairingAmbientNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphAmbient
      period hPeriod metric)).toNormedSpace

local instance deDonderPairingAmbientModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance : InnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphAmbient
      period hPeriod metric)).toNormedSpace.toModule

local instance baseMetricGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  Submodule.normedSpace
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric)

local instance baseMetricGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  Submodule.module
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric)

local instance baseMetricGraphInnerProductSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  Submodule.innerProductSpace
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric)

local instance baseMetricGraphCompleteSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  globalGeneralMetricDeDonderPairingGraphCompleteSpace
    period hPeriod metric

local instance (priority := 10000)
    globalDiffeomorphismOffShellAmbientInnerProductSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalDiffeomorphismOffShellAmbient period hPeriod metric) :=
  @WithLp.instProdInnerProductSpace Real
    (GlobalGeneralMetricDeDonderPairingGraphHilbert
      period hPeriod metric)
    (GlobalDiffeomorphismOffShellFeatureTail period hPeriod)
    inferInstance inferInstance
    (baseMetricGraphInnerProductSpace period hPeriod metric)
    inferInstance inferInstance

local instance (priority := 10000)
    globalDiffeomorphismOffShellAmbientNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalDiffeomorphismOffShellAmbient period hPeriod metric) :=
  (globalDiffeomorphismOffShellAmbientInnerProductSpace
    period hPeriod metric).toNormedSpace


def globalDiffeomorphismOffShellAmbientLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalDiffeomorphismOffShellAmbient period hPeriod metric where
  toFun := fun state => WithLp.toLp 2
    (globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod metric state.metricPerturbation,
      WithLp.toLp 2 ![
        globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          state.nonminimal.nakanishiLautrup.field,
        globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric
          state.nonminimal.nakanishiLautrup.field,
        globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          state.nonminimal.antighost.field,
        globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          state.nonminimal.ghost.field,
        globalDiffeomorphismFPL2LinearMap period hPeriod metric
          state.nonminimal.ghost])
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric).map_add
            first.metricPerturbation second.metricPerturbation
    · apply PiLp.ext
      intro index
      fin_cases index
      · exact
          (globalNormalizedVectorFrameL2LinearMap
            period hPeriod metric).map_add _ _
      · exact
          (globalSmoothMetricFlatFrameL2LinearMap
            period hPeriod metric).map_add _ _
      · exact
          (globalNormalizedVectorFrameL2LinearMap
            period hPeriod metric).map_add _ _
      · exact
          (globalNormalizedVectorFrameL2LinearMap
            period hPeriod metric).map_add _ _
      · exact
          (globalDiffeomorphismFPL2LinearMap
            period hPeriod metric).map_add _ _
  map_smul' scalar state := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rw [show (scalar • state).metricPerturbation =
          scalar • state.metricPerturbation from
        (globalDiffeomorphismMetricPerturbationProjectionLinearMap
          period hPeriod).map_smul scalar state]
      change
        globalGeneralMetricDeDonderPairingSmoothEmbedding
            period hPeriod metric (scalar • state.metricPerturbation) =
          scalar •
            globalGeneralMetricDeDonderPairingSmoothEmbedding
              period hPeriod metric state.metricPerturbation
      exact
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric).map_smul scalar state.metricPerturbation
    · apply PiLp.ext
      intro index
      fin_cases index
      · rw [show (scalar • state).nonminimal.nakanishiLautrup.field =
            scalar • state.nonminimal.nakanishiLautrup.field from
          (globalDiffeomorphismBFieldProjectionLinearMap
            period hPeriod).map_smul scalar state]
        change
          globalNormalizedVectorFrameL2LinearMap period hPeriod metric
              (scalar • state.nonminimal.nakanishiLautrup.field) =
            scalar • globalNormalizedVectorFrameL2LinearMap
              period hPeriod metric
                state.nonminimal.nakanishiLautrup.field
        exact
          (globalNormalizedVectorFrameL2LinearMap
            period hPeriod metric).map_smul _ _
      · rw [show (scalar • state).nonminimal.nakanishiLautrup.field =
            scalar • state.nonminimal.nakanishiLautrup.field from
          (globalDiffeomorphismBFieldProjectionLinearMap
            period hPeriod).map_smul scalar state]
        change
          globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric
              (scalar • state.nonminimal.nakanishiLautrup.field) =
            scalar • globalSmoothMetricFlatFrameL2LinearMap
              period hPeriod metric
                state.nonminimal.nakanishiLautrup.field
        exact
          (globalSmoothMetricFlatFrameL2LinearMap
            period hPeriod metric).map_smul _ _
      · rw [show (scalar • state).nonminimal.antighost.field =
            scalar • state.nonminimal.antighost.field from
          (globalDiffeomorphismAntighostFieldProjectionLinearMap
            period hPeriod).map_smul scalar state]
        change
          globalNormalizedVectorFrameL2LinearMap period hPeriod metric
              (scalar • state.nonminimal.antighost.field) =
            scalar • globalNormalizedVectorFrameL2LinearMap
              period hPeriod metric state.nonminimal.antighost.field
        exact
          (globalNormalizedVectorFrameL2LinearMap
            period hPeriod metric).map_smul _ _
      · rw [show (scalar • state).nonminimal.ghost.field =
            scalar • state.nonminimal.ghost.field from
          (globalDiffeomorphismGhostFieldProjectionLinearMap
            period hPeriod).map_smul scalar state]
        change
          globalNormalizedVectorFrameL2LinearMap period hPeriod metric
              (scalar • state.nonminimal.ghost.field) =
            scalar • globalNormalizedVectorFrameL2LinearMap
              period hPeriod metric state.nonminimal.ghost.field
        exact
          (globalNormalizedVectorFrameL2LinearMap
            period hPeriod metric).map_smul _ _
      · rw [show (scalar • state).nonminimal.ghost =
            scalar • state.nonminimal.ghost from
          (globalDiffeomorphismGhostProjectionLinearMap
            period hPeriod).map_smul scalar state]
        change
          globalDiffeomorphismFPL2LinearMap period hPeriod metric
              (scalar • state.nonminimal.ghost) =
            scalar • globalDiffeomorphismFPL2LinearMap
              period hPeriod metric state.nonminimal.ghost
        exact
          (globalDiffeomorphismFPL2LinearMap
            period hPeriod metric).map_smul _ _

def globalDiffeomorphismOffShellGraphSubmodule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalDiffeomorphismOffShellAmbient period hPeriod metric) :=
  (LinearMap.range
    (globalDiffeomorphismOffShellAmbientLinearMap
      period hPeriod metric)).topologicalClosure

def GlobalDiffeomorphismOffShellGraphHilbert
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismOffShellGraphSubmodule period hPeriod metric

local instance (priority := 10000)
    globalDiffeomorphismOffShellGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  @Submodule.normedSpace Real Real
    inferInstance inferInstance inferInstance
    (GlobalDiffeomorphismOffShellAmbient period hPeriod metric)
    inferInstance
    (globalDiffeomorphismOffShellAmbientNormedSpace
      period hPeriod metric)
    inferInstance inferInstance
    (globalDiffeomorphismOffShellGraphSubmodule
      period hPeriod metric)

local instance (priority := 10000)
    globalDiffeomorphismOffShellGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  Submodule.module
    (globalDiffeomorphismOffShellGraphSubmodule
      period hPeriod metric)

local instance (priority := 10000)
    globalDiffeomorphismOffShellGraphInnerProductSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) :=
  @Submodule.innerProductSpace Real
    (GlobalDiffeomorphismOffShellAmbient period hPeriod metric)
    inferInstance inferInstance
    (globalDiffeomorphismOffShellAmbientInnerProductSpace
      period hPeriod metric)
    (globalDiffeomorphismOffShellGraphSubmodule
      period hPeriod metric)

def globalDiffeomorphismOffShellSmoothEmbedding
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric where
  toFun state :=
    ⟨globalDiffeomorphismOffShellAmbientLinearMap
        period hPeriod metric state,
      (LinearMap.range
        (globalDiffeomorphismOffShellAmbientLinearMap
          period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalDiffeomorphismOffShellAmbientLinearMap
            period hPeriod metric) state)⟩
  map_add' first second := Subtype.ext
    ((globalDiffeomorphismOffShellAmbientLinearMap
      period hPeriod metric).map_add first second)
  map_smul' scalar state := Subtype.ext
    ((globalDiffeomorphismOffShellAmbientLinearMap
      period hPeriod metric).map_smul scalar state)

theorem globalDiffeomorphismOffShellSmoothEmbedding_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric) := by
  intro first second hEqual
  have hAmbient := congrArg Subtype.val hEqual
  have hMetricCoordinates :
      globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric first.metricPerturbation =
        globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric second.metricPerturbation :=
    congrArg
      (fun value : GlobalDiffeomorphismOffShellAmbient
          period hPeriod metric => WithLp.fst value) hAmbient
  have hBCoordinates :
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          first.nonminimal.nakanishiLautrup.field =
        globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          second.nonminimal.nakanishiLautrup.field :=
    congrArg
      (fun value : GlobalDiffeomorphismOffShellAmbient
          period hPeriod metric =>
        (WithLp.snd value)
          (0 : GlobalDiffeomorphismOffShellFeatureIndex)) hAmbient
  have hAntighostCoordinates :
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          first.nonminimal.antighost.field =
        globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          second.nonminimal.antighost.field :=
    congrArg
      (fun value : GlobalDiffeomorphismOffShellAmbient
          period hPeriod metric =>
        (WithLp.snd value)
          (2 : GlobalDiffeomorphismOffShellFeatureIndex)) hAmbient
  have hGhostCoordinates :
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          first.nonminimal.ghost.field =
        globalNormalizedVectorFrameL2LinearMap period hPeriod metric
          second.nonminimal.ghost.field :=
    congrArg
      (fun value : GlobalDiffeomorphismOffShellAmbient
          period hPeriod metric =>
        (WithLp.snd value)
          (3 : GlobalDiffeomorphismOffShellFeatureIndex))
      hAmbient
  have hMetric :=
    globalGeneralMetricDeDonderPairingSmoothEmbedding_injective
      period hPeriod metric hMetricCoordinates
  have hB :=
    globalNormalizedVectorFrameL2LinearMap_injective
      period hPeriod metric hBCoordinates
  have hAntighost :=
    globalNormalizedVectorFrameL2LinearMap_injective
      period hPeriod metric hAntighostCoordinates
  have hGhost :=
    globalNormalizedVectorFrameL2LinearMap_injective
      period hPeriod metric hGhostCoordinates
  apply GlobalDiffeomorphismBRSTState.ext
  · exact hMetric
  · apply GlobalDiffeomorphismNonminimalFields.ext
    · exact GlobalDiffeomorphismGhostField.ext hGhost
    · exact GlobalDiffeomorphismAntighostField.ext hAntighost
    · exact GlobalDiffeomorphismNakanishiLautrupField.ext hB

theorem globalDiffeomorphismOffShellSmoothEmbedding_denseRange
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  unfold GlobalDiffeomorphismOffShellGraphHilbert
    globalDiffeomorphismOffShellGraphSubmodule
  let graph := globalDiffeomorphismOffShellAmbientLinearMap
    period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalDiffeomorphismOffShellSmoothEmbedding
            period hPeriod metric) =
        (LinearMap.range graph :
          Set (GlobalDiffeomorphismOffShellAmbient
            period hPeriod metric)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨state, rfl⟩, rfl⟩
      exact ⟨state, rfl⟩
    · rintro ⟨state, rfl⟩
      exact
        ⟨globalDiffeomorphismOffShellSmoothEmbedding
            period hPeriod metric state,
          ⟨state, rfl⟩, rfl⟩
  change closure
      (LinearMap.range graph :
        Set (GlobalDiffeomorphismOffShellAmbient period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric))
  rw [hRange]

@[implicit_reducible]
def globalDiffeomorphismOffShellGraphCompleteSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalDiffeomorphismOffShellGraphHilbert
        period hPeriod metric) := by
  unfold GlobalDiffeomorphismOffShellGraphHilbert
    globalDiffeomorphismOffShellGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalDiffeomorphismOffShellAmbientLinearMap
        period hPeriod metric))

def globalDiffeomorphismOffShellAmbientProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellAmbient period hPeriod metric :=
  (globalDiffeomorphismOffShellGraphSubmodule
    period hPeriod metric).subtypeL


def globalDiffeomorphismOffShellMetricProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric :=
  (WithLp.fstL 2 Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
      (GlobalDiffeomorphismOffShellFeatureTail period hPeriod)).comp
    (globalDiffeomorphismOffShellAmbientProjection
      period hPeriod metric)

def globalDiffeomorphismOffShellDeDonderProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalGeneralMetricDeDonderPairingFeatureProjection
    period hPeriod metric).comp
      (globalDiffeomorphismOffShellMetricProjection
        period hPeriod metric)

def globalDiffeomorphismOffShellFeatureTailProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellFeatureTail period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)
      (GlobalDiffeomorphismOffShellFeatureTail period hPeriod)).comp
    (globalDiffeomorphismOffShellAmbientProjection
      period hPeriod metric)

def globalDiffeomorphismOffShellFeatureProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : GlobalDiffeomorphismOffShellFeatureIndex) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (PiLp.proj 2
      (fun _ : GlobalDiffeomorphismOffShellFeatureIndex =>
        GlobalDiffeomorphismVectorL2 period hPeriod) index).comp
    (globalDiffeomorphismOffShellFeatureTailProjection
      period hPeriod metric)

def globalDiffeomorphismOffShellBProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismOffShellFeatureProjection
    period hPeriod metric (0 : GlobalDiffeomorphismOffShellFeatureIndex)

def globalDiffeomorphismOffShellBFlatProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismOffShellFeatureProjection
    period hPeriod metric (1 : GlobalDiffeomorphismOffShellFeatureIndex)

def globalDiffeomorphismOffShellAntighostProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismOffShellFeatureProjection
    period hPeriod metric (2 : GlobalDiffeomorphismOffShellFeatureIndex)

def globalDiffeomorphismOffShellGhostProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismOffShellFeatureProjection
    period hPeriod metric (3 : GlobalDiffeomorphismOffShellFeatureIndex)

def globalDiffeomorphismOffShellFPProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalDiffeomorphismOffShellFeatureProjection
    period hPeriod metric (4 : GlobalDiffeomorphismOffShellFeatureIndex)

@[simp]
theorem globalDiffeomorphismOffShellDeDonderProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellDeDonderProjection period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric
        state.metricPerturbation :=
  rfl

@[simp]
theorem globalDiffeomorphismOffShellBProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellBProjection period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        state.nonminimal.nakanishiLautrup.field :=
  rfl

@[simp]
theorem globalDiffeomorphismOffShellBFlatProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellBFlatProjection period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric
        state.nonminimal.nakanishiLautrup.field :=
  rfl

@[simp]
theorem globalDiffeomorphismOffShellAntighostProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellAntighostProjection period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        state.nonminimal.antighost.field :=
  rfl

@[simp]
theorem globalDiffeomorphismOffShellGhostProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellGhostProjection period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        state.nonminimal.ghost.field :=
  rfl

@[simp]
theorem globalDiffeomorphismOffShellFPProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellFPProjection period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalDiffeomorphismFPL2LinearMap period hPeriod metric
        state.nonminimal.ghost :=
  rfl

/-! ## Bounded Hessian and Riesz representative -/

private def realInnerBilinearComp
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [InnerProductSpace Real F]
    (first second : E →L[Real] F) :
    E →L[Real] E →L[Real] Real :=
  (innerSL Real).bilinearComp first second

private def globalDiffeomorphismOffShellInnerBilinearComp
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
        GlobalDiffeomorphismVectorL2 period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
        Real :=
  @realInnerBilinearComp
    (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric)
    (GlobalDiffeomorphismVectorL2 period hPeriod)
    inferInstance
    (globalDiffeomorphismOffShellGraphNormedSpace period hPeriod metric)
    inferInstance inferInstance first second

/-- Polarized Hessian of the mono-metric off-shell BRST action. -/
def globalDiffeomorphismOffShellHessian
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
        Real :=
  globalDiffeomorphismOffShellInnerBilinearComp period hPeriod metric
      (globalDiffeomorphismOffShellDeDonderProjection period hPeriod metric)
      (globalDiffeomorphismOffShellBProjection period hPeriod metric) +
    globalDiffeomorphismOffShellInnerBilinearComp period hPeriod metric
      (globalDiffeomorphismOffShellBProjection period hPeriod metric)
      (globalDiffeomorphismOffShellDeDonderProjection period hPeriod metric) -
    (1 / 2 : Real) •
      globalDiffeomorphismOffShellInnerBilinearComp period hPeriod metric
        (globalDiffeomorphismOffShellBFlatProjection period hPeriod metric)
        (globalDiffeomorphismOffShellBProjection period hPeriod metric) -
    (1 / 2 : Real) •
      globalDiffeomorphismOffShellInnerBilinearComp period hPeriod metric
        (globalDiffeomorphismOffShellBProjection period hPeriod metric)
        (globalDiffeomorphismOffShellBFlatProjection period hPeriod metric) -
    globalDiffeomorphismOffShellInnerBilinearComp period hPeriod metric
      (globalDiffeomorphismOffShellFPProjection period hPeriod metric)
      (globalDiffeomorphismOffShellAntighostProjection
        period hPeriod metric) -
    globalDiffeomorphismOffShellInnerBilinearComp period hPeriod metric
      (globalDiffeomorphismOffShellAntighostProjection
        period hPeriod metric)
      (globalDiffeomorphismOffShellFPProjection period hPeriod metric)

@[simp]
theorem globalDiffeomorphismOffShellHessian_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    globalDiffeomorphismOffShellHessian period hPeriod metric first second =
      inner Real
          (globalDiffeomorphismOffShellDeDonderProjection
            period hPeriod metric first)
          (globalDiffeomorphismOffShellBProjection
            period hPeriod metric second) +
        inner Real
          (globalDiffeomorphismOffShellBProjection
            period hPeriod metric first)
          (globalDiffeomorphismOffShellDeDonderProjection
            period hPeriod metric second) -
        (1 / 2 : Real) * inner Real
          (globalDiffeomorphismOffShellBFlatProjection
            period hPeriod metric first)
          (globalDiffeomorphismOffShellBProjection
            period hPeriod metric second) -
        (1 / 2 : Real) * inner Real
          (globalDiffeomorphismOffShellBProjection
            period hPeriod metric first)
          (globalDiffeomorphismOffShellBFlatProjection
            period hPeriod metric second) -
        inner Real
          (globalDiffeomorphismOffShellFPProjection
            period hPeriod metric first)
          (globalDiffeomorphismOffShellAntighostProjection
            period hPeriod metric second) -
        inner Real
          (globalDiffeomorphismOffShellAntighostProjection
            period hPeriod metric first)
          (globalDiffeomorphismOffShellFPProjection
            period hPeriod metric second) :=
  rfl

theorem globalDiffeomorphismOffShellHessian_comm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    globalDiffeomorphismOffShellHessian period hPeriod metric first second =
      globalDiffeomorphismOffShellHessian
        period hPeriod metric second first := by
  let dFirst := globalDiffeomorphismOffShellDeDonderProjection
    period hPeriod metric first
  let dSecond := globalDiffeomorphismOffShellDeDonderProjection
    period hPeriod metric second
  let bFirst := globalDiffeomorphismOffShellBProjection
    period hPeriod metric first
  let bSecond := globalDiffeomorphismOffShellBProjection
    period hPeriod metric second
  let flatFirst := globalDiffeomorphismOffShellBFlatProjection
    period hPeriod metric first
  let flatSecond := globalDiffeomorphismOffShellBFlatProjection
    period hPeriod metric second
  let fpFirst := globalDiffeomorphismOffShellFPProjection
    period hPeriod metric first
  let fpSecond := globalDiffeomorphismOffShellFPProjection
    period hPeriod metric second
  let barFirst := globalDiffeomorphismOffShellAntighostProjection
    period hPeriod metric first
  let barSecond := globalDiffeomorphismOffShellAntighostProjection
    period hPeriod metric second
  rw [globalDiffeomorphismOffShellHessian_apply,
    globalDiffeomorphismOffShellHessian_apply]
  change
    inner Real dFirst bSecond + inner Real bFirst dSecond -
        (1 / 2 : Real) * inner Real flatFirst bSecond -
        (1 / 2 : Real) * inner Real bFirst flatSecond -
        inner Real fpFirst barSecond - inner Real barFirst fpSecond =
      inner Real dSecond bFirst + inner Real bSecond dFirst -
        (1 / 2 : Real) * inner Real flatSecond bFirst -
        (1 / 2 : Real) * inner Real bSecond flatFirst -
        inner Real fpSecond barFirst - inner Real barSecond fpFirst
  rw [real_inner_comm dFirst bSecond,
    real_inner_comm dSecond bFirst,
    real_inner_comm flatFirst bSecond,
    real_inner_comm flatSecond bFirst,
    real_inner_comm fpFirst barSecond,
    real_inner_comm fpSecond barFirst]
  ring

private def realAdjointComp
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    (first second : E →L[Real] F) : E →L[Real] E :=
  second.adjoint.comp first

private theorem realAdjointComp_pairing
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    (first second : E →L[Real] F) (x y : E) :
    inner Real (realAdjointComp first second x) y =
      inner Real (first x) (second y) := by
  unfold realAdjointComp
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

private def globalDiffeomorphismOffShellAdjointComp
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
        GlobalDiffeomorphismVectorL2 period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric :=
  @realAdjointComp
    (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric)
    (GlobalDiffeomorphismVectorL2 period hPeriod)
    inferInstance
    (globalDiffeomorphismOffShellGraphInnerProductSpace
      period hPeriod metric)
    (globalDiffeomorphismOffShellGraphCompleteSpace period hPeriod metric)
    inferInstance inferInstance inferInstance first second

private theorem globalDiffeomorphismOffShellAdjointComp_pairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
        GlobalDiffeomorphismVectorL2 period hPeriod)
    (x y : GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) :
    inner Real
        (globalDiffeomorphismOffShellAdjointComp
          period hPeriod metric first second x) y =
      inner Real (first x) (second y) :=
  @realAdjointComp_pairing
    (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric)
    (GlobalDiffeomorphismVectorL2 period hPeriod)
    inferInstance
    (globalDiffeomorphismOffShellGraphInnerProductSpace
      period hPeriod metric)
    (globalDiffeomorphismOffShellGraphCompleteSpace period hPeriod metric)
    inferInstance inferInstance inferInstance
    first second x y

private def realOffShellRieszCombination
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (deDonderB bDeDonder flatB bFlat fpBar barFP : E →L[Real] E) :
    E →L[Real] E :=
  deDonderB + bDeDonder - (1 / 2 : Real) • flatB -
    (1 / 2 : Real) • bFlat - fpBar - barFP

private def realOffShellRieszFromFeatures
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    (deDonder b flat fp bar : E →L[Real] F) : E →L[Real] E :=
  realOffShellRieszCombination
    (realAdjointComp deDonder b)
    (realAdjointComp b deDonder)
    (realAdjointComp flat b)
    (realAdjointComp b flat)
    (realAdjointComp fp bar)
    (realAdjointComp bar fp)

private theorem realOffShellRieszFromFeatures_pairing
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    (deDonder b flat fp bar : E →L[Real] F) (x y : E) :
    inner Real
        (realOffShellRieszFromFeatures deDonder b flat fp bar x) y =
      inner Real (deDonder x) (b y) +
        inner Real (b x) (deDonder y) -
        (1 / 2 : Real) * inner Real (flat x) (b y) -
        (1 / 2 : Real) * inner Real (b x) (flat y) -
        inner Real (fp x) (bar y) - inner Real (bar x) (fp y) := by
  unfold realOffShellRieszFromFeatures realOffShellRieszCombination
  simp only [add_apply, sub_apply, smul_apply, inner_add_left,
    inner_sub_left, inner_smul_left]
  rw [realAdjointComp_pairing, realAdjointComp_pairing,
    realAdjointComp_pairing, realAdjointComp_pairing,
    realAdjointComp_pairing, realAdjointComp_pairing]
  simp

/-- Bounded Riesz representative of the mono-metric off-shell Hessian. -/
def globalDiffeomorphismOffShellRieszOperator
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric :=
  @realOffShellRieszFromFeatures
    (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric)
    (GlobalDiffeomorphismVectorL2 period hPeriod)
    inferInstance
    (globalDiffeomorphismOffShellGraphInnerProductSpace
      period hPeriod metric)
    (globalDiffeomorphismOffShellGraphCompleteSpace period hPeriod metric)
    inferInstance inferInstance inferInstance
    (globalDiffeomorphismOffShellDeDonderProjection period hPeriod metric)
    (globalDiffeomorphismOffShellBProjection period hPeriod metric)
    (globalDiffeomorphismOffShellBFlatProjection period hPeriod metric)
    (globalDiffeomorphismOffShellFPProjection period hPeriod metric)
    (globalDiffeomorphismOffShellAntighostProjection period hPeriod metric)

theorem globalDiffeomorphismOffShellRieszOperator_pairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    inner Real
        (globalDiffeomorphismOffShellRieszOperator
          period hPeriod metric first) second =
      globalDiffeomorphismOffShellHessian
        period hPeriod metric first second := by
  rw [globalDiffeomorphismOffShellHessian_apply]
  exact @realOffShellRieszFromFeatures_pairing
    (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric)
    (GlobalDiffeomorphismVectorL2 period hPeriod)
    inferInstance
    (globalDiffeomorphismOffShellGraphInnerProductSpace
      period hPeriod metric)
    (globalDiffeomorphismOffShellGraphCompleteSpace period hPeriod metric)
    inferInstance inferInstance inferInstance
    (globalDiffeomorphismOffShellDeDonderProjection period hPeriod metric)
    (globalDiffeomorphismOffShellBProjection period hPeriod metric)
    (globalDiffeomorphismOffShellBFlatProjection period hPeriod metric)
    (globalDiffeomorphismOffShellFPProjection period hPeriod metric)
    (globalDiffeomorphismOffShellAntighostProjection period hPeriod metric)
    first second

theorem globalDiffeomorphismOffShellRieszOperator_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    inner Real
        (globalDiffeomorphismOffShellRieszOperator
          period hPeriod metric first) second =
      inner Real first
        (globalDiffeomorphismOffShellRieszOperator
          period hPeriod metric second) := by
  rw [globalDiffeomorphismOffShellRieszOperator_pairing,
    globalDiffeomorphismOffShellHessian_comm,
    ← globalDiffeomorphismOffShellRieszOperator_pairing]
  exact real_inner_comm _ _

/-! ## Exact smooth-core action and C² extension -/

theorem globalGeneralMetricDeDonderFrameL2_inner_normalizedVector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    inner Real
        (globalGeneralMetricDeDonderFrameL2LinearMap
          period hPeriod metric tensor)
        (globalNormalizedVectorFrameL2LinearMap
          period hPeriod metric vector) =
      globalIntegratedCovectorVectorPairing period hPeriod metric
        (globalGeneralMetricDeDonderLinearMap
          period hPeriod metric tensor) vector := by
  change inner Real
      (globalSmoothCovectorFrameL2LinearMap period hPeriod
        (globalGeneralMetricDeDonderLinearMap
          period hPeriod metric tensor))
      (globalNormalizedVectorFrameL2LinearMap
        period hPeriod metric vector) = _
  exact globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing
    period hPeriod metric _ _

theorem globalSmoothMetricFlatFrameL2_inner_normalizedVector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothTangentField period hPeriod) :
    inner Real
        (globalSmoothMetricFlatFrameL2LinearMap
          period hPeriod metric first)
        (globalNormalizedVectorFrameL2LinearMap
          period hPeriod metric second) =
      globalIntegratedCovectorVectorPairing period hPeriod metric
        (globalSmoothMetricFlat period hPeriod metric first) second := by
  change inner Real
      (globalSmoothCovectorFrameL2LinearMap period hPeriod
        (globalSmoothMetricFlat period hPeriod metric first))
      (globalNormalizedVectorFrameL2LinearMap
        period hPeriod metric second) = _
  exact globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing
    period hPeriod metric _ _

theorem globalDiffeomorphismFPL2_inner_normalizedVector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    inner Real
        (globalDiffeomorphismFPL2LinearMap
          period hPeriod metric ghost)
        (globalNormalizedVectorFrameL2LinearMap
          period hPeriod metric vector) =
      globalIntegratedCovectorVectorPairing period hPeriod metric
        (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
          period hPeriod metric ghost) vector := by
  change inner Real
      (globalSmoothCovectorFrameL2LinearMap period hPeriod
        (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
          period hPeriod metric ghost))
      (globalNormalizedVectorFrameL2LinearMap
        period hPeriod metric vector) = _
  exact globalSmoothCovectorNormalizedVectorL2_inner_eq_pairing
    period hPeriod metric _ _

theorem globalDiffeomorphismGaugeFermionBRSTMixedAction_eq_offShell_inner
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismGaugeFermionBRSTMixedAction
        period hPeriod metric first second =
      inner Real
          (globalGeneralMetricDeDonderFrameL2LinearMap
            period hPeriod metric second.metricPerturbation)
          (globalNormalizedVectorFrameL2LinearMap period hPeriod metric
            first.nonminimal.nakanishiLautrup.field) -
        (1 / 2 : Real) * inner Real
          (globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric
            first.nonminimal.nakanishiLautrup.field)
          (globalNormalizedVectorFrameL2LinearMap period hPeriod metric
            second.nonminimal.nakanishiLautrup.field) -
        inner Real
          (globalDiffeomorphismFPL2LinearMap period hPeriod metric
            second.nonminimal.ghost)
          (globalNormalizedVectorFrameL2LinearMap period hPeriod metric
            first.nonminimal.antighost.field) := by
  unfold globalDiffeomorphismGaugeFermionBRSTMixedAction
  rw [globalGeneralMetricDeDonderFrameL2_inner_normalizedVector,
    globalSmoothMetricFlatFrameL2_inner_normalizedVector,
    globalDiffeomorphismFPL2_inner_normalizedVector]

theorem globalDiffeomorphismOffShellHessian_smooth_eq_BRST
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellHessian period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric first)
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric second) =
      globalDiffeomorphismGaugeFermionBRSTPolarizationAction
        period hPeriod metric first second := by
  rw [globalDiffeomorphismOffShellHessian_apply]
  simp only [globalDiffeomorphismOffShellDeDonderProjection_smooth,
    globalDiffeomorphismOffShellBProjection_smooth,
    globalDiffeomorphismOffShellBFlatProjection_smooth,
    globalDiffeomorphismOffShellAntighostProjection_smooth,
    globalDiffeomorphismOffShellFPProjection_smooth]
  unfold globalDiffeomorphismGaugeFermionBRSTPolarizationAction
  rw [globalDiffeomorphismGaugeFermionBRSTMixedAction_eq_offShell_inner,
    globalDiffeomorphismGaugeFermionBRSTMixedAction_eq_offShell_inner]
  rw [real_inner_comm
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        first.nonminimal.nakanishiLautrup.field)
      (globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric
        second.metricPerturbation),
    real_inner_comm
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        first.nonminimal.nakanishiLautrup.field)
      (globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric
        second.nonminimal.nakanishiLautrup.field),
    real_inner_comm
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        first.nonminimal.antighost.field)
      (globalDiffeomorphismFPL2LinearMap period hPeriod metric
        second.nonminimal.ghost)]
  ring

/-- Quadratic graph action extending the linearized integrated `sΨ`. -/
def globalDiffeomorphismOffShellGraphAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) : Real :=
  (1 / 2 : Real) *
    globalDiffeomorphismOffShellHessian period hPeriod metric state state

theorem globalDiffeomorphismOffShellGraphAction_smooth_eq_BRST
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellGraphAction period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric state) =
      globalDiffeomorphismGaugeFermionBRSTVariation
        period hPeriod metric state := by
  unfold globalDiffeomorphismOffShellGraphAction
  rw [globalDiffeomorphismOffShellHessian_smooth_eq_BRST]
  unfold globalDiffeomorphismGaugeFermionBRSTPolarizationAction
  rw [globalDiffeomorphismGaugeFermionBRSTVariation_formula]
  ring

private theorem realSymmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second,
      bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

private theorem realSymmetricQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real) :
    ContDiff Real ⊤ (fun state => (1 / 2 : Real) * bilinear state state) :=
  contDiff_const.mul (bilinear.contDiff.clm_apply contDiff_id)

theorem globalDiffeomorphismOffShellGraphAction_hasFDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismOffShellGraphHilbert
      period hPeriod metric) :
    HasFDerivAt
      (globalDiffeomorphismOffShellGraphAction period hPeriod metric)
      (globalDiffeomorphismOffShellHessian period hPeriod metric state)
      state :=
  @realSymmetricQuadratic_hasFDerivAt
    (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric)
    inferInstance
    (globalDiffeomorphismOffShellGraphNormedSpace period hPeriod metric)
    (globalDiffeomorphismOffShellHessian period hPeriod metric)
    (globalDiffeomorphismOffShellHessian_comm period hPeriod metric)
    state

theorem globalDiffeomorphismOffShellGraphAction_contDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (globalDiffeomorphismOffShellGraphAction period hPeriod metric) :=
  @realSymmetricQuadratic_contDiff
    (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric)
    inferInstance
    (globalDiffeomorphismOffShellGraphNormedSpace period hPeriod metric)
    (globalDiffeomorphismOffShellHessian period hPeriod metric)

theorem globalDiffeomorphismOffShellGraphAction_contDiff_two
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (globalDiffeomorphismOffShellGraphAction period hPeriod metric) :=
  (globalDiffeomorphismOffShellGraphAction_contDiff
    period hPeriod metric).of_le (by simp)

/-! ## Canonical raccord to the typed diffeomorphism triple -/

/-- Inclusion of the diffeomorphism triple into the existing typed packet,
with both Abelian triples fixed at zero. -/
def globalDiffeomorphismNonminimalTypedInclusionLinearMap :
    GlobalDiffeomorphismNonminimalFields period hPeriod →ₗ[Real]
      GlobalTypedNonminimalFields period hPeriod where
  toFun nonminimal :=
    { abelian := fun _ => 0
      diffeomorphism := nonminimal }
  map_add' first second := by
    apply GlobalTypedNonminimalFields.ext
    · funext sector
      change (0 : GlobalAbelianNonminimalFields period hPeriod) = 0 + 0
      exact (zero_add 0).symm
    · rfl
  map_smul' scalar nonminimal := by
    apply GlobalTypedNonminimalFields.ext
    · funext sector
      change (0 : GlobalAbelianNonminimalFields period hPeriod) = scalar • 0
      exact (smul_zero scalar).symm
    · rfl

@[simp]
theorem globalDiffeomorphismNonminimalTypedInclusion_abelian
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    (globalDiffeomorphismNonminimalTypedInclusionLinearMap
      period hPeriod nonminimal).abelian = fun _ => 0 :=
  rfl

@[simp]
theorem globalDiffeomorphismNonminimalTypedInclusion_diffeomorphism
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    (globalDiffeomorphismNonminimalTypedInclusionLinearMap
      period hPeriod nonminimal).diffeomorphism = nonminimal :=
  rfl

theorem globalDiffeomorphismNonminimalTypedInclusion_injective :
    Function.Injective
      (globalDiffeomorphismNonminimalTypedInclusionLinearMap
        period hPeriod) := by
  intro first second hEqual
  exact congrArg GlobalTypedNonminimalFields.diffeomorphism hEqual

theorem globalDiffeomorphismNonminimalTypedInclusion_BRST
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalTypedNonminimalBRST period hPeriod
        (globalDiffeomorphismNonminimalTypedInclusionLinearMap
          period hPeriod nonminimal) =
      globalDiffeomorphismNonminimalTypedInclusionLinearMap
        period hPeriod
        (globalDiffeomorphismNonminimalBRST
          period hPeriod nonminimal) :=
  rfl

/-- The analytic graph point paired with its exact pre-existing typed
diffeomorphism triple; no Candidate-A metric choice is made. -/
def globalDiffeomorphismOffShellGraphTypedCoreLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      (GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric ×
        GlobalTypedNonminimalFields period hPeriod) where
  toFun state :=
    (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric state,
      globalDiffeomorphismNonminimalTypedInclusionLinearMap
        period hPeriod state.nonminimal)
  map_add' first second := by
    apply Prod.ext
    · exact (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric).map_add first second
    · exact (globalDiffeomorphismNonminimalTypedInclusionLinearMap
        period hPeriod).map_add first.nonminimal second.nonminimal
  map_smul' scalar state := by
    apply Prod.ext
    · exact (globalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric).map_smul scalar state
    · exact (globalDiffeomorphismNonminimalTypedInclusionLinearMap
        period hPeriod).map_smul scalar state.nonminimal

@[simp]
theorem globalDiffeomorphismOffShellGraphTypedCore_diffeomorphism
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    (globalDiffeomorphismOffShellGraphTypedCoreLinearMap
      period hPeriod metric state).2.diffeomorphism = state.nonminimal :=
  rfl

theorem globalDiffeomorphismOffShellGraphTypedCoreLinearMap_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismOffShellGraphTypedCoreLinearMap
        period hPeriod metric) := by
  intro first second hEqual
  apply globalDiffeomorphismOffShellSmoothEmbedding_injective
    period hPeriod metric
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
end JanusFormal
