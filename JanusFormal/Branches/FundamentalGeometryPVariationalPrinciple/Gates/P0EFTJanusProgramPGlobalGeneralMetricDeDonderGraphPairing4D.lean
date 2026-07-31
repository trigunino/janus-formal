import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderGaugePairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D

/-!
# Exact Lorentz pairing on a refined de Donder graph

The finite partition-weighted tangent generators admit an exact global
reconstruction formula.  Applied to the raised de Donder field, that formula
factorizes the physical inverse-metric pairing into finitely many scalar
`L²` pairings with the existing relative volume ratio.

Closing the graph of these genuine geometric features gives a faithful
Hilbert chart on which the unchanged Lorentzian de Donder pairing is bounded.
No positive replacement of the Lorentz pairing, formal adjoint, or Fredholm
claim is used here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderGaugePairing4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

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

private abbrev frame :=
  finiteSmoothTangentFrame period hPeriod

private abbrev deDonderBackground :=
  generalMetricDivergenceBackground period hPeriod

private abbrev GeneratorIndex :=
  FiniteTangentGeneratorIndex period hPeriod

private def generatorIndexEquivFrameIndex :
    GeneratorIndex period hPeriod ≃
      Fin (frame period hPeriod).count :=
  finiteTangentGeneratorIndexEquivFin period hPeriod

/-! ## Exact finite-frame factorization -/

/-- Positive square sum of the finite partition weights. -/
def globalFiniteTangentWeightSquareSum :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    ∑ patch : FiniteTangentGeneratorPatch period hPeriod,
      finiteTangentGeneratorWeight period hPeriod patch point ^ 2
  contMDiff_toFun := by
    apply ContMDiff.sum
    intro patch _
    exact
      (finiteTangentGeneratorWeight_contMDiff
        period hPeriod patch).pow 2

theorem globalFiniteTangentWeightSquareSum_pos
    (point : EffectiveQuotient period hPeriod) :
    0 < globalFiniteTangentWeightSquareSum period hPeriod point := by
  obtain ⟨patch, hPatch⟩ :=
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
  have hWeight :
      0 < finiteTangentGeneratorWeight period hPeriod patch point :=
    lt_of_lt_of_le hInverse hPatch
  change
    0 < ∑ current : FiniteTangentGeneratorPatch period hPeriod,
      finiteTangentGeneratorWeight period hPeriod current point ^ 2
  exact lt_of_lt_of_le (sq_pos_of_pos hWeight)
    (Finset.single_le_sum
      (fun current _ => sq_nonneg
        (finiteTangentGeneratorWeight period hPeriod current point))
      (Finset.mem_univ patch))

/-- Existing relative volume ratio divided by the positive frame-weight
square sum. -/
def globalGeneralMetricDeDonderPairingNormalization
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    globalMetricVolumeRatio period hPeriod metric point /
      globalFiniteTangentWeightSquareSum period hPeriod point
  contMDiff_toFun := by
    exact
      (globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.div₀
        (globalFiniteTangentWeightSquareSum
          period hPeriod).contMDiff_toFun
        (fun point =>
          ne_of_gt
            (globalFiniteTangentWeightSquareSum_pos
              period hPeriod point))

/-- A local-frame coefficient multiplied by its subordinate partition
weight.  The support condition makes this a genuine global smooth scalar. -/
def globalFiniteTangentWeightedLocalCoefficient
    (field : EffectiveD8SmoothVectorField
      (deDonderBackground period hPeriod))
    (index : GeneratorIndex period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    finiteTangentGeneratorWeight period hPeriod index.1 point *
      finiteTangentGeneratorLocalCoefficient
        period hPeriod index.1 index.2 point (field point)
  contMDiff_toFun := by
    apply contMDiff_of_tsupport
    intro point hPoint
    have hWeightSupport :
        point ∈ tsupport
          (finiteTangentGeneratorWeight period hPeriod index.1) :=
      tsupport_mul_subset_left hPoint
    have hPatch :
        point ∈
          finiteTangentGeneratorOpenPatch
            period hPeriod index.1 :=
      finiteTangentGeneratorClosedPatch_subset_openPatch
        period hPeriod index.1 hWeightSupport
    have hCoefficientTotal :=
      finiteTangentGeneratorLocalCoefficient_contMDiffAt
        period hPeriod index.1 index.2
        (⟨point, field point⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod))
        hPatch
    have hCoefficient :=
      hCoefficientTotal.comp point field.contMDiff_toFun.contMDiffAt
    exact
      (finiteTangentGeneratorWeight_contMDiff
        period hPeriod index.1).contMDiffAt.mul hCoefficient

@[simp]
theorem globalFiniteTangentWeightedLocalCoefficient_apply
    (field : EffectiveD8SmoothVectorField
      (deDonderBackground period hPeriod))
    (index : GeneratorIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalFiniteTangentWeightedLocalCoefficient
        period hPeriod field index point =
      finiteTangentGeneratorWeight period hPeriod index.1 point *
        finiteTangentGeneratorLocalCoefficient
          period hPeriod index.1 index.2 point (field point) :=
  rfl

/-- The raised global de Donder one-form as a genuine smooth vector field. -/
def globalGeneralMetricRaisedDeDonder
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    EffectiveD8SmoothVectorField
      (deDonderBackground period hPeriod) :=
  effectiveD8SmoothInverseMusical
    (deDonderBackground period hPeriod) metric
    (globalGeneralMetricDeDonderLinearMap
      period hPeriod metric tensor)

/-- Volume-normalized weighted local coefficient of the raised de Donder
field. -/
def globalGeneralMetricRaisedDeDonderCoordinate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (index : Fin (frame period hPeriod).count) :
    SmoothQuotientField period hPeriod Real :=
  smoothScalarFieldMul period hPeriod
    (globalGeneralMetricDeDonderPairingNormalization
      period hPeriod metric)
    (globalFiniteTangentWeightedLocalCoefficient
      period hPeriod
      (globalGeneralMetricRaisedDeDonder
        period hPeriod metric tensor)
      ((generatorIndexEquivFrameIndex
        period hPeriod).symm index))

@[simp]
theorem globalGeneralMetricRaisedDeDonderCoordinate_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (index : Fin (frame period hPeriod).count)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricRaisedDeDonderCoordinate
        period hPeriod metric tensor index point =
      globalGeneralMetricDeDonderPairingNormalization
          period hPeriod metric point *
        (finiteTangentGeneratorWeight period hPeriod
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).1 point *
          finiteTangentGeneratorLocalCoefficient period hPeriod
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).1
            ((generatorIndexEquivFrameIndex
              period hPeriod).symm index).2 point
            (globalGeneralMetricRaisedDeDonder
              period hPeriod metric tensor point)) :=
  rfl

def globalGeneralMetricRaisedDeDonderCoordinateLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (frame period hPeriod).count) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun := fun tensor =>
    globalGeneralMetricRaisedDeDonderCoordinate
      period hPeriod metric tensor index
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change
      globalGeneralMetricRaisedDeDonderCoordinate
          period hPeriod metric (first + second) index point =
        globalGeneralMetricRaisedDeDonderCoordinate
            period hPeriod metric first index point +
          globalGeneralMetricRaisedDeDonderCoordinate
            period hPeriod metric second index point
    rw [globalGeneralMetricRaisedDeDonderCoordinate_apply,
      globalGeneralMetricRaisedDeDonderCoordinate_apply,
      globalGeneralMetricRaisedDeDonderCoordinate_apply]
    change
      _ *
          (_ *
            finiteTangentGeneratorLocalCoefficient period hPeriod _ _ point
              (inverseMetricSharp period hPeriod metric point
                (globalGeneralMetricDeDonder period hPeriod metric
                  (first + second) point))) =
        _ *
            (_ *
              finiteTangentGeneratorLocalCoefficient period hPeriod _ _ point
                (inverseMetricSharp period hPeriod metric point
                  (globalGeneralMetricDeDonder period hPeriod metric
                    first point))) +
          _ *
            (_ *
              finiteTangentGeneratorLocalCoefficient period hPeriod _ _ point
                (inverseMetricSharp period hPeriod metric point
                  (globalGeneralMetricDeDonder period hPeriod metric
                    second point)))
    rw [globalGeneralMetricDeDonder_add]
    unfold finiteTangentGeneratorLocalCoefficient
    simp only [ContMDiffSection.coe_add, Pi.add_apply, map_add]
    ring
  map_smul' scalar tensor := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change
      globalGeneralMetricRaisedDeDonderCoordinate
          period hPeriod metric (scalar • tensor) index point =
        scalar *
          globalGeneralMetricRaisedDeDonderCoordinate
            period hPeriod metric tensor index point
    rw [globalGeneralMetricRaisedDeDonderCoordinate_apply,
      globalGeneralMetricRaisedDeDonderCoordinate_apply]
    change
      _ *
          (_ *
            finiteTangentGeneratorLocalCoefficient period hPeriod _ _ point
              (inverseMetricSharp period hPeriod metric point
                (globalGeneralMetricDeDonder period hPeriod metric
                  (scalar • tensor) point))) =
        scalar *
          (_ *
            (_ *
              finiteTangentGeneratorLocalCoefficient period hPeriod _ _ point
                (inverseMetricSharp period hPeriod metric point
                  (globalGeneralMetricDeDonder period hPeriod metric
                    tensor point))))
    rw [globalGeneralMetricDeDonder_smul]
    unfold finiteTangentGeneratorLocalCoefficient
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply,
      map_smul]
    ring

def globalGeneralMetricRaisedDeDonderFrameL2LinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod where
  toFun := fun tensor =>
    WithLp.toLp 2 fun index =>
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (globalGeneralMetricRaisedDeDonderCoordinate
          period hPeriod metric tensor index)
  map_add' first second := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalGeneralMetricRaisedDeDonderCoordinateLinearMap
          period hPeriod metric index)
    exact component.map_add first second
  map_smul' scalar tensor := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalGeneralMetricRaisedDeDonderCoordinateLinearMap
          period hPeriod metric index)
    exact component.map_smul scalar tensor

private theorem finiteTangentWeight_eq_zero_of_not_mem
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hPoint :
      point ∉ finiteTangentGeneratorOpenPatch
        period hPeriod patch) :
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
      period hPeriod point index using 1 <;>
    rfl

/-- The weighted finite local frames reconstruct the pairing of any covector
and tangent vector, with the square-weight sum as the only scalar factor. -/
theorem globalFiniteTangentPairingFactorization
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
  rw [← (generatorIndexEquivFrameIndex
    period hPeriod).sum_comp]
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
          (finiteTangentGeneratorWeight
              period hPeriod patch point *
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
      _ = finiteTangentGeneratorWeight
            period hPeriod patch point ^ 2 * covector vector := by
        rw [← hApplied]
  · have hWeight :=
      finiteTangentWeight_eq_zero_of_not_mem
        period hPeriod patch point hPoint
    simp [hWeight]

/-- Pointwise exact factorization of the unchanged Lorentzian de Donder
pairing through the two scalar feature families. -/
theorem globalGeneralMetricDeDonderPairing_factorization
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∑ index : Fin (frame period hPeriod).count,
      globalGeneralMetricDeDonder period hPeriod metric first point
          ((frame period hPeriod).vectorAt point index) *
        globalGeneralMetricRaisedDeDonderCoordinate
          period hPeriod metric second index point) =
      globalMetricVolumeRatio period hPeriod metric point *
        inverseMetricContraction period hPeriod metric point
          (globalGeneralMetricDeDonder
            period hPeriod metric first point)
          (globalGeneralMetricDeDonder
            period hPeriod metric second point) := by
  let covector :=
    globalGeneralMetricDeDonder period hPeriod metric first point
  let raised :=
    globalGeneralMetricRaisedDeDonder
      period hPeriod metric second point
  have hFactor :=
    globalFiniteTangentPairingFactorization
      period hPeriod point covector raised
  have hWeightNonzero :
      globalFiniteTangentWeightSquareSum period hPeriod point ≠ 0 :=
    ne_of_gt
      (globalFiniteTangentWeightSquareSum_pos
        period hPeriod point)
  calc
    (∑ index : Fin (frame period hPeriod).count,
      globalGeneralMetricDeDonder period hPeriod metric first point
          ((frame period hPeriod).vectorAt point index) *
        globalGeneralMetricRaisedDeDonderCoordinate
          period hPeriod metric second index point) =
        globalGeneralMetricDeDonderPairingNormalization
            period hPeriod metric point *
          (∑ index : Fin (frame period hPeriod).count,
            covector ((frame period hPeriod).vectorAt point index) *
              (finiteTangentGeneratorWeight period hPeriod
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).1 point *
                finiteTangentGeneratorLocalCoefficient period hPeriod
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).1
                  ((generatorIndexEquivFrameIndex
                    period hPeriod).symm index).2 point raised)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      rw [globalGeneralMetricRaisedDeDonderCoordinate_apply]
      dsimp only [covector, raised]
      ring
    _ = globalGeneralMetricDeDonderPairingNormalization
          period hPeriod metric point *
        (globalFiniteTangentWeightSquareSum period hPeriod point *
          covector raised) := by
      rw [hFactor]
    _ = globalMetricVolumeRatio period hPeriod metric point *
        covector raised := by
      change
        (globalMetricVolumeRatio period hPeriod metric point /
            globalFiniteTangentWeightSquareSum period hPeriod point) *
            (globalFiniteTangentWeightSquareSum period hPeriod point *
              covector raised) =
          globalMetricVolumeRatio period hPeriod metric point *
            covector raised
      rw [← mul_assoc,
        div_mul_cancel₀ _ hWeightNonzero]
    _ = globalMetricVolumeRatio period hPeriod metric point *
        inverseMetricContraction period hPeriod metric point
          (globalGeneralMetricDeDonder
            period hPeriod metric first point)
          (globalGeneralMetricDeDonder
            period hPeriod metric second point) := by
      rfl

/-! ## Integrated feature identity -/

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

private theorem deDonderFeatureProduct_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      SmoothSymmetricCovariantTwoTensor period hPeriod)
    (index : Fin (frame period hPeriod).count) :
    Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        globalSmoothCovectorFrameCoefficient period hPeriod
            (globalGeneralMetricDeDonderLinearMap
              period hPeriod metric first) index point *
          globalGeneralMetricRaisedDeDonderCoordinate
            period hPeriod metric second index point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact
    ((globalSmoothCovectorFrameCoefficient period hPeriod
        (globalGeneralMetricDeDonderLinearMap
          period hPeriod metric first) index).contMDiff_toFun.continuous.mul
      (globalGeneralMetricRaisedDeDonderCoordinate
        period hPeriod metric second index).contMDiff_toFun.continuous
    ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The cross inner product of the two graph features is exactly the
integrated physical inverse-metric de Donder pairing. -/
theorem globalGeneralMetricDeDonderFeatures_inner_eq_gaugePairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real
        (globalGeneralMetricDeDonderFrameL2LinearMap
          period hPeriod metric first)
        (globalGeneralMetricRaisedDeDonderFrameL2LinearMap
          period hPeriod metric second) =
      globalGeneralMetricDeDonderGaugePairingValue
        period hPeriod metric first second := by
  unfold globalGeneralMetricDeDonderGaugePairingValue
  rw [integral_generalLorentzVolumeMeasure_eq_reference]
  simp only [PiLp.inner_apply]
  change
    (∑ index : Fin (frame period hPeriod).count,
      inner Real
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (globalSmoothCovectorFrameCoefficient period hPeriod
            (globalGeneralMetricDeDonderLinearMap
              period hPeriod metric first) index))
        (smoothToCanonicalPhysicalBulkL2 period hPeriod
          (globalGeneralMetricRaisedDeDonderCoordinate
            period hPeriod metric second index))) =
      ∫ point,
        globalMetricVolumeRatio period hPeriod metric point *
          globalGeneralMetricDeDonderPairingField
            period hPeriod metric first second point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  simp_rw [smoothCanonicalPhysicalBulkL2_inner]
  rw [← integral_finsetSum Finset.univ
    (fun index _ =>
      deDonderFeatureProduct_integrable
        period hPeriod metric first second index)]
  apply integral_congr_ae
  filter_upwards [] with point
  change
    (∑ index : Fin (frame period hPeriod).count,
      globalGeneralMetricDeDonder period hPeriod metric first point
          ((frame period hPeriod).vectorAt point index) *
        globalGeneralMetricRaisedDeDonderCoordinate
          period hPeriod metric second index point) =
      globalMetricVolumeRatio period hPeriod metric point *
        globalGeneralMetricDeDonderPairingField
          period hPeriod metric first second point
  rw [globalGeneralMetricDeDonderPairingField_apply]
  exact globalGeneralMetricDeDonderPairing_factorization
    period hPeriod metric first second point

/-! ## Refined closed Hilbert graph -/

abbrev GlobalGeneralMetricDeDonderPairingGraphAmbient
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  WithLp 2
    (GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric ×
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod)

local instance baseGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance baseGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace.toModule

local instance baseGraphCompleteSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  globalGeneralMetricDeDonderGraphCompleteSpace
    period hPeriod metric

local instance pairingGraphAmbientNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric)).toNormedSpace

local instance pairingGraphAmbientModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric)).toNormedSpace.toModule

def globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric where
  toFun := fun tensor =>
    WithLp.toLp 2
      (globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric tensor,
        globalGeneralMetricRaisedDeDonderFrameL2LinearMap
          period hPeriod metric tensor)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    change
      (globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric (first + second),
        globalGeneralMetricRaisedDeDonderFrameL2LinearMap
          period hPeriod metric (first + second)) = _
    rw [(globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric).map_add,
      (globalGeneralMetricRaisedDeDonderFrameL2LinearMap
        period hPeriod metric).map_add]
    rfl
  map_smul' scalar tensor := by
    apply WithLp.ofLp_injective 2
    change
      (globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric (scalar • tensor),
        globalGeneralMetricRaisedDeDonderFrameL2LinearMap
          period hPeriod metric (scalar • tensor)) = _
    rw [(globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric).map_smul,
      (globalGeneralMetricRaisedDeDonderFrameL2LinearMap
        period hPeriod metric).map_smul]
    rfl

def globalGeneralMetricDeDonderPairingGraphSubmodule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (LinearMap.range
    (globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
      period hPeriod metric)).topologicalClosure

abbrev GlobalGeneralMetricDeDonderPairingGraphHilbert
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalGeneralMetricDeDonderPairingGraphSubmodule
    period hPeriod metric

local instance pairingGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  Submodule.module
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric)

local instance pairingGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  Submodule.normedSpace
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric)

def globalGeneralMetricDeDonderPairingSmoothEmbedding
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric where
  toFun tensor :=
    ⟨globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
        period hPeriod metric tensor,
      (LinearMap.range
        (globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
          period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
            period hPeriod metric) tensor)⟩
  map_add' first second := Subtype.ext
    ((globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
      period hPeriod metric).map_add first second)
  map_smul' scalar tensor := Subtype.ext
    ((globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
      period hPeriod metric).map_smul scalar tensor)

theorem globalGeneralMetricDeDonderPairingSmoothEmbedding_denseRange
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  unfold GlobalGeneralMetricDeDonderPairingGraphHilbert
    globalGeneralMetricDeDonderPairingGraphSubmodule
  let graph :=
    globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
      period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalGeneralMetricDeDonderPairingSmoothEmbedding
            period hPeriod metric) =
        (LinearMap.range graph :
          Set (GlobalGeneralMetricDeDonderPairingGraphAmbient
            period hPeriod metric)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨tensor, rfl⟩, rfl⟩
      exact ⟨tensor, rfl⟩
    · rintro ⟨tensor, rfl⟩
      exact
        ⟨globalGeneralMetricDeDonderPairingSmoothEmbedding
            period hPeriod metric tensor,
          ⟨tensor, rfl⟩, rfl⟩
  change closure
      (LinearMap.range graph :
        Set (GlobalGeneralMetricDeDonderPairingGraphAmbient
          period hPeriod metric)) ⊆
    closure (Subtype.val '' Set.range
      (globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod metric))
  rw [hRange]

theorem globalGeneralMetricDeDonderPairingSmoothEmbedding_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod metric) := by
  intro first second hEqual
  have hAmbient := congrArg Subtype.val hEqual
  have hBase :
      globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric first =
        globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric second :=
    congrArg WithLp.fst hAmbient
  exact globalGeneralMetricDeDonderSmoothEmbedding_injective
    period hPeriod metric hBase

@[implicit_reducible]
def globalGeneralMetricDeDonderPairingGraphCompleteSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) := by
  unfold GlobalGeneralMetricDeDonderPairingGraphHilbert
    globalGeneralMetricDeDonderPairingGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalGeneralMetricDeDonderPairingGraphAmbientLinearMap
        period hPeriod metric))

def globalGeneralMetricDeDonderPairingBaseProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric :=
  (WithLp.fstL 2 Real
      (GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric)
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod)).comp
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric).subtypeL

def globalGeneralMetricDeDonderPairingFeatureProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalGeneralMetricDeDonderFeatureProjection
    period hPeriod metric).comp
      (globalGeneralMetricDeDonderPairingBaseProjection
        period hPeriod metric)

def globalGeneralMetricRaisedDeDonderPairingFeatureProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric)
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod)).comp
    (globalGeneralMetricDeDonderPairingGraphSubmodule
      period hPeriod metric).subtypeL

@[simp]
theorem globalGeneralMetricDeDonderPairingFeatureProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingFeatureProjection
        period hPeriod metric
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric tensor) =
      globalGeneralMetricDeDonderFrameL2LinearMap
        period hPeriod metric tensor :=
  rfl

@[simp]
theorem globalGeneralMetricRaisedDeDonderPairingFeatureProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricRaisedDeDonderPairingFeatureProjection
        period hPeriod metric
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric tensor) =
      globalGeneralMetricRaisedDeDonderFrameL2LinearMap
        period hPeriod metric tensor :=
  rfl

/-! ## Bounded physical Hessian and quadratic action -/

private def globalGeneralMetricDeDonderPairingCrossForm
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real := by
  letI : Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
    pairingGraphModule period hPeriod metric
  letI : NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
    pairingGraphNormedSpace period hPeriod metric
  exact
    (innerSL Real :
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
          Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' :=
        GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric)
      (F' :=
        GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric)
      (globalGeneralMetricDeDonderPairingFeatureProjection
        period hPeriod metric)
      (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
        period hPeriod metric)

private def globalGeneralMetricDeDonderPairingReverseCrossForm
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real := by
  letI : Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
    pairingGraphModule period hPeriod metric
  letI : NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
    pairingGraphNormedSpace period hPeriod metric
  exact
    (innerSL Real :
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
          Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' :=
        GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric)
      (F' :=
        GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric)
      (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
        period hPeriod metric)
      (globalGeneralMetricDeDonderPairingFeatureProjection
        period hPeriod metric)

/-- Bounded symmetric Hessian extending the actual Lorentzian gauge block. -/
def globalGeneralMetricDeDonderPairingGraphHessian
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (1 / 2 : Real) •
    (globalGeneralMetricDeDonderPairingCrossForm
        period hPeriod metric +
      globalGeneralMetricDeDonderPairingReverseCrossForm
        period hPeriod metric)

@[simp]
theorem globalGeneralMetricDeDonderPairingGraphHessian_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    globalGeneralMetricDeDonderPairingGraphHessian
        period hPeriod metric first second =
      (1 / 2 : Real) *
        (inner Real
            (globalGeneralMetricDeDonderPairingFeatureProjection
              period hPeriod metric first)
            (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
              period hPeriod metric second) +
          inner Real
            (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
              period hPeriod metric first)
            (globalGeneralMetricDeDonderPairingFeatureProjection
              period hPeriod metric second)) :=
  by
    simp [globalGeneralMetricDeDonderPairingGraphHessian,
      globalGeneralMetricDeDonderPairingCrossForm,
      globalGeneralMetricDeDonderPairingReverseCrossForm]
    ring

theorem globalGeneralMetricDeDonderPairingGraphHessian_comm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :
    globalGeneralMetricDeDonderPairingGraphHessian
        period hPeriod metric first second =
      globalGeneralMetricDeDonderPairingGraphHessian
        period hPeriod metric second first := by
  rw [globalGeneralMetricDeDonderPairingGraphHessian_apply,
    globalGeneralMetricDeDonderPairingGraphHessian_apply]
  rw [real_inner_comm
      (globalGeneralMetricDeDonderPairingFeatureProjection
        period hPeriod metric first),
    real_inner_comm
      (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
        period hPeriod metric first)]
  ring

/-- On the dense smooth core the bounded Hessian is exactly the pre-existing
integrated Lorentzian gauge pairing. -/
theorem globalGeneralMetricDeDonderPairingGraphHessian_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingGraphHessian
        period hPeriod metric
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric first)
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod metric second) =
      globalGeneralMetricDeDonderGaugePairingValue
        period hPeriod metric first second := by
  rw [globalGeneralMetricDeDonderPairingGraphHessian_apply]
  simp only [
    globalGeneralMetricDeDonderPairingFeatureProjection_smooth,
    globalGeneralMetricRaisedDeDonderPairingFeatureProjection_smooth]
  rw [globalGeneralMetricDeDonderFeatures_inner_eq_gaugePairing,
    real_inner_comm,
    globalGeneralMetricDeDonderFeatures_inner_eq_gaugePairing]
  have hSymmetry :=
    globalGeneralMetricDeDonderGaugeBilinearForm_symmetric
      period hPeriod metric first second
  change
    globalGeneralMetricDeDonderGaugePairingValue
        period hPeriod metric first second =
      globalGeneralMetricDeDonderGaugePairingValue
        period hPeriod metric second first at hSymmetry
  rw [← hSymmetry]
  ring

end
end P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
end JanusFormal
