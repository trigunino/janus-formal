import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderLinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D

/-!
# Faithful Hilbert graph core for the global de Donder operator

The existing finite smooth tangent spanning family turns a smooth symmetric
metric perturbation and its genuine global de Donder one-form into faithful
scalar `L²` coordinates.  Closing the range of the combined map gives a
Hilbert graph with an injective dense smooth core and a bounded projection
onto the de Donder feature.

This gate only constructs the analytic chart core.  It does not replace the
Lorentzian inverse-metric gauge pairing by the positive coordinate pairing,
and therefore makes no same-action Riesz or Fredholm claim.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

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
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D

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

abbrev GlobalGeneralMetricTensorFrameIndex :=
  Fin (frame period hPeriod).count × Fin (frame period hPeriod).count

abbrev GlobalGeneralMetricDeDonderFrameIndex :=
  Fin (frame period hPeriod).count

abbrev GlobalGeneralMetricTensorFrameL2 :=
  PiLp 2
    (fun _ : GlobalGeneralMetricTensorFrameIndex period hPeriod =>
      CanonicalPhysicalBulkL2 period hPeriod)

abbrev GlobalGeneralMetricDeDonderFrameL2 :=
  PiLp 2
    (fun _ : GlobalGeneralMetricDeDonderFrameIndex period hPeriod =>
      CanonicalPhysicalBulkL2 period hPeriod)

abbrev GlobalGeneralMetricDeDonderGraphAmbient :=
  WithLp 2
    (GlobalGeneralMetricTensorFrameL2 period hPeriod ×
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod)

local instance globalGeneralMetricTensorFrameL2NormedSpace :
    NormedSpace Real
      (GlobalGeneralMetricTensorFrameL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricTensorFrameL2 period hPeriod)).toNormedSpace

local instance globalGeneralMetricTensorFrameL2Module :
    Module Real
      (GlobalGeneralMetricTensorFrameL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricTensorFrameL2 period hPeriod)).toNormedSpace.toModule

local instance globalGeneralMetricDeDonderFrameL2NormedSpace :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod)).toNormedSpace

local instance globalGeneralMetricDeDonderFrameL2Module :
    Module Real
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod)).toNormedSpace.toModule

local instance globalGeneralMetricDeDonderGraphAmbientNormedSpace :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphAmbient period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphAmbient period hPeriod)).toNormedSpace

local instance globalGeneralMetricDeDonderGraphAmbientModule :
    Module Real
      (GlobalGeneralMetricDeDonderGraphAmbient period hPeriod) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphAmbient period hPeriod)
    ).toNormedSpace.toModule

/-! ## Faithful raw tensor coordinates -/

def globalGeneralMetricTensorFrameCoefficientLinearMap
    (firstIndex secondIndex : Fin (frame period hPeriod).count) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun := fun tensor =>
    generalMetricFrameCoefficient period hPeriod
      (frame period hPeriod) tensor firstIndex secondIndex
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl
  map_smul' scalar tensor := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl

def globalGeneralMetricTensorFrameL2LinearMap :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GlobalGeneralMetricTensorFrameL2 period hPeriod where
  toFun := fun tensor =>
    WithLp.toLp 2 fun index =>
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (globalGeneralMetricTensorFrameCoefficientLinearMap
          period hPeriod index.1 index.2 tensor)
  map_add' first second := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalGeneralMetricTensorFrameCoefficientLinearMap
          period hPeriod index.1 index.2)
    exact component.map_add first second
  map_smul' scalar tensor := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        (globalGeneralMetricTensorFrameCoefficientLinearMap
          period hPeriod index.1 index.2)
    exact component.map_smul scalar tensor

theorem globalGeneralMetricTensorFrameL2LinearMap_injective :
    Function.Injective
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod) := by
  intro first second hEqual
  have hReading
      (firstIndex secondIndex : Fin (frame period hPeriod).count)
      (point : EffectiveQuotient period hPeriod) :
      first.tensor point
          ((frame period hPeriod).vectorAt point firstIndex)
          ((frame period hPeriod).vectorAt point secondIndex) =
        second.tensor point
          ((frame period hPeriod).vectorAt point firstIndex)
          ((frame period hPeriod).vectorAt point secondIndex) := by
    have hL2 := congrArg
      (fun value : GlobalGeneralMetricTensorFrameL2 period hPeriod =>
        value (firstIndex, secondIndex)) hEqual
    change
      smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (generalMetricFrameCoefficient period hPeriod
            (frame period hPeriod) first firstIndex secondIndex) =
        smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (generalMetricFrameCoefficient period hPeriod
            (frame period hPeriod) second firstIndex secondIndex)
      at hL2
    have hField :=
      smoothFieldToL2_injective period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) hL2
    exact congrArg
      (fun field : SmoothQuotientField period hPeriod Real => field point)
      hField
  have hEnergy :
      ∀ point,
        generalMetricFrameEnergy period hPeriod (frame period hPeriod)
          (first - second) point = 0 := by
    intro point
    unfold generalMetricFrameEnergy
    apply Finset.sum_eq_zero
    intro firstIndex _
    apply Finset.sum_eq_zero
    intro secondIndex _
    have hZero :
        (first - second).tensor point
            ((frame period hPeriod).vectorAt point firstIndex)
            ((frame period hPeriod).vectorAt point secondIndex) = 0 := by
      change
        first.tensor point
            ((frame period hPeriod).vectorAt point firstIndex)
            ((frame period hPeriod).vectorAt point secondIndex) -
          second.tensor point
            ((frame period hPeriod).vectorAt point firstIndex)
            ((frame period hPeriod).vectorAt point secondIndex) = 0
      exact sub_eq_zero.mpr
        (hReading firstIndex secondIndex point)
    rw [hZero]
    norm_num
  have hDifference :=
    generalMetricFrameEnergy_pointwiseSeparates period hPeriod
      (frame period hPeriod) (first - second) hEnergy
  exact sub_eq_zero.mp hDifference

/-! ## Genuine de Donder feature coordinates -/

def globalSmoothCovectorFrameCoefficient
    (covector :
      EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod))
    (index : Fin (frame period hPeriod).count) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    covector point ((frame period hPeriod).vectorAt point index)
  contMDiff_toFun := by
    have hApplied := covector.contMDiff.clm_bundle_apply
      ((frame period hPeriod).contMDiff_vector index)
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

def globalSmoothCovectorFrameCoefficientLinearMap
    (index : Fin (frame period hPeriod).count) :
    EffectiveD8SmoothCovectorField (deDonderBackground period hPeriod) →ₗ[Real]
      SmoothQuotientField period hPeriod Real where
  toFun := fun covector =>
    globalSmoothCovectorFrameCoefficient period hPeriod covector index
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl
  map_smul' scalar covector := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl

def globalGeneralMetricDeDonderFrameL2LinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod where
  toFun := fun tensor =>
    WithLp.toLp 2 fun index =>
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (globalSmoothCovectorFrameCoefficientLinearMap
          period hPeriod index
          (globalGeneralMetricDeDonderLinearMap
            period hPeriod metric tensor))
  map_add' first second := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        ((globalSmoothCovectorFrameCoefficientLinearMap
          period hPeriod index).comp
            (globalGeneralMetricDeDonderLinearMap
              period hPeriod metric))
    exact component.map_add first second
  map_smul' scalar tensor := by
    apply PiLp.ext
    intro index
    let component :=
      (smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
        ((globalSmoothCovectorFrameCoefficientLinearMap
          period hPeriod index).comp
            (globalGeneralMetricDeDonderLinearMap
              period hPeriod metric))
    exact component.map_smul scalar tensor

/-! ## Closed Hilbert graph -/

def globalGeneralMetricDeDonderGraphAmbientLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GlobalGeneralMetricDeDonderGraphAmbient period hPeriod where
  toFun := fun tensor =>
    WithLp.toLp 2
      (globalGeneralMetricTensorFrameL2LinearMap
          period hPeriod tensor,
        globalGeneralMetricDeDonderFrameL2LinearMap
          period hPeriod metric tensor)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    change
      ((globalGeneralMetricTensorFrameL2LinearMap period hPeriod)
          (first + second),
        (globalGeneralMetricDeDonderFrameL2LinearMap
          period hPeriod metric) (first + second)) = _
    rw [(globalGeneralMetricTensorFrameL2LinearMap
          period hPeriod).map_add,
      (globalGeneralMetricDeDonderFrameL2LinearMap
        period hPeriod metric).map_add]
    rfl
  map_smul' scalar tensor := by
    apply WithLp.ofLp_injective 2
    change
      ((globalGeneralMetricTensorFrameL2LinearMap period hPeriod)
          (scalar • tensor),
        (globalGeneralMetricDeDonderFrameL2LinearMap
          period hPeriod metric) (scalar • tensor)) = _
    rw [(globalGeneralMetricTensorFrameL2LinearMap
          period hPeriod).map_smul,
      (globalGeneralMetricDeDonderFrameL2LinearMap
        period hPeriod metric).map_smul]
    rfl

def globalGeneralMetricDeDonderGraphSubmodule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real
      (GlobalGeneralMetricDeDonderGraphAmbient period hPeriod) :=
  (LinearMap.range
    (globalGeneralMetricDeDonderGraphAmbientLinearMap
      period hPeriod metric)).topologicalClosure

abbrev GlobalGeneralMetricDeDonderGraphHilbert
    (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  globalGeneralMetricDeDonderGraphSubmodule period hPeriod metric

local instance globalGeneralMetricDeDonderGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance globalGeneralMetricDeDonderGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace.toModule

def globalGeneralMetricDeDonderSmoothEmbedding
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric where
  toFun tensor :=
    ⟨globalGeneralMetricDeDonderGraphAmbientLinearMap
        period hPeriod metric tensor,
      (LinearMap.range
        (globalGeneralMetricDeDonderGraphAmbientLinearMap
          period hPeriod metric)).le_topologicalClosure
        (LinearMap.mem_range_self
          (globalGeneralMetricDeDonderGraphAmbientLinearMap
            period hPeriod metric) tensor)⟩
  map_add' first second := Subtype.ext
    ((globalGeneralMetricDeDonderGraphAmbientLinearMap
      period hPeriod metric).map_add first second)
  map_smul' scalar tensor := Subtype.ext
    ((globalGeneralMetricDeDonderGraphAmbientLinearMap
      period hPeriod metric).map_smul scalar tensor)

theorem globalGeneralMetricDeDonderSmoothEmbedding_denseRange
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  unfold GlobalGeneralMetricDeDonderGraphHilbert
    globalGeneralMetricDeDonderGraphSubmodule
  let graph :=
    globalGeneralMetricDeDonderGraphAmbientLinearMap
      period hPeriod metric
  have hRange :
      Subtype.val '' Set.range
          (globalGeneralMetricDeDonderSmoothEmbedding
            period hPeriod metric) =
        (LinearMap.range graph :
          Set (GlobalGeneralMetricDeDonderGraphAmbient
            period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨tensor, rfl⟩, rfl⟩
      exact ⟨tensor, rfl⟩
    · rintro ⟨tensor, rfl⟩
      exact
        ⟨globalGeneralMetricDeDonderSmoothEmbedding
            period hPeriod metric tensor,
          ⟨tensor, rfl⟩, rfl⟩
  change closure
      (LinearMap.range graph :
        Set (GlobalGeneralMetricDeDonderGraphAmbient period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (globalGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric))
  rw [hRange]

theorem globalGeneralMetricDeDonderSmoothEmbedding_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric) := by
  intro first second hEqual
  have hAmbient := congrArg Subtype.val hEqual
  have hTensor :
      globalGeneralMetricTensorFrameL2LinearMap period hPeriod first =
        globalGeneralMetricTensorFrameL2LinearMap
          period hPeriod second :=
    congrArg WithLp.fst hAmbient
  exact globalGeneralMetricTensorFrameL2LinearMap_injective
    period hPeriod hTensor

@[implicit_reducible]
def globalGeneralMetricDeDonderGraphCompleteSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) := by
  unfold GlobalGeneralMetricDeDonderGraphHilbert
    globalGeneralMetricDeDonderGraphSubmodule
  exact Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (globalGeneralMetricDeDonderGraphAmbientLinearMap
        period hPeriod metric))

def globalGeneralMetricDeDonderFeatureProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (WithLp.sndL 2 Real
      (GlobalGeneralMetricTensorFrameL2 period hPeriod)
      (GlobalGeneralMetricDeDonderFrameL2 period hPeriod)).comp
    (globalGeneralMetricDeDonderGraphSubmodule
      period hPeriod metric).subtypeL

@[simp]
theorem globalGeneralMetricDeDonderFeatureProjection_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderFeatureProjection period hPeriod metric
        (globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric tensor) =
      globalGeneralMetricDeDonderFrameL2LinearMap
        period hPeriod metric tensor :=
  rfl

end
end P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
end JanusFormal
