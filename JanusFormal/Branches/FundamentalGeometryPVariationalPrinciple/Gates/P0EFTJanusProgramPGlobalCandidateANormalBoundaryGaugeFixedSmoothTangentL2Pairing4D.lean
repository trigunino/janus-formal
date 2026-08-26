import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalRobinL2Injection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentRange4D

/-!
# L2 pairing on the smooth normal-boundary tangent range

The metric component uses the existing faithful de Donder Hilbert graph.  The
normal component uses its faithful scalar representative on the orientation
double and the canonical throat `L2` inclusion.  Their orthogonal sum gives a
nondegenerate pairing on the genuine smooth core and, by transport, on its
actual gauge-fixed tangent range.

This does not install an inner product on the completed `C3 × C2` Banach core
and makes no same-action or terminal claim.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusMappingTorusCanonicalRobinL2Injection4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentRange4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev OrientationNormalL2 :=
  ThroatScalarL2
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))

local instance orientationCanonicalVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

attribute [local instance]
  intrinsicCanonicalThroatVolumeMeasure_isFinite

/-- The genuine normal section, first scalarized on the orientation double and
then included in its canonical throat `L2`. -/
def candidateANormalBoundaryNormalL2LinearMap :
    SmoothNormalDisplacement period hPeriod →ₗ[Real]
      OrientationNormalL2 period hPeriod where
  toFun displacement :=
    smoothThroatFieldToL2
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      (normalDisplacementOrientationSmoothField
        period hPeriod displacement)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [smoothThroatFieldToL2_ae
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField
          period hPeriod (first + second)),
       smoothThroatFieldToL2_ae
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField period hPeriod first),
       smoothThroatFieldToL2_ae
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField period hPeriod second),
       Lp.coeFn_add
        (smoothThroatFieldToL2
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          (normalDisplacementOrientationSmoothField period hPeriod first))
        (smoothThroatFieldToL2
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          (normalDisplacementOrientationSmoothField period hPeriod second))]
      with boundary hSum hFirst hSecond hAdd
    calc
      _ = normalDisplacementOrientationSmoothField
          period hPeriod (first + second) boundary := hSum
      _ = normalDisplacementOrientationSmoothField
            period hPeriod first boundary +
          normalDisplacementOrientationSmoothField
            period hPeriod second boundary := by
              rw [normalDisplacementOrientationSmoothField_add]
              rfl
      _ = _ := by
        simpa only [Pi.add_apply, hFirst, hSecond] using hAdd.symm
  map_smul' scalar displacement := by
    apply Lp.ext
    filter_upwards
      [smoothThroatFieldToL2_ae
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField
          period hPeriod (scalar • displacement)),
       smoothThroatFieldToL2_ae
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField period hPeriod displacement),
       Lp.coeFn_smul scalar
        (smoothThroatFieldToL2
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          (normalDisplacementOrientationSmoothField
            period hPeriod displacement))]
      with boundary hScaled hField hSmul
    calc
      _ = normalDisplacementOrientationSmoothField
          period hPeriod (scalar • displacement) boundary := hScaled
      _ = scalar • normalDisplacementOrientationSmoothField
          period hPeriod displacement boundary := by
            rw [normalDisplacementOrientationSmoothField_smul]
            rfl
      _ = _ := by
        simpa only [Pi.smul_apply, RingHom.id_apply, hField] using hSmul.symm

theorem candidateANormalBoundaryNormalL2LinearMap_injective :
    Function.Injective
      (candidateANormalBoundaryNormalL2LinearMap period hPeriod) := by
  intro first second hEqual
  apply normalDisplacementOrientationScalar_injective period hPeriod
  change
    smoothThroatFieldToL2
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField period hPeriod first) =
      smoothThroatFieldToL2
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField period hPeriod second)
    at hEqual
  have hSmoothField :
      normalDisplacementOrientationSmoothField period hPeriod first =
        normalDisplacementOrientationSmoothField period hPeriod second :=
    smoothThroatFieldToCanonicalL2_injective
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) hEqual
  funext boundary
  exact congrArg
    (fun field : SmoothThroatField
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real =>
      field boundary) hSmoothField

theorem candidateANormalBoundaryNormalL2LinearMap_inner
    (first second : SmoothNormalDisplacement period hPeriod) :
    inner Real
        (candidateANormalBoundaryNormalL2LinearMap period hPeriod first)
        (candidateANormalBoundaryNormalL2LinearMap period hPeriod second) =
      ∫ boundary,
        normalDisplacementOrientationScalar period hPeriod first boundary *
          normalDisplacementOrientationScalar period hPeriod second boundary
        ∂(intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) := by
  change inner Real
      (smoothThroatFieldToL2
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField period hPeriod first))
      (smoothThroatFieldToL2
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (normalDisplacementOrientationSmoothField period hPeriod second)) = _
  rw [smoothThroatFieldToL2_inner]
  rfl

/-- Orthogonal Hilbert target for the two genuine smooth boundary directions. -/
abbrev CandidateANormalBoundarySmoothL2Hilbert
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  WithLp 2
    (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric.metric ×
      OrientationNormalL2 period hPeriod)

/-- Faithful joint `L2` realization of the smooth metric/normal pair. -/
def candidateANormalBoundarySmoothL2Embedding
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      CandidateANormalBoundarySmoothL2Hilbert period hPeriod metric where
  toFun variation :=
    WithLp.toLp 2
      (globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric.metric variation.1,
        candidateANormalBoundaryNormalL2LinearMap
          period hPeriod variation.2)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    change
      (globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric.metric (first.1 + second.1),
        candidateANormalBoundaryNormalL2LinearMap
          period hPeriod (first.2 + second.2)) = _
    rw [(globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric.metric).map_add,
      (candidateANormalBoundaryNormalL2LinearMap
        period hPeriod).map_add]
    rfl
  map_smul' scalar variation := by
    apply WithLp.ofLp_injective 2
    change
      (globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric.metric (scalar • variation.1),
        candidateANormalBoundaryNormalL2LinearMap
          period hPeriod (scalar • variation.2)) = _
    rw [(globalGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric.metric).map_smul,
      (candidateANormalBoundaryNormalL2LinearMap
        period hPeriod).map_smul]
    rfl

theorem candidateANormalBoundarySmoothL2Embedding_injective
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (candidateANormalBoundarySmoothL2Embedding
        period hPeriod metric) := by
  intro first second hEqual
  apply Prod.ext
  · apply globalGeneralMetricDeDonderSmoothEmbedding_injective
      period hPeriod metric.metric
    exact congrArg WithLp.fst hEqual
  · apply candidateANormalBoundaryNormalL2LinearMap_injective
      period hPeriod
    exact congrArg WithLp.snd hEqual

/-- Positive symmetric bilinear pairing pulled back from the genuine joint
Hilbert target.  It is deliberately not an instance on the Banach core. -/
def candidateANormalBoundarySmoothL2Pairing
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun first second =>
      inner Real
        (candidateANormalBoundarySmoothL2Embedding
          period hPeriod metric first)
        (candidateANormalBoundarySmoothL2Embedding
          period hPeriod metric second))
    (by
      intro first second third
      rw [(candidateANormalBoundarySmoothL2Embedding
        period hPeriod metric).map_add]
      exact inner_add_left _ _ _)
    (by
      intro scalar first second
      rw [(candidateANormalBoundarySmoothL2Embedding
        period hPeriod metric).map_smul]
      exact inner_smul_left_eq_smul _ _ scalar)
    (by
      intro first second third
      rw [(candidateANormalBoundarySmoothL2Embedding
        period hPeriod metric).map_add]
      exact inner_add_right _ _ _)
    (by
      intro scalar first second
      rw [(candidateANormalBoundarySmoothL2Embedding
        period hPeriod metric).map_smul]
      exact inner_smul_right_eq_smul _ _ scalar)

@[simp]
theorem candidateANormalBoundarySmoothL2Pairing_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundarySmoothL2Pairing
        period hPeriod metric first second =
      inner Real
        (candidateANormalBoundarySmoothL2Embedding
          period hPeriod metric first)
        (candidateANormalBoundarySmoothL2Embedding
          period hPeriod metric second) := by
  rfl

theorem candidateANormalBoundarySmoothL2Pairing_eq_components
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundarySmoothL2Pairing
        period hPeriod metric first second =
      inner Real
          (globalGeneralMetricDeDonderSmoothEmbedding
            period hPeriod metric.metric first.1)
          (globalGeneralMetricDeDonderSmoothEmbedding
            period hPeriod metric.metric second.1) +
        ∫ boundary,
          normalDisplacementOrientationScalar period hPeriod first.2 boundary *
            normalDisplacementOrientationScalar
              period hPeriod second.2 boundary
          ∂(intrinsicCanonicalThroatVolumeMeasure
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) := by
  rw [candidateANormalBoundarySmoothL2Pairing_apply]
  change inner Real
      (WithLp.toLp 2
        (globalGeneralMetricDeDonderSmoothEmbedding
            period hPeriod metric.metric first.1,
          candidateANormalBoundaryNormalL2LinearMap
            period hPeriod first.2))
      (WithLp.toLp 2
        (globalGeneralMetricDeDonderSmoothEmbedding
            period hPeriod metric.metric second.1,
          candidateANormalBoundaryNormalL2LinearMap
            period hPeriod second.2)) = _
  rw [WithLp.prod_inner_apply,
    candidateANormalBoundaryNormalL2LinearMap_inner]

theorem candidateANormalBoundarySmoothL2Pairing_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundarySmoothL2Pairing
        period hPeriod metric first second =
      candidateANormalBoundarySmoothL2Pairing
        period hPeriod metric second first := by
  rw [candidateANormalBoundarySmoothL2Pairing_apply,
    candidateANormalBoundarySmoothL2Pairing_apply]
  exact real_inner_comm _ _

theorem candidateANormalBoundarySmoothL2Pairing_self_eq_zero_iff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundarySmoothL2Pairing
        period hPeriod metric variation variation = 0 ↔
      variation = 0 := by
  rw [candidateANormalBoundarySmoothL2Pairing_apply]
  constructor
  · intro hZero
    have hImage :
        candidateANormalBoundarySmoothL2Embedding
            period hPeriod metric variation = 0 :=
      inner_self_eq_zero.mp hZero
    apply candidateANormalBoundarySmoothL2Embedding_injective
      period hPeriod metric
    simpa using hImage
  · rintro rfl
    simp

/-- The same bilinear pairing, transported only across the equivalence with
the actual smooth range inside the gauge-fixed tangent. -/
def candidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    CandidateANormalBoundaryGaugeFixedSmoothTangent
        period hPeriod configuration →ₗ[Real]
      CandidateANormalBoundaryGaugeFixedSmoothTangent
        period hPeriod configuration →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun first second =>
      candidateANormalBoundarySmoothL2Pairing period hPeriod metric
        ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration).symm first)
        ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration).symm second))
    (by
      intro first second third
      rw [(candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
        period hPeriod configuration).symm.map_add]
      exact congrArg
        (fun functional :
            CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real] Real =>
          functional
            ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
              period hPeriod configuration).symm third))
        ((candidateANormalBoundarySmoothL2Pairing
          period hPeriod metric).map_add _ _))
    (by
      intro scalar first second
      rw [(candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
        period hPeriod configuration).symm.map_smul]
      exact congrArg
        (fun functional :
            CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real] Real =>
          functional
            ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
              period hPeriod configuration).symm second))
        ((candidateANormalBoundarySmoothL2Pairing
          period hPeriod metric).map_smul scalar _))
    (by
      intro first second third
      rw [(candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
        period hPeriod configuration).symm.map_add]
      exact (candidateANormalBoundarySmoothL2Pairing period hPeriod metric
        ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration).symm first)).map_add _ _)
    (by
      intro scalar first second
      rw [(candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
        period hPeriod configuration).symm.map_smul]
      exact (candidateANormalBoundarySmoothL2Pairing period hPeriod metric
        ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration).symm first)).map_smul scalar _)

@[simp]
theorem candidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (first second : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing
        period hPeriod metric configuration
        (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration first)
        (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration second) =
      candidateANormalBoundarySmoothL2Pairing
        period hPeriod metric first second := by
  simp [candidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing]

theorem candidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing_self_eq_zero_iff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundaryGaugeFixedSmoothTangent
      period hPeriod configuration) :
    candidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing
        period hPeriod metric configuration variation variation = 0 ↔
      variation = 0 := by
  change candidateANormalBoundarySmoothL2Pairing period hPeriod metric
      ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
        period hPeriod configuration).symm variation)
      ((candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
        period hPeriod configuration).symm variation) = 0 ↔ _
  rw [candidateANormalBoundarySmoothL2Pairing_self_eq_zero_iff]
  exact
    (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
      period hPeriod configuration).symm.map_eq_zero_iff

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing4D
end JanusFormal
