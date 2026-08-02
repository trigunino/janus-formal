import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D

/-!
# Candidate-A metric and Abelian gauge graph chart

The two exact de Donder graph actions and the paired Lorenz graph action are
assembled on one Hilbert product.  The resulting quadratic action is smooth
and has the direct-sum same-action Hessian.  Its smooth core also maps
linearly into the corrected typed gauge-fixed tangent, with the nonminimal
directions held at zero.

This is the physical gauge subchart only.  It does not claim analytic
completions for the typed nonminimal, matter, LL, normal or boundary sectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderGaugePairing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairingC2Chart4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphC2Chart4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

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

local instance baseGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance pairingGraphAmbientNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphAmbient
        period hPeriod metric)).toNormedSpace

local instance pairingGraphNormedSpace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance (priority := 10000) pairingGraphModule
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod metric) :=
  (pairingGraphNormedSpace period hPeriod metric).toModule

local instance lorenzGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert
        period hPeriod metric) :=
  (inferInstance :
    InnerProductSpace Real
      (GlobalPairedAbelianLorenzGraphHilbert
        period hPeriod metric)).toNormedSpace

local instance (priority := 10000) lorenzGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianLorenzGraphHilbert
        period hPeriod metric) :=
  (lorenzGraphNormedSpace period hPeriod metric).toModule

/-! ## The paired metric gauge chart -/

/-- Product of the exact de Donder pairing graphs for the two Candidate-A
metric sectors. -/
abbrev GlobalPairedGeneralMetricDeDonderGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  GlobalGeneralMetricDeDonderPairingGraphHilbert
      period hPeriod (metric .plus) ×
    GlobalGeneralMetricDeDonderPairingGraphHilbert
      period hPeriod (metric .minus)

local instance pairedMetricGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  Prod.normedSpace

local instance (priority := 10000) pairedMetricGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :=
  (Prod.normedSpace :
    NormedSpace Real
      (GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)).toModule

def globalPairedGeneralMetricDeDonderPlusProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod (metric .plus) :=
  { toFun := Prod.fst
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst }

def globalPairedGeneralMetricDeDonderMinusProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderPairingGraphHilbert
        period hPeriod (metric .minus) :=
  { toFun := Prod.snd
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_snd }

/-- Dense smooth-core insertion for the two metric sectors. -/
def globalPairedGeneralMetricDeDonderSmoothEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric where
  toFun tensor :=
    (globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod (metric .plus) (tensor .plus),
      globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod (metric .minus) (tensor .minus))
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod (metric .plus)).map_add
          (first .plus) (second .plus)
    · exact
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod (metric .minus)).map_add
          (first .minus) (second .minus)
  map_smul' scalar tensor := by
    apply Prod.ext
    · exact
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod (metric .plus)).map_smul
          scalar (tensor .plus)
    · exact
        (globalGeneralMetricDeDonderPairingSmoothEmbedding
          period hPeriod (metric .minus)).map_smul
          scalar (tensor .minus)

@[simp]
theorem globalPairedGeneralMetricDeDonderSmoothEmbedding_fst
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (tensor : GlobalMetricPerturbationPair period hPeriod) :
    (globalPairedGeneralMetricDeDonderSmoothEmbedding
      period hPeriod metric tensor).1 =
      globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod (metric .plus) (tensor .plus) :=
  rfl

@[simp]
theorem globalPairedGeneralMetricDeDonderSmoothEmbedding_snd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (tensor : GlobalMetricPerturbationPair period hPeriod) :
    (globalPairedGeneralMetricDeDonderSmoothEmbedding
      period hPeriod metric tensor).2 =
      globalGeneralMetricDeDonderPairingSmoothEmbedding
        period hPeriod (metric .minus) (tensor .minus) :=
  rfl

theorem globalPairedGeneralMetricDeDonderSmoothEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalPairedGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric) := by
  intro first second hEqual
  funext sector
  cases sector with
  | plus =>
      apply globalGeneralMetricDeDonderPairingSmoothEmbedding_injective
        period hPeriod (metric .plus)
      exact congrArg Prod.fst hEqual
  | minus =>
      apply globalGeneralMetricDeDonderPairingSmoothEmbedding_injective
        period hPeriod (metric .minus)
      exact congrArg Prod.snd hEqual

theorem globalPairedGeneralMetricDeDonderSmoothEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalPairedGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric) := by
  have hProduct :
      DenseRange
        (Prod.map
          (globalGeneralMetricDeDonderPairingSmoothEmbedding
            period hPeriod (metric .plus))
          (globalGeneralMetricDeDonderPairingSmoothEmbedding
            period hPeriod (metric .minus))) :=
    (globalGeneralMetricDeDonderPairingSmoothEmbedding_denseRange
      period hPeriod (metric .plus)).prodMap
      (globalGeneralMetricDeDonderPairingSmoothEmbedding_denseRange
        period hPeriod (metric .minus))
  apply Dense.mono _ hProduct
  rintro _ ⟨⟨plus, minus⟩, rfl⟩
  refine ⟨fun
    | .plus => plus
    | .minus => minus, ?_⟩
  rfl

private def globalPairedGeneralMetricDeDonderPlusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalGeneralMetricDeDonderPairingFeatureProjection
    period hPeriod (metric .plus)).comp
      (globalPairedGeneralMetricDeDonderPlusProjection
        period hPeriod metric)

private def globalPairedGeneralMetricRaisedDeDonderPlusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
    period hPeriod (metric .plus)).comp
      (globalPairedGeneralMetricDeDonderPlusProjection
        period hPeriod metric)

private def globalPairedGeneralMetricDeDonderMinusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalGeneralMetricDeDonderPairingFeatureProjection
    period hPeriod (metric .minus)).comp
      (globalPairedGeneralMetricDeDonderMinusProjection
        period hPeriod metric)

private def globalPairedGeneralMetricRaisedDeDonderMinusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
    period hPeriod (metric .minus)).comp
      (globalPairedGeneralMetricDeDonderMinusProjection
        period hPeriod metric)

private def globalPairedGeneralMetricDeDonderPlusCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (F' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (globalPairedGeneralMetricDeDonderPlusFeature
        period hPeriod metric)
      (globalPairedGeneralMetricRaisedDeDonderPlusFeature
        period hPeriod metric)

private def globalPairedGeneralMetricDeDonderMinusCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (F' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (globalPairedGeneralMetricDeDonderMinusFeature
        period hPeriod metric)
      (globalPairedGeneralMetricRaisedDeDonderMinusFeature
        period hPeriod metric)

private def globalPairedGeneralMetricDeDonderPlusReverseCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (F' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (globalPairedGeneralMetricRaisedDeDonderPlusFeature
        period hPeriod metric)
      (globalPairedGeneralMetricDeDonderPlusFeature
        period hPeriod metric)

private def globalPairedGeneralMetricDeDonderMinusReverseCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (F' := GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric)
      (globalPairedGeneralMetricRaisedDeDonderMinusFeature
        period hPeriod metric)
      (globalPairedGeneralMetricDeDonderMinusFeature
        period hPeriod metric)

private def globalPairedGeneralMetricDeDonderCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
          period hPeriod metric →L[Real] Real :=
  globalPairedGeneralMetricDeDonderPlusCrossForm
      period hPeriod metric +
    globalPairedGeneralMetricDeDonderMinusCrossForm
      period hPeriod metric

private def globalPairedGeneralMetricDeDonderReverseCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
          period hPeriod metric →L[Real] Real :=
  globalPairedGeneralMetricDeDonderPlusReverseCrossForm
      period hPeriod metric +
    globalPairedGeneralMetricDeDonderMinusReverseCrossForm
      period hPeriod metric

/-- Direct sum of the two exact Lorentzian de Donder Hessians. -/
def globalPairedGeneralMetricDeDonderGraphHessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (1 / 2 : Real) •
    (globalPairedGeneralMetricDeDonderCrossForm
        period hPeriod metric +
      globalPairedGeneralMetricDeDonderReverseCrossForm
        period hPeriod metric)

@[simp]
theorem globalPairedGeneralMetricDeDonderGraphHessian_apply
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :
    globalPairedGeneralMetricDeDonderGraphHessian
        period hPeriod metric first second =
      globalGeneralMetricDeDonderPairingC2Hessian
          period hPeriod (metric .plus) first.1 second.1 +
      globalGeneralMetricDeDonderPairingC2Hessian
          period hPeriod (metric .minus) first.2 second.2 := by
  rw [globalGeneralMetricDeDonderPairingC2Hessian_apply,
    globalGeneralMetricDeDonderPairingC2Hessian_apply]
  change
    (1 / 2 : Real) *
        ((inner Real
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) first.1)
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) second.1) +
            inner Real
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) first.2)
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) second.2)) +
          (inner Real
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) first.1)
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) second.1) +
            inner Real
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) first.2)
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) second.2))) =
      (1 / 2 : Real) *
          (inner Real
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) first.1)
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) second.1) +
            inner Real
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) first.1)
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .plus) second.1)) +
        (1 / 2 : Real) *
          (inner Real
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) first.2)
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) second.2) +
            inner Real
              (globalGeneralMetricRaisedDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) first.2)
              (globalGeneralMetricDeDonderPairingFeatureProjection
                period hPeriod (metric .minus) second.2))
  ring

theorem globalPairedGeneralMetricDeDonderGraphHessian_comm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric) :
    globalPairedGeneralMetricDeDonderGraphHessian
        period hPeriod metric first second =
      globalPairedGeneralMetricDeDonderGraphHessian
        period hPeriod metric second first := by
  rw [globalPairedGeneralMetricDeDonderGraphHessian_apply,
    globalPairedGeneralMetricDeDonderGraphHessian_apply]
  rw [globalGeneralMetricDeDonderPairingC2Hessian_comm
      period hPeriod (metric .plus) first.1 second.1,
    globalGeneralMetricDeDonderPairingC2Hessian_comm
      period hPeriod (metric .minus) first.2 second.2]

theorem globalPairedGeneralMetricDeDonderGraphHessian_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalMetricPerturbationPair period hPeriod) :
    globalPairedGeneralMetricDeDonderGraphHessian period hPeriod metric
        (globalPairedGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric first)
        (globalPairedGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric second) =
      globalGeneralMetricDeDonderGaugePairingValue
          period hPeriod (metric .plus) (first .plus) (second .plus) +
        globalGeneralMetricDeDonderGaugePairingValue
          period hPeriod (metric .minus) (first .minus) (second .minus) := by
  rw [globalPairedGeneralMetricDeDonderGraphHessian_apply]
  simp only [
    globalPairedGeneralMetricDeDonderSmoothEmbedding_fst,
    globalPairedGeneralMetricDeDonderSmoothEmbedding_snd]
  rw [globalGeneralMetricDeDonderPairingC2Hessian_smooth,
    globalGeneralMetricDeDonderPairingC2Hessian_smooth]

/-! ## Product with the already closed Lorenz chart -/

/-- Physical metric-plus-Abelian gauge chart. -/
abbrev GlobalCandidateAGaugeGraphHilbert
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :=
  GlobalPairedGeneralMetricDeDonderGraphHilbert
      period hPeriod metric ×
    GlobalPairedAbelianLorenzGraphHilbert
      period hPeriod metric

local instance candidateGaugeGraphNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :=
  Prod.normedSpace

local instance (priority := 10000) candidateGaugeGraphModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :=
  (Prod.normedSpace :
    NormedSpace Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)).toModule

local instance candidateGaugeGraphDualNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup
    Real Real
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (candidateGaugeGraphNormedSpace period hPeriod metric)
    inferInstance
    (RingHom.id Real) inferInstance

local instance candidateGaugeGraphDualNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedSpace
    Real Real
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
    Real
    inferInstance inferInstance inferInstance inferInstance
    (candidateGaugeGraphNormedSpace period hPeriod metric)
    inferInstance
    (RingHom.id Real) inferInstance
    Real inferInstance inferInstance inferInstance

/-- Smooth intrinsic core of the physical gauge chart. -/
abbrev GlobalCandidateAGaugeSmoothCore :=
  GlobalMetricPerturbationPair period hPeriod ×
    GlobalPairedAbelianPotentialSmooth period hPeriod

def globalCandidateAGaugeMetricProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedGeneralMetricDeDonderGraphHilbert
        period hPeriod metric :=
  { toFun := Prod.fst
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_fst }

def globalCandidateAGaugeLorenzProjection
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert period hPeriod metric →L[Real]
      GlobalPairedAbelianLorenzGraphHilbert
        period hPeriod metric :=
  { toFun := Prod.snd
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    cont := continuous_snd }

/-- Common smooth-core insertion into the metric and Lorenz product chart. -/
def globalCandidateAGaugeSmoothEmbedding
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeSmoothCore period hPeriod →ₗ[Real]
      GlobalCandidateAGaugeGraphHilbert period hPeriod metric where
  toFun core :=
    (globalPairedGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric core.1,
      globalPairedAbelianLorenzSmoothEmbedding
        period hPeriod metric core.2)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalPairedGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric).map_add first.1 second.1
    · exact
        (globalPairedAbelianLorenzSmoothEmbedding
          period hPeriod metric).map_add first.2 second.2
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (globalPairedGeneralMetricDeDonderSmoothEmbedding
          period hPeriod metric).map_smul scalar core.1
    · exact
        (globalPairedAbelianLorenzSmoothEmbedding
          period hPeriod metric).map_smul scalar core.2

@[simp]
theorem globalCandidateAGaugeSmoothEmbedding_fst
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (core : GlobalCandidateAGaugeSmoothCore period hPeriod) :
    (globalCandidateAGaugeSmoothEmbedding
      period hPeriod metric core).1 =
      globalPairedGeneralMetricDeDonderSmoothEmbedding
        period hPeriod metric core.1 :=
  rfl

@[simp]
theorem globalCandidateAGaugeSmoothEmbedding_snd
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (core : GlobalCandidateAGaugeSmoothCore period hPeriod) :
    (globalCandidateAGaugeSmoothEmbedding
      period hPeriod metric core).2 =
      globalPairedAbelianLorenzSmoothEmbedding
        period hPeriod metric core.2 :=
  rfl

theorem globalCandidateAGaugeSmoothEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalCandidateAGaugeSmoothEmbedding
        period hPeriod metric) := by
  intro first second hEqual
  apply Prod.ext
  · apply globalPairedGeneralMetricDeDonderSmoothEmbedding_injective
      period hPeriod metric
    exact congrArg (fun value => value.1) hEqual
  · apply globalPairedAbelianLorenzSmoothEmbedding_injective
      period hPeriod metric
    exact congrArg (fun value => value.2) hEqual

theorem globalCandidateAGaugeSmoothEmbedding_denseRange
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange
      (globalCandidateAGaugeSmoothEmbedding
        period hPeriod metric) := by
  have hProduct :=
    (globalPairedGeneralMetricDeDonderSmoothEmbedding_denseRange
      period hPeriod metric).prodMap
      (globalPairedAbelianLorenzSmoothEmbedding_denseRange
        period hPeriod metric)
  apply Dense.mono _ hProduct
  rintro _ ⟨⟨metricCore, lorenzCore⟩, rfl⟩
  exact ⟨(metricCore, lorenzCore), rfl⟩

private def globalCandidateAGaugeDeDonderPlusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalPairedGeneralMetricDeDonderPlusFeature
    period hPeriod metric).comp
      (globalCandidateAGaugeMetricProjection
        period hPeriod metric)

private def globalCandidateAGaugeRaisedDeDonderPlusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalPairedGeneralMetricRaisedDeDonderPlusFeature
    period hPeriod metric).comp
      (globalCandidateAGaugeMetricProjection
        period hPeriod metric)

private def globalCandidateAGaugeDeDonderMinusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalPairedGeneralMetricDeDonderMinusFeature
    period hPeriod metric).comp
      (globalCandidateAGaugeMetricProjection
        period hPeriod metric)

private def globalCandidateAGaugeRaisedDeDonderMinusFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod :=
  (globalPairedGeneralMetricRaisedDeDonderMinusFeature
    period hPeriod metric).comp
      (globalCandidateAGaugeMetricProjection
        period hPeriod metric)

private def globalCandidateAGaugeLorenzFeature
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalPairedAbelianLorenzL2 period hPeriod :=
  (globalPairedAbelianLorenzFeatureProjection
    period hPeriod metric).comp
      (globalCandidateAGaugeLorenzProjection
        period hPeriod metric)

private def globalCandidateAGaugeMetricPlusCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (F' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (globalCandidateAGaugeDeDonderPlusFeature
        period hPeriod metric)
      (globalCandidateAGaugeRaisedDeDonderPlusFeature
        period hPeriod metric)

private def globalCandidateAGaugeMetricMinusCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (F' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (globalCandidateAGaugeDeDonderMinusFeature
        period hPeriod metric)
      (globalCandidateAGaugeRaisedDeDonderMinusFeature
        period hPeriod metric)

private def globalCandidateAGaugeMetricPlusReverseCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (F' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (globalCandidateAGaugeRaisedDeDonderPlusFeature
        period hPeriod metric)
      (globalCandidateAGaugeDeDonderPlusFeature
        period hPeriod metric)

private def globalCandidateAGaugeMetricMinusReverseCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
      GlobalGeneralMetricDeDonderFrameL2 period hPeriod →L[Real]
        Real).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (F' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (globalCandidateAGaugeRaisedDeDonderMinusFeature
        period hPeriod metric)
      (globalCandidateAGaugeDeDonderMinusFeature
        period hPeriod metric)

private def globalCandidateAGaugeMetricCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  globalCandidateAGaugeMetricPlusCrossForm period hPeriod metric +
    globalCandidateAGaugeMetricMinusCrossForm period hPeriod metric

private def globalCandidateAGaugeMetricReverseCrossForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  globalCandidateAGaugeMetricPlusReverseCrossForm
      period hPeriod metric +
    globalCandidateAGaugeMetricMinusReverseCrossForm
      period hPeriod metric

private def globalCandidateAGaugeLorenzForm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (innerSL Real :
    GlobalPairedAbelianLorenzL2 period hPeriod →L[Real]
      GlobalPairedAbelianLorenzL2 period hPeriod →L[Real] Real
    ).bilinearComp
      (𝕜₁' := Real) (𝕜₂' := Real)
      (E' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (F' := GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (globalCandidateAGaugeLorenzFeature period hPeriod metric)
      (globalCandidateAGaugeLorenzFeature period hPeriod metric)

/-- Direct-sum Hessian of the exact de Donder and Lorenz graph actions. -/
def globalCandidateAGaugeGraphHessian
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real]
      GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real :=
  (1 / 2 : Real) •
      (globalCandidateAGaugeMetricCrossForm
          period hPeriod metric +
        globalCandidateAGaugeMetricReverseCrossForm
          period hPeriod metric) +
    globalCandidateAGaugeLorenzForm period hPeriod metric

@[simp]
theorem globalCandidateAGaugeGraphHessian_apply
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :
    globalCandidateAGaugeGraphHessian
        period hPeriod metric first second =
      globalPairedGeneralMetricDeDonderGraphHessian
          period hPeriod metric first.1 second.1 +
        globalPairedAbelianLorenzGraphHessian
          period hPeriod metric first.2 second.2 := by
  change
    (1 / 2 : Real) *
        (globalPairedGeneralMetricDeDonderCrossForm
            period hPeriod metric first.1 second.1 +
          globalPairedGeneralMetricDeDonderReverseCrossForm
            period hPeriod metric first.1 second.1) +
      inner Real
        (globalPairedAbelianLorenzFeatureProjection
          period hPeriod metric first.2)
        (globalPairedAbelianLorenzFeatureProjection
          period hPeriod metric second.2) =
      globalPairedGeneralMetricDeDonderGraphHessian
          period hPeriod metric first.1 second.1 +
        globalPairedAbelianLorenzGraphHessian
          period hPeriod metric first.2 second.2
  rw [globalPairedAbelianLorenzGraphHessian_apply]
  rfl

theorem globalCandidateAGaugeGraphHessian_comm
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :
    globalCandidateAGaugeGraphHessian
        period hPeriod metric first second =
      globalCandidateAGaugeGraphHessian
        period hPeriod metric second first := by
  rw [globalCandidateAGaugeGraphHessian_apply,
    globalCandidateAGaugeGraphHessian_apply,
    globalPairedGeneralMetricDeDonderGraphHessian_comm,
    globalPairedAbelianLorenzGraphHessian_comm]

/-- Pull the gauge Hessian back along a bounded linear chart map.  This keeps
the chart's chosen calculus structures encapsulated for downstream products. -/
def globalCandidateAGaugeGraphHessianPullback
    {E : Type*}
    [domainGroup : NormedAddCommGroup E]
    [domainNorm : NormedSpace Real E]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (projection : E →L[Real]
      GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :
    E →L[Real] E →L[Real] Real :=
  @ContinuousLinearMap.bilinearComp
    Real Real Real
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric) Real
    inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (candidateGaugeGraphNormedSpace period hPeriod metric)
    (candidateGaugeGraphNormedSpace period hPeriod metric) inferInstance
    (RingHom.id Real) (RingHom.id Real)
    E E inferInstance inferInstance
    Real Real inferInstance inferInstance inferInstance inferInstance
    (RingHom.id Real) (RingHom.id Real)
    (RingHom.id Real) (RingHom.id Real)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAGaugeGraphHessian period hPeriod metric)
    projection projection

/-- On the common smooth core, this is exactly the sum of the two physical
de Donder pairings and the unchanged reduced Abelian BRST polarization. -/
theorem globalCandidateAGaugeGraphHessian_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalCandidateAGaugeSmoothCore period hPeriod) :
    globalCandidateAGaugeGraphHessian period hPeriod metric
        (globalCandidateAGaugeSmoothEmbedding
          period hPeriod metric first)
        (globalCandidateAGaugeSmoothEmbedding
          period hPeriod metric second) =
      globalGeneralMetricDeDonderGaugePairingValue
          period hPeriod (metric .plus)
          (first.1 .plus) (second.1 .plus) +
        globalGeneralMetricDeDonderGaugePairingValue
          period hPeriod (metric .minus)
          (first.1 .minus) (second.1 .minus) +
        globalPairedAbelianGaugeFermionBRSTPolarizationAction
          period hPeriod metric
          (globalPairedAbelianLorenzOnShellState
            period hPeriod metric first.2)
          (globalPairedAbelianLorenzOnShellState
            period hPeriod metric second.2)
          (intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) := by
  rw [globalCandidateAGaugeGraphHessian_apply]
  simp only [globalCandidateAGaugeSmoothEmbedding_fst,
    globalCandidateAGaugeSmoothEmbedding_snd]
  rw [globalPairedGeneralMetricDeDonderGraphHessian_smooth,
    globalPairedAbelianLorenzGraphHessian_apply]
  simp only [globalPairedAbelianLorenzFeatureProjection_smooth]
  rw [globalPairedAbelianLorenzFeature_inner_eq_BRST]

/-- Quadratic physical gauge action on the combined graph chart. -/
def globalCandidateAGaugeGraphAction
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateAGaugeGraphHilbert
      period hPeriod metric) : Real :=
  (1 / 2 : Real) *
    globalCandidateAGaugeGraphHessian
      period hPeriod metric state state

private theorem symmetricQuadratic_hasFDerivAt
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

theorem globalCandidateAGaugeGraphAction_hasFDerivAt
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateAGaugeGraphHilbert
      period hPeriod metric) :
    HasFDerivAt
      (globalCandidateAGaugeGraphAction period hPeriod metric)
      (globalCandidateAGaugeGraphHessian
        period hPeriod metric state)
      state := by
  exact @symmetricQuadratic_hasFDerivAt
    (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
    inferInstance
    (candidateGaugeGraphNormedSpace period hPeriod metric)
    (globalCandidateAGaugeGraphHessian
      period hPeriod metric)
    (globalCandidateAGaugeGraphHessian_comm
      period hPeriod metric)
    state

theorem globalCandidateAGaugeGraphAction_fderiv
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalCandidateAGaugeGraphHilbert
      period hPeriod metric) :
    fderiv Real
        (globalCandidateAGaugeGraphAction
          period hPeriod metric) state =
      globalCandidateAGaugeGraphHessian
        period hPeriod metric state :=
  (globalCandidateAGaugeGraphAction_hasFDerivAt
    period hPeriod metric state).fderiv

theorem globalCandidateAGaugeGraphAction_second_fderiv
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (base : GlobalCandidateAGaugeGraphHilbert
      period hPeriod metric) :
    fderiv Real
        (fun state => fderiv Real
          (globalCandidateAGaugeGraphAction
            period hPeriod metric) state)
        base =
      globalCandidateAGaugeGraphHessian
        period hPeriod metric := by
  rw [show
      (fun state => fderiv Real
        (globalCandidateAGaugeGraphAction
          period hPeriod metric) state) =
      (fun state =>
        globalCandidateAGaugeGraphHessian
          period hPeriod metric state) from by
    funext state
    exact globalCandidateAGaugeGraphAction_fderiv
      period hPeriod metric state]
  exact ContinuousLinearMap.fderiv
    (𝕜 := Real)
    (E := GlobalCandidateAGaugeGraphHilbert
      period hPeriod metric)
    (F := GlobalCandidateAGaugeGraphHilbert
        period hPeriod metric →L[Real] Real)
    (globalCandidateAGaugeGraphHessian
      period hPeriod metric)

theorem globalCandidateAGaugeGraphAction_contDiff
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real ⊤
      (globalCandidateAGaugeGraphAction
        period hPeriod metric) := by
  unfold globalCandidateAGaugeGraphAction
  have hHessian :
      ContDiff Real ⊤
        (globalCandidateAGaugeGraphHessian
          period hPeriod metric) :=
    @ContinuousLinearMap.contDiff
      Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (GlobalCandidateAGaugeGraphHilbert
          period hPeriod metric →L[Real] Real)
      inferInstance
      inferInstance
      (candidateGaugeGraphNormedSpace period hPeriod metric)
      inferInstance
      inferInstance
      ⊤
      (globalCandidateAGaugeGraphHessian
        period hPeriod metric)
  have hIdentity :
      ContDiff Real ⊤
        (id :
          GlobalCandidateAGaugeGraphHilbert period hPeriod metric →
            GlobalCandidateAGaugeGraphHilbert period hPeriod metric) :=
    @contDiff_id
      Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      inferInstance
      inferInstance
      (candidateGaugeGraphNormedSpace period hPeriod metric)
      ⊤
  have hDiagonal :
      ContDiff Real ⊤
        (fun state =>
          globalCandidateAGaugeGraphHessian
            period hPeriod metric state state) :=
    @ContDiff.clm_apply
      Real
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      (GlobalCandidateAGaugeGraphHilbert period hPeriod metric)
      Real
      inferInstance
      inferInstance
      (candidateGaugeGraphNormedSpace period hPeriod metric)
      inferInstance
      (candidateGaugeGraphNormedSpace period hPeriod metric)
      inferInstance
      inferInstance
      ⊤
      (globalCandidateAGaugeGraphHessian period hPeriod metric)
      id
      hHessian
      hIdentity
  exact contDiff_const.mul hDiagonal

theorem globalCandidateAGaugeGraphAction_contDiff_two
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (globalCandidateAGaugeGraphAction
        period hPeriod metric) :=
  (globalCandidateAGaugeGraphAction_contDiff
    period hPeriod metric).of_le (by simp)

theorem globalCandidateAGaugeGraphAction_second_fderiv_smooth
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (base : GlobalCandidateAGaugeGraphHilbert
      period hPeriod metric)
    (first second : GlobalCandidateAGaugeSmoothCore
      period hPeriod) :
    fderiv Real
        (fun state => fderiv Real
          (globalCandidateAGaugeGraphAction
            period hPeriod metric) state)
        base
        (globalCandidateAGaugeSmoothEmbedding
          period hPeriod metric first)
        (globalCandidateAGaugeSmoothEmbedding
          period hPeriod metric second) =
      globalGeneralMetricDeDonderGaugePairingValue
          period hPeriod (metric .plus)
          (first.1 .plus) (second.1 .plus) +
        globalGeneralMetricDeDonderGaugePairingValue
          period hPeriod (metric .minus)
          (first.1 .minus) (second.1 .minus) +
        globalPairedAbelianGaugeFermionBRSTPolarizationAction
          period hPeriod metric
          (globalPairedAbelianLorenzOnShellState
            period hPeriod metric first.2)
          (globalPairedAbelianLorenzOnShellState
            period hPeriod metric second.2)
          (intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) := by
  rw [globalCandidateAGaugeGraphAction_second_fderiv]
  exact globalCandidateAGaugeGraphHessian_smooth
    period hPeriod metric first second

/-! ## The same smooth core in the corrected typed tangent -/

/-- Metric and intrinsic Abelian directions inserted together in the corrected
minimal physical tangent. -/
def globalCandidateAGaugeSmoothCoreMinimalTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalCandidateAGaugeSmoothCore period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration :=
  ((globalMetricPerturbationMinimalPhysicalTangentLinearMap
      period hPeriod configuration).comp
    (LinearMap.fst Real
      (GlobalMetricPerturbationPair period hPeriod)
      (GlobalPairedAbelianPotentialSmooth period hPeriod))) +
  ((globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
      period hPeriod data).comp
    (LinearMap.snd Real
      (GlobalMetricPerturbationPair period hPeriod)
      (GlobalPairedAbelianPotentialSmooth period hPeriod)))

/-- The combined physical gauge core in the typed gauge-fixed tangent; the
nine nonminimal coordinates are unchanged. -/
def globalCandidateAGaugeSmoothCoreGaugeFixedTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    GlobalCandidateAGaugeSmoothCore period hPeriod →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent
        period hPeriod configuration :=
  (globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
      period hPeriod configuration).comp
    (globalCandidateAGaugeSmoothCoreMinimalTangentLinearMap
      period hPeriod data)

@[simp]
theorem globalCandidateAGaugeSmoothCoreGaugeFixedTangent_nonminimal
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (core : GlobalCandidateAGaugeSmoothCore period hPeriod) :
    (globalCandidateAGaugeSmoothCoreGaugeFixedTangentLinearMap
      period hPeriod configuration data core).2 =
      0 :=
  rfl

/-- One faithful map records both the analytic graph-chart point and its
typed physical tangent direction. -/
def globalCandidateAGaugeGraphTypedCoreLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    GlobalCandidateAGaugeSmoothCore period hPeriod →ₗ[Real]
      (GlobalCandidateAGaugeGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) ×
        GlobalGaugeFixedPhysicalFieldTangent
          period hPeriod configuration) where
  toFun core :=
    (globalCandidateAGaugeSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) core,
      globalCandidateAGaugeSmoothCoreGaugeFixedTangentLinearMap
        period hPeriod configuration data core)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateAGaugeSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          ).map_add first second
    · exact
        (globalCandidateAGaugeSmoothCoreGaugeFixedTangentLinearMap
          period hPeriod configuration data).map_add first second
  map_smul' scalar core := by
    apply Prod.ext
    · exact
        (globalCandidateAGaugeSmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          ).map_smul scalar core
    · exact
        (globalCandidateAGaugeSmoothCoreGaugeFixedTangentLinearMap
          period hPeriod configuration data).map_smul scalar core

theorem globalCandidateAGaugeGraphTypedCoreLinearMap_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    Function.Injective
      (globalCandidateAGaugeGraphTypedCoreLinearMap
        period hPeriod configuration data) := by
  intro first second hEqual
  apply globalCandidateAGaugeSmoothEmbedding_injective
    period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalCandidateAGaugeGraphC2Chart4D
end JanusFormal
