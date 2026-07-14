import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorPhysicalRealizationAtlas

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open P0EFTJanusRieszShapeOperatorBundleDescent
open P0EFTJanusRieszShapeOperatorMetricAtlasInterface
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover

universe u v w x y

/-- Local coordinate expressions together with a proof that they all realize one
and the same physical operator family. -/
structure PhysicalRealizationData
    (Chart : Type u) (Base : Type v) (PhysicalOperator : Type w) where
  valid : Chart → Base → Prop
  physicalOperator : Base → PhysicalOperator
  localOperator : Chart → Base → PhysicalOperator
  realizes :
    ∀ chart base, valid chart base →
      localOperator chart base = physicalOperator base

variable {Chart : Type u} {Base : Type v} {PhysicalOperator : Type w}

/-- Physical realization immediately implies overlap compatibility. -/
theorem PhysicalRealizationData.overlapCompatible
    (data : PhysicalRealizationData Chart Base PhysicalOperator)
    (first second : Chart) (base : Base)
    (hFirst : data.valid first base)
    (hSecond : data.valid second base) :
    data.localOperator first base = data.localOperator second base := by
  rw [data.realizes first base hFirst, data.realizes second base hSecond]

/-- Any covered physical-realization family defines a metric atlas. -/
def metricAtlasOfPhysicalRealization
    {TangentModel : Type x} {NormalModel : Type y}
    [TopologicalSpace Base]
    (data : PhysicalRealizationData Chart Base PhysicalOperator)
    (hCover : ∀ base, ∃ chart, data.valid chart base)
    (hEventually :
      ∀ chart base, data.valid chart base →
        ∀ᶠ nearby in 𝓝 base, data.valid chart nearby) :
    MetricFiberAtlas Chart Base TangentModel NormalModel PhysicalOperator where
  valid := data.valid
  cover := hCover
  valid_eventually := hEventually
  localOperator := data.localOperator
  overlapCompatible := data.overlapCompatible

/-- The descended global operator is exactly the originally realized physical
operator. -/
theorem descendedMetricOperator_eq_physicalOperator
    {TangentModel : Type x} {NormalModel : Type y}
    [TopologicalSpace Base]
    (data : PhysicalRealizationData Chart Base PhysicalOperator)
    (hCover : ∀ base, ∃ chart, data.valid chart base)
    (hEventually :
      ∀ chart base, data.valid chart base →
        ∀ᶠ nearby in 𝓝 base, data.valid chart nearby) :
    descendedMetricOperator
      (metricAtlasOfPhysicalRealization
        (TangentModel := TangentModel) (NormalModel := NormalModel)
        data hCover hEventually) = data.physicalOperator := by
  funext base
  obtain ⟨chart, hValid⟩ := hCover base
  rw [← localOperator_eq_descendedMetricOperator
    (metricAtlasOfPhysicalRealization
      (TangentModel := TangentModel) (NormalModel := NormalModel)
      data hCover hEventually) chart base hValid]
  exact data.realizes chart base hValid

/-- Smoothness of the physical operator can be proved either directly or by
smooth local descent; both descriptions coincide. -/
theorem physicalOperator_contDiff_of_local
    {E : Type v} {F : Type w}
    {TangentModel : Type x} {NormalModel : Type y}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (data : PhysicalRealizationData Chart E F)
    (hCover : ∀ base, ∃ chart, data.valid chart base)
    (hEventually :
      ∀ chart base, data.valid chart base →
        ∀ᶠ nearby in 𝓝 base, data.valid chart nearby)
    (hLocalSmooth : ∀ chart, ContDiff ℝ ∞ (data.localOperator chart)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  rw [← descendedMetricOperator_eq_physicalOperator
    (TangentModel := TangentModel) (NormalModel := NormalModel)
    data hCover hEventually]
  exact descendedMetricOperator_contDiff
    (metricAtlasOfPhysicalRealization
      (TangentModel := TangentModel) (NormalModel := NormalModel)
      data hCover hEventually) hLocalSmooth

/-- Exact boundary after physical-realization compatibility. -/
structure PhysicalRealizationStatus where
  localCoordinateOperatorsConstructed : Prop
  physicalRealizationIdentityProved : Prop
  overlapCompatibilityDerived : Prop
  atlasCoverSupplied : Prop
  globalOperatorIdentified : Prop
  localSmoothnessSupplied : Prop
  globalSmoothnessDerived : Prop

/-- Full closure of physical-realization descent. -/
def physicalRealizationClosed (s : PhysicalRealizationStatus) : Prop :=
  s.localCoordinateOperatorsConstructed ∧
  s.physicalRealizationIdentityProved ∧
  s.overlapCompatibilityDerived ∧
  s.atlasCoverSupplied ∧
  s.globalOperatorIdentified ∧
  s.localSmoothnessSupplied ∧
  s.globalSmoothnessDerived

/-- Once physical realization is proved, overlap compatibility is not an
independent obstruction. -/
theorem missing_realization_blocks_compatibility
    (s : PhysicalRealizationStatus)
    (hMissing : Not s.physicalRealizationIdentityProved) :
    Not (physicalRealizationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.1

end

end P0EFTJanusRieszShapeOperatorPhysicalRealizationAtlas
end JanusFormal
