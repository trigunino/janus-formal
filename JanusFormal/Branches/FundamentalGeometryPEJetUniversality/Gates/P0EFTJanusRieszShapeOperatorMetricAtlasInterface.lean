import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorLocalRegularityDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorMetricAtlasInterface

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff
open P0EFTJanusRieszShapeOperatorBundleDescent
open P0EFTJanusRieszShapeOperatorLocalRegularityDescent

universe u v w x y

/-- Abstract local metric trivialization interface for varying tangent and normal
fibers over a structured-jet base.

This structure does not assert that such an atlas exists for Janus. It records
exactly the data whose existence must still be proved geometrically. -/
structure MetricFiberAtlas
    (Chart : Type u) (Base : Type v)
    (TangentModel : Type w) (NormalModel : Type x)
    (PhysicalOperator : Type y)
    [TopologicalSpace Base] where
  valid : Chart → Base → Prop
  cover : ∀ base, ∃ chart, valid chart base
  valid_eventually :
    ∀ chart base, valid chart base →
      ∀ᶠ nearby in 𝓝 base, valid chart nearby
  localOperator : Chart → Base → PhysicalOperator
  overlapCompatible :
    ∀ first second base,
      valid first base → valid second base →
        localOperator first base = localOperator second base

variable {Chart : Type u} {Base : Type v}
variable {TangentModel : Type w} {NormalModel : Type x}
variable {PhysicalOperator : Type y}
variable [TopologicalSpace Base]

/-- Forget the metric-model bookkeeping and retain the local descent data. -/
def MetricFiberAtlas.toNeighborhoodLocalDescentData
    (atlas : MetricFiberAtlas Chart Base TangentModel NormalModel PhysicalOperator) :
    NeighborhoodLocalDescentData Chart Base PhysicalOperator where
  valid := atlas.valid
  localValue := atlas.localOperator
  cover := atlas.cover
  compatible := atlas.overlapCompatible
  valid_eventually := atlas.valid_eventually

/-- Canonical global physical operator family determined by a compatible metric
atlas. -/
def descendedMetricOperator
    (atlas : MetricFiberAtlas Chart Base TangentModel NormalModel PhysicalOperator) :
    Base → PhysicalOperator :=
  descendedValue atlas.toNeighborhoodLocalDescentData.toLocalDescentData

/-- Every valid metric chart computes the same global physical operator. -/
theorem localOperator_eq_descendedMetricOperator
    (atlas : MetricFiberAtlas Chart Base TangentModel NormalModel PhysicalOperator)
    (chart : Chart) (base : Base)
    (hValid : atlas.valid chart base) :
    atlas.localOperator chart base = descendedMetricOperator atlas base := by
  exact localValue_eq_descendedValue
    atlas.toNeighborhoodLocalDescentData.toLocalDescentData
    chart base hValid

/-- Smooth local operator representatives yield a smooth global operator family
once the actual metric atlas has been supplied. -/
theorem descendedMetricOperator_contDiff
    {E : Type v} {F : Type y}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (atlas : MetricFiberAtlas Chart E TangentModel NormalModel F)
    (hLocalSmooth : ∀ chart, ContDiff ℝ ∞ (atlas.localOperator chart)) :
    ContDiff ℝ ∞ (descendedMetricOperator atlas) := by
  exact contDiff_descends atlas.toNeighborhoodLocalDescentData hLocalSmooth

/-- Exact boundary of the metric-atlas interface. -/
structure MetricAtlasStatus where
  varyingTangentMetricFramesConstructed : Prop
  varyingNormalMetricFramesConstructed : Prop
  neighborhoodStableCoverProved : Prop
  localRieszOperatorsConstructed : Prop
  overlapCompatibilityProved : Prop
  localSmoothnessProved : Prop
  globalSmoothRieszOperatorDescended : Prop
  instantiatedOnActualJanusJetBase : Prop

/-- Full closure of the metric-atlas stage. -/
def metricAtlasClosed (s : MetricAtlasStatus) : Prop :=
  s.varyingTangentMetricFramesConstructed ∧
  s.varyingNormalMetricFramesConstructed ∧
  s.neighborhoodStableCoverProved ∧
  s.localRieszOperatorsConstructed ∧
  s.overlapCompatibilityProved ∧
  s.localSmoothnessProved ∧
  s.globalSmoothRieszOperatorDescended ∧
  s.instantiatedOnActualJanusJetBase

/-- The interface theorem does not manufacture the actual Janus atlas. -/
theorem missing_actual_jet_atlas_blocks_metric_closure
    (s : MetricAtlasStatus)
    (hMissing : Not s.instantiatedOnActualJanusJetBase) :
    Not (metricAtlasClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorMetricAtlasInterface
end JanusFormal
