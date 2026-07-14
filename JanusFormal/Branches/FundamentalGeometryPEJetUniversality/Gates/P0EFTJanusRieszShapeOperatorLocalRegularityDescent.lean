import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorBundleDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorLocalRegularityDescent

set_option autoImplicit false

noncomputable section

open Filter Topology
open P0EFTJanusRieszShapeOperatorBundleDescent

universe u v w

variable {Chart : Type u} {Base : Type v} {Fiber : Type w}
variable [TopologicalSpace Base]

/-- A predicate on global representatives is local when it can be checked using
an eventually equal regular representative around every point. -/
def IsLocalRegularityProperty
    (Regular : (Base → Fiber) → Prop) : Prop :=
  ∀ function : Base → Fiber,
    (∀ base, ∃ localRepresentative : Base → Fiber,
      Regular localRepresentative ∧
        function =ᶠ[𝓝 base] localRepresentative) →
    Regular function

/-- Local descent data with the additional fact that a chart valid at a point
remains valid on some neighborhood of that point. -/
structure NeighborhoodLocalDescentData
    (Chart : Type u) (Base : Type v) (Fiber : Type w)
    [TopologicalSpace Base] extends LocalDescentData Chart Base Fiber where
  valid_eventually :
    ∀ chart base, valid chart base →
      ∀ᶠ nearby in 𝓝 base, valid chart nearby

/-- On a neighborhood where one chart remains valid, the descended value is
eventually equal to that chart's local representative. -/
theorem descendedValue_eventuallyEq_localValue
    (data : NeighborhoodLocalDescentData Chart Base Fiber)
    (chart : Chart) (base : Base)
    (hValid : data.valid chart base) :
    descendedValue data.toLocalDescentData =ᶠ[𝓝 base]
      data.localValue chart := by
  filter_upwards [data.valid_eventually chart base hValid] with nearby hNearby
  exact (localValue_eq_descendedValue data.toLocalDescentData
    chart nearby hNearby).symm

/-- Any genuinely local regularity property descends from regular chart
representatives. -/
theorem regularity_descends
    (data : NeighborhoodLocalDescentData Chart Base Fiber)
    (Regular : (Base → Fiber) → Prop)
    (hLocalProperty : IsLocalRegularityProperty Regular)
    (hLocalRegular : ∀ chart, Regular (data.localValue chart)) :
    Regular (descendedValue data.toLocalDescentData) := by
  apply hLocalProperty (descendedValue data.toLocalDescentData)
  intro base
  obtain ⟨chart, hValid⟩ := data.cover base
  refine ⟨data.localValue chart, hLocalRegular chart, ?_⟩
  exact descendedValue_eventuallyEq_localValue data chart base hValid

/-- Two local regularity proofs give the same descended object because abstract
descent is unique before regularity is considered. -/
theorem regularity_descent_value_unique
    (data : NeighborhoodLocalDescentData Chart Base Fiber)
    (candidate : Base → Fiber)
    (hCandidate :
      ∀ chart base, data.valid chart base →
        candidate base = data.localValue chart base) :
    candidate = descendedValue data.toLocalDescentData := by
  exact descendedValue_unique data.toLocalDescentData candidate hCandidate

/-- Exact boundary after local-property descent. -/
structure RieszLocalRegularityStatus where
  neighborhoodStableAtlasSupplied : Prop
  abstractLocalityPrincipleConnected : Prop
  localRepresentativeRegularitySupplied : Prop
  globalRegularityDescended : Prop
  contDiffLocalityInstantiated : Prop
  actualJanusMetricAtlasInstantiated : Prop

/-- Full closure of local smooth Riesz descent. -/
def rieszLocalRegularityClosed
    (s : RieszLocalRegularityStatus) : Prop :=
  s.neighborhoodStableAtlasSupplied ∧
  s.abstractLocalityPrincipleConnected ∧
  s.localRepresentativeRegularitySupplied ∧
  s.globalRegularityDescended ∧
  s.contDiffLocalityInstantiated ∧
  s.actualJanusMetricAtlasInstantiated

/-- Abstract local-property descent does not by itself provide the concrete
`ContDiff` locality instance or the Janus metric atlas. -/
theorem missing_contDiff_instance_blocks_local_smooth_descent
    (s : RieszLocalRegularityStatus)
    (hMissing : Not s.contDiffLocalityInstantiated) :
    Not (rieszLocalRegularityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorLocalRegularityDescent
end JanusFormal
