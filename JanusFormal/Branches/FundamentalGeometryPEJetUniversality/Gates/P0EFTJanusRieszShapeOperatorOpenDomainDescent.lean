import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorLocalRegularityDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorOpenDomainDescent

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff
open P0EFTJanusRieszShapeOperatorBundleDescent
open P0EFTJanusRieszShapeOperatorLocalRegularityDescent

universe u v w

/-- Descent data whose chart-validity loci are open and whose local
representatives are smooth only on their own chart domains.

This is the natural regularity package for Gram--Schmidt charts: no arbitrary
global smooth extension of a chart expression is required. -/
structure OpenDomainLocalDescentData
    (Chart : Type u) (Base : Type v) (Fiber : Type w)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]
    extends LocalDescentData Chart Base Fiber where
  domainOpen : ∀ chart, IsOpen {base | valid chart base}
  localContDiffOn :
    ∀ chart, ContDiffOn ℝ ∞ (localValue chart) {base | valid chart base}

variable {Chart : Type u} {Base : Type v} {Fiber : Type w}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

/-- Open chart domains are automatically stable on neighborhoods. -/
def OpenDomainLocalDescentData.toNeighborhoodLocalDescentData
    (data : OpenDomainLocalDescentData Chart Base Fiber) :
    NeighborhoodLocalDescentData Chart Base Fiber where
  valid := data.valid
  localValue := data.localValue
  cover := data.cover
  compatible := data.compatible
  valid_eventually := by
    intro chart base hValid
    exact (data.domainOpen chart).eventually_mem hValid

/-- On a valid open chart, the descended value agrees eventually with the local
smooth representative. -/
theorem descendedValue_eventuallyEq_openLocalValue
    (data : OpenDomainLocalDescentData Chart Base Fiber)
    (chart : Chart) (base : Base)
    (hValid : data.valid chart base) :
    descendedValue data.toLocalDescentData =ᶠ[𝓝 base]
      data.localValue chart := by
  exact descendedValue_eventuallyEq_localValue
    data.toNeighborhoodLocalDescentData chart base hValid

/-- Smoothness of a chart representative on its open validity domain gives
ordinary pointwise smoothness at every valid point. -/
theorem localValue_contDiffAt
    (data : OpenDomainLocalDescentData Chart Base Fiber)
    (chart : Chart) (base : Base)
    (hValid : data.valid chart base) :
    ContDiffAt ℝ ∞ (data.localValue chart) base := by
  exact (data.localContDiffOn chart).contDiffAt
    ((data.domainOpen chart).mem_nhds hValid)

/-- Compatible representatives that are smooth only on their own open chart
domains descend to a globally smooth function. -/
theorem descendedValue_contDiff
    (data : OpenDomainLocalDescentData Chart Base Fiber) :
    ContDiff ℝ ∞ (descendedValue data.toLocalDescentData) := by
  rw [contDiff_iff_contDiffAt]
  intro base
  obtain ⟨chart, hValid⟩ := data.cover base
  exact (localValue_contDiffAt data chart base hValid).congr_of_eventuallyEq
    (descendedValue_eventuallyEq_openLocalValue data chart base hValid)

/-- The globally descended smooth function is uniquely characterized by the
local chart values. -/
theorem descendedValue_contDiff_unique
    (data : OpenDomainLocalDescentData Chart Base Fiber)
    (candidate : Base → Fiber)
    (hCandidate :
      ∀ chart base, data.valid chart base →
        candidate base = data.localValue chart base) :
    candidate = descendedValue data.toLocalDescentData := by
  exact descendedValue_unique data.toLocalDescentData candidate hCandidate

/-- Exact boundary after open-domain smooth descent. -/
structure OpenDomainDescentStatus where
  openChartCoverSupplied : Prop
  overlapCompatibilitySupplied : Prop
  chartwiseContDiffOnSupplied : Prop
  globalValueDescended : Prop
  globalContDiffProved : Prop
  instantiatedOnGramSchmidtCharts : Prop

/-- Closure of open-domain smooth descent. -/
def openDomainDescentClosed (s : OpenDomainDescentStatus) : Prop :=
  s.openChartCoverSupplied ∧
  s.overlapCompatibilitySupplied ∧
  s.chartwiseContDiffOnSupplied ∧
  s.globalValueDescended ∧
  s.globalContDiffProved ∧
  s.instantiatedOnGramSchmidtCharts

/-- The abstract theorem still requires an actual Gram--Schmidt chart
instantiation. -/
theorem missing_gramSchmidt_instantiation_blocks_open_domain_closure
    (s : OpenDomainDescentStatus)
    (hMissing : Not s.instantiatedOnGramSchmidtCharts) :
    Not (openDomainDescentClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorOpenDomainDescent
end JanusFormal
