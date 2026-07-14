import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorMetricAtlasInterface
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenDomainDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorOpenMetricAtlas

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open P0EFTJanusRieszShapeOperatorBundleDescent
open P0EFTJanusRieszShapeOperatorMetricAtlasInterface
open P0EFTJanusRieszShapeOperatorOpenDomainDescent

universe u v w x y

/-- A metric atlas whose operator representatives are smooth on their open chart
domains. This is the correct target for projected-seed Gram--Schmidt charts. -/
structure OpenMetricFiberAtlas
    (Chart : Type u) (Base : Type v)
    (TangentModel : Type w) (NormalModel : Type x)
    (PhysicalOperator : Type y)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup PhysicalOperator]
    [NormedSpace ℝ PhysicalOperator]
    extends MetricFiberAtlas Chart Base TangentModel NormalModel PhysicalOperator where
  domainOpen : ∀ chart, IsOpen {base | valid chart base}
  localOperator_contDiffOn :
    ∀ chart, ContDiffOn ℝ ∞ (localOperator chart) {base | valid chart base}

variable {Chart : Type u} {Base : Type v}
variable {TangentModel : Type w} {NormalModel : Type x}
variable {PhysicalOperator : Type y}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup PhysicalOperator]
variable [NormedSpace ℝ PhysicalOperator]

/-- Forget the metric labels and retain the open-domain descent data. -/
def OpenMetricFiberAtlas.toOpenDomainLocalDescentData
    (atlas : OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator) :
    OpenDomainLocalDescentData Chart Base PhysicalOperator where
  valid := atlas.valid
  localValue := atlas.localOperator
  cover := atlas.cover
  compatible := atlas.overlapCompatible
  domainOpen := atlas.domainOpen
  localContDiffOn := atlas.localOperator_contDiffOn

/-- The open metric atlas descends to a globally smooth operator family without
requiring global extensions of its local chart formulas. -/
theorem descendedMetricOperator_contDiffOnCharts
    (atlas : OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator) :
    ContDiff ℝ ∞ (descendedMetricOperator atlas.toMetricFiberAtlas) := by
  exact descendedValue_contDiff atlas.toOpenDomainLocalDescentData

/-- Every valid open metric chart computes the descended global operator. -/
theorem localOperator_eq_descended_openMetricOperator
    (atlas : OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator)
    (chart : Chart) (base : Base)
    (hValid : atlas.valid chart base) :
    atlas.localOperator chart base =
      descendedMetricOperator atlas.toMetricFiberAtlas base := by
  exact localOperator_eq_descendedMetricOperator
    atlas.toMetricFiberAtlas chart base hValid

/-- A physical family realized by every open chart is equal to the descended
operator. -/
theorem physicalOperator_eq_descended
    (atlas : OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator)
    (physical : Base → PhysicalOperator)
    (hRealizes :
      ∀ chart base, atlas.valid chart base →
        atlas.localOperator chart base = physical base) :
    physical = descendedMetricOperator atlas.toMetricFiberAtlas := by
  apply descendedValue_unique
  intro chart base hValid
  exact (hRealizes chart base hValid).symm

/-- Consequently, a physical family realized by all local chart formulas is
smooth. -/
theorem physicalOperator_contDiff
    (atlas : OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator)
    (physical : Base → PhysicalOperator)
    (hRealizes :
      ∀ chart base, atlas.valid chart base →
        atlas.localOperator chart base = physical base) :
    ContDiff ℝ ∞ physical := by
  rw [physicalOperator_eq_descended atlas physical hRealizes]
  exact descendedMetricOperator_contDiffOnCharts atlas

/-- Exact boundary after open metric-atlas descent. -/
structure OpenMetricAtlasStatus where
  openMetricChartsConstructed : Prop
  localOperatorContDiffOnProved : Prop
  overlapCompatibilityProved : Prop
  globalSmoothOperatorDescended : Prop
  physicalFamilyIdentified : Prop
  projectedSeedAtlasInstantiated : Prop

/-- Closure of the open metric-atlas stage. -/
def openMetricAtlasClosed (s : OpenMetricAtlasStatus) : Prop :=
  s.openMetricChartsConstructed ∧
  s.localOperatorContDiffOnProved ∧
  s.overlapCompatibilityProved ∧
  s.globalSmoothOperatorDescended ∧
  s.physicalFamilyIdentified ∧
  s.projectedSeedAtlasInstantiated

/-- The remaining step is the projected-seed instantiation. -/
theorem missing_projected_seed_atlas_blocks_open_metric_closure
    (s : OpenMetricAtlasStatus)
    (hMissing : Not s.projectedSeedAtlasInstantiated) :
    Not (openMetricAtlasClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorOpenMetricAtlas
end JanusFormal
