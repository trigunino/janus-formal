import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenMetricAtlas

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedOpenAtlas

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorOpenMetricAtlas

universe u v w x y

variable {Chart : Type u} {Base : Type v} {Ambient : Type w}
variable {TangentModel : Type x} {NormalModel : Type y}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Projected-seed chart domains, a cover, compatible local operators and
chartwise smoothness define an open metric atlas. -/
def openMetricAtlasOfProjectedSeeds
    {PhysicalOperator : Type*}
    [NormedAddCommGroup PhysicalOperator]
    [NormedSpace ℝ PhysicalOperator]
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (localOperator : Chart → Base → PhysicalOperator)
    (hCover : ∀ base, ∃ chart,
      projectedSeedChartValid tangentFrame charts chart base)
    (hCompatible :
      ∀ first second base,
        projectedSeedChartValid tangentFrame charts first base →
        projectedSeedChartValid tangentFrame charts second base →
          localOperator first base = localOperator second base)
    (hLocalSmooth :
      ∀ chart, ContDiffOn ℝ ∞ (localOperator chart)
        {base | projectedSeedChartValid tangentFrame charts chart base}) :
    OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator where
  toMetricFiberAtlas := metricAtlasOfProjectedSeeds tangentFrame charts
    hTangent localOperator hCover hCompatible
  domainOpen := by
    intro chart
    exact projectedSeedChartValid_isOpen tangentFrame charts hTangent chart
  localOperator_contDiffOn := hLocalSmooth

/-- If every local projected-seed formula realizes one physical operator, then
compatibility on overlaps is automatic. -/
def openMetricAtlasOfProjectedSeedsPhysical
    {PhysicalOperator : Type*}
    [NormedAddCommGroup PhysicalOperator]
    [NormedSpace ℝ PhysicalOperator]
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (physicalOperator : Base → PhysicalOperator)
    (localOperator : Chart → Base → PhysicalOperator)
    (hCover : ∀ base, ∃ chart,
      projectedSeedChartValid tangentFrame charts chart base)
    (hRealizes :
      ∀ chart base,
        projectedSeedChartValid tangentFrame charts chart base →
          localOperator chart base = physicalOperator base)
    (hLocalSmooth :
      ∀ chart, ContDiffOn ℝ ∞ (localOperator chart)
        {base | projectedSeedChartValid tangentFrame charts chart base}) :
    OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator :=
  openMetricAtlasOfProjectedSeeds tangentFrame charts hTangent localOperator
    hCover
    (by
      intro first second base hFirst hSecond
      rw [hRealizes first base hFirst, hRealizes second base hSecond])
    hLocalSmooth

/-- The physical operator realized by smooth projected-seed chart formulas is
globally smooth. -/
theorem projectedSeedPhysicalOperator_contDiff
    {TangentModel : Type x} {NormalModel : Type y}
    {PhysicalOperator : Type*}
    [NormedAddCommGroup PhysicalOperator]
    [NormedSpace ℝ PhysicalOperator]
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (physicalOperator : Base → PhysicalOperator)
    (localOperator : Chart → Base → PhysicalOperator)
    (hCover : ∀ base, ∃ chart,
      projectedSeedChartValid tangentFrame charts chart base)
    (hRealizes :
      ∀ chart base,
        projectedSeedChartValid tangentFrame charts chart base →
          localOperator chart base = physicalOperator base)
    (hLocalSmooth :
      ∀ chart, ContDiffOn ℝ ∞ (localOperator chart)
        {base | projectedSeedChartValid tangentFrame charts chart base}) :
    ContDiff ℝ ∞ physicalOperator := by
  let atlas : OpenMetricFiberAtlas
      Chart Base TangentModel NormalModel PhysicalOperator :=
    openMetricAtlasOfProjectedSeedsPhysical tangentFrame charts hTangent
      physicalOperator localOperator hCover hRealizes hLocalSmooth
  exact P0EFTJanusRieszShapeOperatorOpenMetricAtlas.physicalOperator_contDiff
    atlas physicalOperator hRealizes

/-- Exact boundary after projected-seed open-atlas descent. -/
structure ProjectedSeedOpenAtlasStatus where
  projectedSeedDomainsOpen : Prop
  projectedSeedCoverProved : Prop
  localPhysicalRealizationProved : Prop
  localContDiffOnProved : Prop
  openMetricAtlasConstructed : Prop
  globalPhysicalContDiffProved : Prop
  instantiatedWithRieszFormula : Prop

/-- Closure of projected-seed open-atlas descent. -/
def projectedSeedOpenAtlasClosed
    (s : ProjectedSeedOpenAtlasStatus) : Prop :=
  s.projectedSeedDomainsOpen ∧
  s.projectedSeedCoverProved ∧
  s.localPhysicalRealizationProved ∧
  s.localContDiffOnProved ∧
  s.openMetricAtlasConstructed ∧
  s.globalPhysicalContDiffProved ∧
  s.instantiatedWithRieszFormula

/-- The remaining step is the concrete Riesz formula on each projected-seed
chart. -/
theorem missing_riesz_formula_blocks_projected_seed_open_atlas
    (s : ProjectedSeedOpenAtlasStatus)
    (hMissing : Not s.instantiatedWithRieszFormula) :
    Not (projectedSeedOpenAtlasClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorProjectedSeedOpenAtlas
end JanusFormal
