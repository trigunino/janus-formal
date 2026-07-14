import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothAdaptedFrame
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorMetricAtlasInterface

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedAtlas

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff InnerProductSpace
open P0EFTJanusSmoothProjectorField
open P0EFTJanusSmoothAdaptedFrame
open P0EFTJanusRieszShapeOperatorMetricAtlasInterface

universe u v w x y

variable {Chart : Type u} {Base : Type v} {Ambient : Type w}
variable {TangentModel : Type x} {NormalModel : Type y}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

/-- A chart is represented by a finite family of smooth ambient seed fields.
After projection to the normal complement, its validity domain is exactly the
open locus where the projected family is linearly independent. -/
structure ProjectedSeedChartFamily
    (Chart : Type u) (Base : Type v) (Ambient : Type w)
    (κ : Type*)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient] where
  seed : Chart → κ → Base → Ambient
  seed_contDiff : ∀ chart k, ContDiff ℝ ∞ (seed chart k)

variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Validity domain of one projected-seed normal chart. -/
def projectedSeedChartValid
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base) : Prop :=
  base ∈ normalIndependenceLocus tangentFrame (charts.seed chart)

/-- Every projected-seed chart domain is open. -/
theorem projectedSeedChartValid_isOpen
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (chart : Chart) :
    IsOpen {base | projectedSeedChartValid tangentFrame charts chart base} := by
  exact normalIndependenceLocus_isOpen tangentFrame (charts.seed chart)
    hTangent (charts.seed_contDiff chart)

/-- Validity of a projected-seed chart persists on a neighborhood. -/
theorem projectedSeedChartValid_eventually
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (chart : Chart) (base : Base)
    (hValid : projectedSeedChartValid tangentFrame charts chart base) :
    ∀ᶠ nearby in 𝓝 base,
      projectedSeedChartValid tangentFrame charts chart nearby := by
  exact (projectedSeedChartValid_isOpen tangentFrame charts hTangent chart).eventually_mem hValid

/-- Normal orthonormal frame associated with one projected-seed chart. -/
def projectedSeedNormalFrame
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (k : κ) (base : Base) : Ambient :=
  smoothNormalFrame tangentFrame (charts.seed chart) k base

/-- The chart normal frame is smooth on its validity domain. -/
theorem projectedSeedNormalFrame_contDiffOn
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (chart : Chart) (k : κ) :
    ContDiffOn ℝ ∞
      (projectedSeedNormalFrame tangentFrame charts chart k)
      {base | projectedSeedChartValid tangentFrame charts chart base} := by
  exact smoothNormalFrame_contDiffOn tangentFrame (charts.seed chart)
    hTangent (charts.seed_contDiff chart) k

/-- The chart normal frame is pointwise orthonormal wherever the chart is valid. -/
theorem projectedSeedNormalFrame_orthonormal
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base)
    (hValid : projectedSeedChartValid tangentFrame charts chart base) :
    Orthonormal ℝ
      (fun k => projectedSeedNormalFrame tangentFrame charts chart k base) := by
  exact smoothNormalFrame_orthonormal tangentFrame (charts.seed chart) hValid

/-- The constructed chart frame is normal to the supplied tangent orthonormal
frame. -/
theorem tangent_inner_projectedSeedNormalFrame_eq_zero
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangentOrthonormal : ∀ base,
      Orthonormal ℝ (fun i => tangentFrame i base))
    (chart : Chart) (base : Base) (i : ι) (k : κ) :
    inner ℝ (tangentFrame i base)
      (projectedSeedNormalFrame tangentFrame charts chart k base) = 0 := by
  exact tangent_inner_smoothNormalFrame_eq_zero tangentFrame
    (charts.seed chart) hTangentOrthonormal base i k

/-- Constructor for the metric-atlas interface from projected-seed chart
validity domains and compatible local physical operators.

The remaining `hCover` hypothesis is now exact: at every base point one must
exhibit at least one seed family whose projected normal vectors form a basis of
the required normal rank. -/
def metricAtlasOfProjectedSeeds
    {PhysicalOperator : Type*}
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
          localOperator first base = localOperator second base) :
    MetricFiberAtlas Chart Base TangentModel NormalModel PhysicalOperator where
  valid := projectedSeedChartValid tangentFrame charts
  cover := hCover
  valid_eventually := by
    intro chart base hValid
    exact projectedSeedChartValid_eventually tangentFrame charts hTangent
      chart base hValid
  localOperator := localOperator
  overlapCompatible := hCompatible

/-- Exact boundary of the projected-seed atlas construction. -/
structure ProjectedSeedAtlasStatus where
  smoothTangentFrameSupplied : Prop
  finiteNormalSeedChartsSupplied : Prop
  chartDomainsOpenProved : Prop
  chartNormalFramesSmoothProved : Prop
  chartNormalFramesOrthonormalProved : Prop
  chartCoverProved : Prop
  localRieszOverlapCompatibilityProved : Prop
  metricAtlasInstantiated : Prop

/-- Full closure of the projected-seed atlas stage. -/
def projectedSeedAtlasClosed (s : ProjectedSeedAtlasStatus) : Prop :=
  s.smoothTangentFrameSupplied ∧
  s.finiteNormalSeedChartsSupplied ∧
  s.chartDomainsOpenProved ∧
  s.chartNormalFramesSmoothProved ∧
  s.chartNormalFramesOrthonormalProved ∧
  s.chartCoverProved ∧
  s.localRieszOverlapCompatibilityProved ∧
  s.metricAtlasInstantiated

/-- The only missing atlas ingredient after the local frame theorems is a cover
by sufficiently independent projected seed families, together with the concrete
Riesz overlap law. -/
theorem missing_chart_cover_blocks_projected_seed_atlas
    (s : ProjectedSeedAtlasStatus)
    (hMissing : Not s.chartCoverProved) :
    Not (projectedSeedAtlasClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
end JanusFormal
