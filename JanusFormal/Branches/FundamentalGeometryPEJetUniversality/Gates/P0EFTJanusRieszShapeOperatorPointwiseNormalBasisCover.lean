import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedAtlas

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff InnerProductSpace
open P0EFTJanusSmoothProjectorField
open P0EFTJanusSmoothAdaptedFrame
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas

universe u v

variable {Base : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Pointwise normal basis data. No smooth dependence on the center is assumed:
each center supplies only one orthonormal normal basis used as a constant seed
family for its own local chart. -/
structure PointwiseNormalBasisData
    (Base : Type u) (Ambient : Type v) (ι κ : Type*)
    [NormedAddCommGroup Base] [NormedSpace ℝ Base]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient] where
  tangentFrame : ι → Base → Ambient
  tangent_contDiff : ∀ i, ContDiff ℝ ∞ (tangentFrame i)
  tangent_orthonormal : ∀ base,
    Orthonormal ℝ (fun i => tangentFrame i base)
  normalBasisAt : Base → κ → Ambient
  normal_orthonormal : ∀ base,
    Orthonormal ℝ (normalBasisAt base)
  tangent_normal_orthogonal :
    ∀ base i k,
      inner ℝ (tangentFrame i base) (normalBasisAt base k) = 0

/-- Constant ambient seeds associated with a chart center. -/
def pointwiseNormalSeedCharts
    (data : PointwiseNormalBasisData Base Ambient ι κ) :
    ProjectedSeedChartFamily Base Base Ambient κ where
  seed := fun center k _ => data.normalBasisAt center k
  seed_contDiff := by
    intro center k
    exact contDiff_const

/-- Tangent projection of a pointwise normal basis vector vanishes at its chart
center. -/
theorem tangentProjector_normalBasisAt_center
    (data : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) (k : κ) :
    tangentProjector data.tangentFrame center (data.normalBasisAt center k) = 0 := by
  classical
  unfold tangentProjector
  apply Finset.sum_eq_zero
  intro i hi
  simp [data.tangent_normal_orthogonal center i k]

/-- Normal projection fixes each pointwise normal basis vector at its chart
center. -/
theorem normalProjector_normalBasisAt_center
    (data : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) (k : κ) :
    normalProjector data.tangentFrame center (data.normalBasisAt center k) =
      data.normalBasisAt center k := by
  rw [normalProjector, tangentProjector_normalBasisAt_center data center k,
    sub_zero]

/-- The chart centered at a point is valid at that point. -/
theorem pointwiseNormalSeedChart_valid_at_center
    (data : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    projectedSeedChartValid data.tangentFrame
      (pointwiseNormalSeedCharts data) center center := by
  change LinearIndependent ℝ
    (fun k => normalProjector data.tangentFrame center
      (data.normalBasisAt center k))
  simpa [normalProjector_normalBasisAt_center data center] using
    (data.normal_orthonormal center).linearIndependent

/-- The point-centered projected-seed charts cover the whole base. -/
theorem pointwiseNormalSeedCharts_cover
    (data : PointwiseNormalBasisData Base Ambient ι κ) :
    ∀ base, ∃ center,
      projectedSeedChartValid data.tangentFrame
        (pointwiseNormalSeedCharts data) center base := by
  intro base
  exact ⟨base, pointwiseNormalSeedChart_valid_at_center data base⟩

/-- Each point-centered chart contains an open neighborhood of its center. -/
theorem pointwiseNormalSeedChart_eventually_valid
    (data : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    ∀ᶠ nearby in 𝓝 center,
      projectedSeedChartValid data.tangentFrame
        (pointwiseNormalSeedCharts data) center nearby := by
  exact projectedSeedChartValid_eventually data.tangentFrame
    (pointwiseNormalSeedCharts data) data.tangent_contDiff center center
    (pointwiseNormalSeedChart_valid_at_center data center)

/-- Constructor for a covered metric atlas from pointwise normal bases and a
compatible family of local physical operators. -/
def metricAtlasOfPointwiseNormalBases
    {TangentModel NormalModel PhysicalOperator : Type*}
    (data : PointwiseNormalBasisData Base Ambient ι κ)
    (localOperator : Base → Base → PhysicalOperator)
    (hCompatible :
      ∀ first second base,
        projectedSeedChartValid data.tangentFrame
          (pointwiseNormalSeedCharts data) first base →
        projectedSeedChartValid data.tangentFrame
          (pointwiseNormalSeedCharts data) second base →
        localOperator first base = localOperator second base) :
    P0EFTJanusRieszShapeOperatorMetricAtlasInterface.MetricFiberAtlas
      Base Base TangentModel NormalModel PhysicalOperator :=
  metricAtlasOfProjectedSeeds data.tangentFrame
    (pointwiseNormalSeedCharts data) data.tangent_contDiff localOperator
    (pointwiseNormalSeedCharts_cover data) hCompatible

/-- Exact boundary after the pointwise-normal-basis cover theorem. -/
structure PointwiseBasisCoverStatus where
  pointwiseTangentOrthonormalFramesSupplied : Prop
  pointwiseNormalOrthonormalBasesSupplied : Prop
  tangentNormalOrthogonalitySupplied : Prop
  constantSeedChartsConstructed : Prop
  centerValidityProved : Prop
  openCoverProved : Prop
  concreteLocalRieszCompatibilityProved : Prop
  globalSmoothRieszFamilyConstructed : Prop

/-- Closure of the pointwise-basis atlas stage. -/
def pointwiseBasisCoverClosed (s : PointwiseBasisCoverStatus) : Prop :=
  s.pointwiseTangentOrthonormalFramesSupplied ∧
  s.pointwiseNormalOrthonormalBasesSupplied ∧
  s.tangentNormalOrthogonalitySupplied ∧
  s.constantSeedChartsConstructed ∧
  s.centerValidityProved ∧
  s.openCoverProved ∧
  s.concreteLocalRieszCompatibilityProved ∧
  s.globalSmoothRieszFamilyConstructed

/-- After the cover theorem, the remaining substantive step is compatibility of
the concrete local Riesz expressions and their local smoothness. -/
theorem missing_riesz_compatibility_blocks_global_family
    (s : PointwiseBasisCoverStatus)
    (hMissing : Not s.concreteLocalRieszCompatibilityProved) :
    Not (pointwiseBasisCoverClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
end JanusFormal
