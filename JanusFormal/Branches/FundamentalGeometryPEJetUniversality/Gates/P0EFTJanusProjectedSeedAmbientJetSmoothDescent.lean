import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedAmbientJetDescent

namespace JanusFormal
namespace P0EFTJanusProjectedSeedAmbientJetSmoothDescent

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped ContDiff InnerProductSpace Topology
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusProjectedSeedSmoothCoefficientTransport
open P0EFTJanusProjectedSeedAmbientJetDescent

universe u v w x y

variable {Base : Type w} {Tangent : Type u}
variable {Normal : Type v} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- The descended physical Riesz operator is globally smooth. At each point we
use the projected-seed chart centered at that point, whose validity persists on
a neighborhood, and transfer the local `ContDiffOn` proof through the eventual
equality with the descended value. -/
theorem ProjectedSeedGlobalAmbientJetData.descendedPhysicalOperator_contDiff
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    ContDiff ℝ ∞
      (data.descendedPhysicalOperator tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension) := by
  rw [contDiff_iff_contDiffAt]
  intro base
  have hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) base base :=
    pointwiseNormalSeedChart_valid_at_center basisData base
  have hDomainNhds : projectedSeedCoefficientDomain basisData base ∈ 𝓝 base := by
    simpa [projectedSeedCoefficientDomain] using
      (pointwiseNormalSeedChart_eventually_valid basisData base)
  have hLocalAt : ContDiffAt ℝ ∞
      (data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData base) base :=
    (data.localPhysicalOperator_contDiffOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData base).contDiffAt hDomainNhds
  have hEventuallyEq :
      data.descendedPhysicalOperator tangentBasis hTangentBasis normalBasis
          hNormalBasis basisData hDimension =ᶠ[𝓝 base]
        data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
          hNormalBasis basisData base := by
    filter_upwards [hDomainNhds] with nearby hNearby
    exact (data.localPhysicalOperator_eq_descended tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension base nearby hNearby).symm
  exact hLocalAt.congr_of_eventuallyEq hEventuallyEq

/-- The local chart representative and the globally smooth descended operator
coincide at every valid chart point. -/
theorem ProjectedSeedGlobalAmbientJetData.localPhysicalOperator_eq_smoothDescended
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData center base =
      data.descendedPhysicalOperator tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension base :=
  data.localPhysicalOperator_eq_descended tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension center base hValid

/-- Audit boundary after closing the local-to-global smoothness argument for
ambient Janus jet coefficients. -/
structure ProjectedSeedAmbientJetSmoothDescentStatus where
  globalAmbientCoefficientsSupplied : Prop
  chartwiseCoefficientSmoothnessProved : Prop
  chartOverlapCompatibilityProved : Prop
  metricAtlasConstructed : Prop
  globalOperatorDescended : Prop
  globalOperatorSmoothnessProved : Prop
  genuineManifoldSpinCJetExtractionConstructed : Prop

def projectedSeedAmbientJetSmoothDescentClosed
    (s : ProjectedSeedAmbientJetSmoothDescentStatus) : Prop :=
  s.globalAmbientCoefficientsSupplied ∧
  s.chartwiseCoefficientSmoothnessProved ∧
  s.chartOverlapCompatibilityProved ∧
  s.metricAtlasConstructed ∧
  s.globalOperatorDescended ∧
  s.globalOperatorSmoothnessProved ∧
  s.genuineManifoldSpinCJetExtractionConstructed

theorem missing_genuine_manifold_extraction_blocks_smooth_descent
    (s : ProjectedSeedAmbientJetSmoothDescentStatus)
    (hMissing : Not s.genuineManifoldSpinCJetExtractionConstructed) :
    Not (projectedSeedAmbientJetSmoothDescentClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusProjectedSeedAmbientJetSmoothDescent
end JanusFormal
