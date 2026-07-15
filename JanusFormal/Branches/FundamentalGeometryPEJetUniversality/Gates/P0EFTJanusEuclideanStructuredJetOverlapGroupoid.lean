import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusEuclideanStructuredJetActionGroupoidRealization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedVaryingNormalBundle

namespace JanusFormal
namespace P0EFTJanusEuclideanStructuredJetOverlapGroupoid

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusStructuredJetActionGroupoid
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusConcreteSecondJetChainRule
open P0EFTJanusConcreteAbelianConnectionJet
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusRieszShapeOperatorEquivariance
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusProjectedSeedNormalSpaceTrivialization
open P0EFTJanusProjectedSeedNormalCoefficientOverlap
open P0EFTJanusProjectedSeedSmoothCoefficientTransport
open P0EFTJanusProjectedSeedAmbientJetDescent
open P0EFTJanusProjectedSeedVaryingNormalBundle
open P0EFTJanusEuclideanImmersionConnectionJetExtraction
open P0EFTJanusEuclideanMetricKoszulConnection
open P0EFTJanusEuclideanStructuredJetActionGroupoidRealization

universe u v w y

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]
variable {ι κ : Type y} [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- The canonical residual normal-frame change, with trivial tangent and SpinC
components, between two projected-seed charts at one base point. -/
def euclideanLowOrderOverlapSpinCFrameAt
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (first second base : Tangent) :
    LowOrderSpinCFrame Tangent Normal :=
  ((1, (projectedSeedNormalTransitionOnOverlap data.normalBasis
      data.normalBasis_orthonormal data.basisData data.ambientDimension
      first second).frame base), 1)

/-- On a valid overlap, the packaged smooth transition is the canonical
pointwise normal-frame transition. -/
theorem euclideanLowOrderOverlapSpinCFrameAt_normal_apply
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (first second base : Tangent)
    (hFirst : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) first base)
    (hSecond : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) second base)
    (normal : Normal) :
    (euclideanLowOrderOverlapSpinCFrameAt data first second base).1.2 normal =
      normalFrameTransition
        ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
          data.normalBasis_orthonormal data.basisData first).frame base)
        ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
          data.normalBasis_orthonormal data.basisData second).frame base)
        (projectedSeedNormalFrames_sameRange data.normalBasis
          data.normalBasis_orthonormal data.basisData data.ambientDimension
          first second base hFirst hSecond) normal := by
  apply (projectedSeedNormalEmbedding data.normalBasis
    data.normalBasis_orthonormal data.basisData first base).injective
  change projectedSeedNormalEmbedding data.normalBasis
      data.normalBasis_orthonormal data.basisData first base
        ((projectedSeedNormalTransitionOnOverlap data.normalBasis
          data.normalBasis_orthonormal data.basisData data.ambientDimension
          first second).frame base normal) = _
  rw [projectedSeedNormalTransitionOnOverlap_spec data.normalBasis
    data.normalBasis_orthonormal data.basisData data.ambientDimension
    first second base ⟨hFirst, hSecond⟩ normal]
  exact (normalFrameTransition_spec
    ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
      data.normalBasis_orthonormal data.basisData first).frame base)
    ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
      data.normalBasis_orthonormal data.basisData second).frame base)
    (projectedSeedNormalFrames_sameRange data.normalBasis
      data.normalBasis_orthonormal data.basisData data.ambientDimension
      first second base hFirst hSecond) normal).symm

theorem euclideanLowOrderOverlapSpinCFrameAt_normal
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (first second base : Tangent)
    (hFirst : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) first base)
    (hSecond : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) second base) :
    (euclideanLowOrderOverlapSpinCFrameAt data first second base).1.2 =
      normalFrameTransition
        ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
          data.normalBasis_orthonormal data.basisData first).frame base)
        ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
          data.normalBasis_orthonormal data.basisData second).frame base)
        (projectedSeedNormalFrames_sameRange data.normalBasis
          data.normalBasis_orthonormal data.basisData data.ambientDimension
          first second base hFirst hSecond) := by
  ext normal
  exact euclideanLowOrderOverlapSpinCFrameAt_normal_apply data first second
    base hFirst hSecond normal

@[simp]
theorem euclideanLowOrderOverlapSpinCFrameAt_self
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (center base : Tangent)
    (hValid : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) center base) :
    euclideanLowOrderOverlapSpinCFrameAt data center center base = 1 := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · rw [euclideanLowOrderOverlapSpinCFrameAt_normal data center center
        base hValid hValid]
      apply LinearIsometryEquiv.ext
      intro normal
      apply ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
        data.normalBasis_orthonormal data.basisData center).frame base).injective
      rw [normalFrameTransition_spec]
      rfl
  · rfl

theorem euclideanLowOrderOverlapSpinCFrameAt_cocycle
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (first second third base : Tangent)
    (hFirst : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) first base)
    (hSecond : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) second base)
    (hThird : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) third base) :
    euclideanLowOrderOverlapSpinCFrameAt data first second base *
        euclideanLowOrderOverlapSpinCFrameAt data second third base =
      euclideanLowOrderOverlapSpinCFrameAt data first third base := by
  apply Prod.ext
  · apply Prod.ext
    · simp [euclideanLowOrderOverlapSpinCFrameAt]
    · change
        (euclideanLowOrderOverlapSpinCFrameAt data first second base).1.2 *
            (euclideanLowOrderOverlapSpinCFrameAt data second third base).1.2 =
          (euclideanLowOrderOverlapSpinCFrameAt data first third base).1.2
      rw [euclideanLowOrderOverlapSpinCFrameAt_normal data first second
        base hFirst hSecond]
      rw [euclideanLowOrderOverlapSpinCFrameAt_normal data second third
        base hSecond hThird]
      rw [euclideanLowOrderOverlapSpinCFrameAt_normal data first third
        base hFirst hThird]
      rw [normalFrameTransition_cocycle]
  · simp [euclideanLowOrderOverlapSpinCFrameAt]

/-- The reduced jets extracted in two valid projected-seed charts at the same
base point differ by the canonical residual normal-frame action. -/
theorem euclideanLowOrderStructuredJet_overlap_equivariant
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (first second base : Tangent)
    (hFirst : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) first base)
    (hSecond : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) second base) :
    euclideanLowOrderOverlapSpinCFrameAt data first second base •
        euclideanLowOrderStructuredJetAt data
          ⟨second, base, hSecond⟩ =
      euclideanLowOrderStructuredJetAt data
        ⟨first, base, hFirst⟩ := by
  change actOnReducedData
      (euclideanLowOrderOverlapSpinCFrameAt data first second base).1
      (euclideanLowOrderStructuredJetAt data ⟨second, base, hSecond⟩) =
    euclideanLowOrderStructuredJetAt data ⟨first, base, hFirst⟩
  apply LowOrderReducedData.ext
  · funext x y
    simp only [euclideanLowOrderStructuredJetAt,
      euclideanLowOrderOverlapSpinCFrameAt,
      actOnReducedData, actOnNormalTensor, actualJetToLowOrderReducedData,
      ActualJanusLocalJetData.toReducedJet_secondFundamental, inv_one,
      one_smul]
    let globalData := data.coefficients.toEuclideanImmersionConnectionJetData
      |>.toProjectedSeedGlobalAmbientJetData
    change (projectedSeedNormalTransitionOnOverlap data.normalBasis
        data.normalBasis_orthonormal data.basisData data.ambientDimension
        first second).frame base
          ((globalData.toChartData data.tangentBasis
            data.tangentBasis_orthonormal data.normalBasis
            data.normalBasis_orthonormal data.basisData second).normalQuadratic
              base x y) =
      (globalData.toChartData data.tangentBasis
        data.tangentBasis_orthonormal data.normalBasis
        data.normalBasis_orthonormal data.basisData first).normalQuadratic
          base x y
    change (euclideanLowOrderOverlapSpinCFrameAt data first second base).1.2
        ((globalData.toChartData data.tangentBasis
          data.tangentBasis_orthonormal data.normalBasis
          data.normalBasis_orthonormal data.basisData second).normalQuadratic
            base x y) = _
    rw [euclideanLowOrderOverlapSpinCFrameAt_normal_apply data first second
      base hFirst hSecond]
    change normalFrameTransition
        ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
          data.normalBasis_orthonormal data.basisData first).frame base)
        ((pointwiseBasisSmoothNormalFrameFamilyOn data.normalBasis
          data.normalBasis_orthonormal data.basisData second).frame base)
        (projectedSeedNormalFrames_sameRange data.normalBasis
          data.normalBasis_orthonormal data.basisData data.ambientDimension
          first second base hFirst hSecond)
        (projectedSeedChartNormalAdjointCLM data.normalBasis
          data.normalBasis_orthonormal data.basisData second base
          ((globalData.toChartData data.tangentBasis
            data.tangentBasis_orthonormal data.normalBasis
            data.normalBasis_orthonormal data.basisData second)
              |>.correctedAmbientSecondDerivative base x y)) =
      projectedSeedChartNormalAdjointCLM data.normalBasis
        data.normalBasis_orthonormal data.basisData first base
        ((globalData.toChartData data.tangentBasis
          data.tangentBasis_orthonormal data.normalBasis
          data.normalBasis_orthonormal data.basisData first)
            |>.correctedAmbientSecondDerivative base x y)
    rw [globalData.chart_corrected_eq_global data.tangentBasis
      data.tangentBasis_orthonormal data.normalBasis
      data.normalBasis_orthonormal data.basisData second base hSecond]
    rw [globalData.chart_corrected_eq_global data.tangentBasis
      data.tangentBasis_orthonormal data.normalBasis
      data.normalBasis_orthonormal data.basisData first base hFirst]
    exact (projectedSeedChartNormalAdjoint_transition_apply data.normalBasis
      data.normalBasis_orthonormal data.basisData data.ambientDimension
      first second base hFirst hSecond
      (globalData.correctedAmbientSecondDerivative data.tangentBasis
        data.basisData base x y)).symm
  · funext x y
    simp only [euclideanLowOrderStructuredJetAt,
      euclideanLowOrderOverlapSpinCFrameAt,
      actOnReducedData, pullbackTwoForm, actualJetToLowOrderReducedData,
      ActualJanusLocalJetData.toReducedJet_curvature_apply, inv_one,
      one_smul]
    rfl

/-- Canonical action-groupoid arrow between the actual reduced jets extracted
from two valid projected-seed charts at the same base point. -/
def euclideanLowOrderSpinCOverlapArrow
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (first second base : Tangent)
    (hFirst : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) first base)
    (hSecond : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) second base) :
    ActionArrow (Symmetry := LowOrderSpinCFrame Tangent Normal)
      (euclideanLowOrderStructuredJetAt data ⟨second, base, hSecond⟩)
      (euclideanLowOrderStructuredJetAt data ⟨first, base, hFirst⟩) where
  element := euclideanLowOrderOverlapSpinCFrameAt data first second base
  maps_source := euclideanLowOrderStructuredJet_overlap_equivariant data
    first second base hFirst hSecond

@[simp]
theorem euclideanLowOrderSpinCOverlapArrow_self
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (center base : Tangent)
    (hValid : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) center base) :
    euclideanLowOrderSpinCOverlapArrow data center center base hValid hValid =
      idArrow (euclideanLowOrderStructuredJetAt data
        ⟨center, base, hValid⟩) := by
  apply ActionArrow.ext
  exact euclideanLowOrderOverlapSpinCFrameAt_self data center base hValid

/-- The canonical arrows compose by the Čech overlap law. -/
theorem euclideanLowOrderSpinCOverlapArrow_comp
    (data : EuclideanMetricProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (first second third base : Tangent)
    (hFirst : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) first base)
    (hSecond : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) second base)
    (hThird : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) third base) :
    comp
        (euclideanLowOrderSpinCOverlapArrow data first second base
          hFirst hSecond)
        (euclideanLowOrderSpinCOverlapArrow data second third base
          hSecond hThird) =
      euclideanLowOrderSpinCOverlapArrow data first third base hFirst hThird := by
  apply ActionArrow.ext
  exact euclideanLowOrderOverlapSpinCFrameAt_cocycle data
    first second third base hFirst hSecond hThird

end

end P0EFTJanusEuclideanStructuredJetOverlapGroupoid
end JanusFormal
