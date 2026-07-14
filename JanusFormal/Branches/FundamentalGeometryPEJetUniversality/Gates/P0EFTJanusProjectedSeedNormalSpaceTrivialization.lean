import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedOrthogonalRange
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusConnectionCorrectedActualJetBridge

namespace JanusFormal
namespace P0EFTJanusProjectedSeedNormalSpaceTrivialization

set_option autoImplicit false

noncomputable section

open Set Module
open scoped InnerProductSpace
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedOrthogonalRange
open P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusConnectionCorrectedActualJetBridge

universe u v w x y z

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

/-- Canonical immersion derivative obtained from the supplied global tangent
orthonormal frame.  The chart center is chosen to be the evaluation point, where
pointwise-seed validity is automatic. -/
def projectedSeedTangentDerivative
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) : Tangent →ₗᵢ[ℝ] Ambient :=
  (pointwiseBasisSmoothTangentFrameFamilyOn tangentBasis
    hTangentBasis basisData base).frame base

/-- The canonical derivative has exactly the tangent-frame span as its range. -/
theorem projectedSeedTangentDerivative_range
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) :
    tangentRange
        (projectedSeedTangentDerivative tangentBasis
          hTangentBasis basisData base) =
      tangentFrameSpan basisData base := by
  change normalFrameRange
      ((pointwiseBasisSmoothTangentFrameFamilyOn tangentBasis
        hTangentBasis basisData base).frame base) =
    tangentFrameSpan basisData base
  exact pointwiseBasisSmoothTangentFrameFamilyOn_range tangentBasis
    hTangentBasis basisData base base
    (pointwiseNormalSeedChart_valid_at_center basisData base)

/-- Projected-seed normal embedding on one valid point-centered chart. -/
def projectedSeedNormalEmbedding
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base) : Normal →ₗᵢ[ℝ] Ambient :=
  (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
    hNormalBasis basisData center).frame base

/-- On a valid chart point, the projected normal embedding has range equal to
the intrinsic normal space of the canonical immersion derivative. -/
theorem projectedSeedNormalEmbedding_range_normalSpace
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    normalFrameRange
        (projectedSeedNormalEmbedding normalBasis hNormalBasis
          basisData center base) =
      NormalSpace
        (projectedSeedTangentDerivative tangentBasis
          hTangentBasis basisData base) := by
  change normalFrameRange
      ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData center).frame base) =
    (tangentRange
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base))ᗮ
  calc
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
          hNormalBasis basisData center).frame base) =
      projectedSeedNormalSpan basisData center base :=
        pointwiseBasisSmoothNormalFrameFamilyOn_range normalBasis
          hNormalBasis basisData center base hValid
    _ = (tangentFrameSpan basisData base)ᗮ :=
      projectedSeedNormalSpan_eq_tangentFrameSpan_orthogonal
        basisData hDimension center base hValid
    _ = (tangentRange
        (projectedSeedTangentDerivative tangentBasis
          hTangentBasis basisData base))ᗮ := by
      exact congrArg
        (fun subspace : Submodule ℝ Ambient => subspaceᗮ)
        (projectedSeedTangentDerivative_range tangentBasis
          hTangentBasis basisData base).symm

/-- Isometric identification from the fixed normal model onto the intrinsic
normal space supplied by the canonical tangent derivative. -/
def projectedSeedNormalModelEquivNormalSpace
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    Normal ≃ₗᵢ[ℝ]
      NormalSpace
        (projectedSeedTangentDerivative tangentBasis
          hTangentBasis basisData base) :=
  (projectedSeedNormalEmbedding normalBasis hNormalBasis
      basisData center base).equivRange |>.trans
    (LinearIsometryEquiv.ofEq
      (normalFrameRange
        (projectedSeedNormalEmbedding normalBasis hNormalBasis
          basisData center base))
      (NormalSpace
        (projectedSeedTangentDerivative tangentBasis
          hTangentBasis basisData base))
      (projectedSeedNormalEmbedding_range_normalSpace tangentBasis
        hTangentBasis normalBasis hNormalBasis basisData hDimension
        center base hValid))

/-- Canonical fixed-model normal trivialization induced by the projected-seed
frame. -/
def projectedSeedNormalTrivialization
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    NormalSpace
        (projectedSeedTangentDerivative tangentBasis
          hTangentBasis basisData base) ≃ₗᵢ[ℝ] Normal :=
  (projectedSeedNormalModelEquivNormalSpace tangentBasis
    hTangentBasis normalBasis hNormalBasis basisData hDimension
    center base hValid).symm

@[simp]
theorem projectedSeedNormalTrivialization_inverse
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (normal : Normal) :
    projectedSeedNormalTrivialization tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hValid
        (projectedSeedNormalModelEquivNormalSpace tangentBasis
          hTangentBasis normalBasis hNormalBasis basisData hDimension
          center base hValid normal) =
      normal := by
  exact LinearIsometryEquiv.symm_apply_apply _ normal

section Transport

variable {NormalSource : Type z}
variable [NormedAddCommGroup NormalSource]
variable [InnerProductSpace ℝ NormalSource]
variable [FiniteDimensional ℝ NormalSource]

/-- Postcompose a continuous second fundamental form by one continuous normal
coordinate map. -/
def transportContinuousSecondFundamentalForm
    (transport : NormalSource →L[ℝ] Normal)
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := NormalSource)) :
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  (ContinuousLinearMap.compL ℝ Tangent NormalSource Normal transport).comp form

@[simp]
theorem transportContinuousSecondFundamentalForm_apply
    (transport : NormalSource →L[ℝ] Normal)
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := NormalSource))
    (first second : Tangent) :
    transportContinuousSecondFundamentalForm transport form first second =
      transport (form first second) := by
  rfl

end Transport

/-- Transport one connection-corrected geometric jet through the canonical
projected-seed normal trivialization.  The output is exactly the fixed-model
local coefficient interface used by the reduced-jet and Riesz constructions. -/
def ConnectionCorrectedActualJanusLocalJetData.toProjectedSeedActualJanusLocalJetData
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (data : ConnectionCorrectedActualJanusLocalJetData
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base)) :
    ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal) where
  tangentialQuadratic := data.sourceConnection
  normalQuadratic := transportContinuousSecondFundamentalForm
    ((projectedSeedNormalTrivialization tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension center base hValid)
        .toContinuousLinearEquiv).toContinuousLinearMap
    data.normalQuadratic
  connectionValue := data.connectionValue
  connectionDerivative := data.connectionDerivative
  physicalNormal :=
    projectedSeedNormalTrivialization tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension center base hValid
      data.physicalNormal
  tangentialQuadratic_symmetric := data.sourceConnection_symmetric
  normalQuadratic_symmetric := by
    intro first second
    rw [transportContinuousSecondFundamentalForm_apply,
      transportContinuousSecondFundamentalForm_apply]
    exact congrArg
      (projectedSeedNormalTrivialization tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hValid)
      (ConnectionCorrectedActualJanusLocalJetData.normalQuadratic_symmetric
        (projectedSeedTangentDerivative tangentBasis hTangentBasis
          basisData base) data first second)

@[simp]
theorem ConnectionCorrectedActualJanusLocalJetData.toProjectedSeed_normalQuadratic_apply
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (data : ConnectionCorrectedActualJanusLocalJetData
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base))
    (first second : Tangent) :
    (data.toProjectedSeedActualJanusLocalJetData tangentBasis
      hTangentBasis normalBasis hNormalBasis basisData hDimension
      center base hValid).normalQuadratic first second =
      projectedSeedNormalTrivialization tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hValid
        (data.normalQuadratic first second) := by
  rfl

/-- The transported coefficient is the fixed-model image of the geometric
second fundamental form obtained from the corrected jet. -/
theorem ConnectionCorrectedActualJanusLocalJetData.toProjectedSeed_normalQuadratic_eq_geometric
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (data : ConnectionCorrectedActualJanusLocalJetData
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base))
    (first second : Tangent) :
    (data.toProjectedSeedActualJanusLocalJetData tangentBasis
      hTangentBasis normalBasis hNormalBasis basisData hDimension
      center base hValid).normalQuadratic first second =
      projectedSeedNormalTrivialization tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hValid
        (P0EFTJanusSecondFundamentalFormJet.secondFundamentalForm
          (projectedSeedTangentDerivative tangentBasis
            hTangentBasis basisData base)
          data.toConnectionCorrectedSecondJet first second) := by
  rw [data.toProjectedSeed_normalQuadratic_apply tangentBasis
    hTangentBasis normalBasis hNormalBasis basisData hDimension
    center base hValid first second]
  exact congrArg
    (projectedSeedNormalTrivialization tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension center base hValid)
    (ConnectionCorrectedActualJanusLocalJetData.normalQuadratic_eq_secondFundamentalForm
      (projectedSeedTangentDerivative tangentBasis hTangentBasis
        basisData base) data first second)

@[simp]
theorem ConnectionCorrectedActualJanusLocalJetData.toProjectedSeed_reduced_curvature_apply
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (data : ConnectionCorrectedActualJanusLocalJetData
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base))
    (first second : Tangent) :
    (data.toProjectedSeedActualJanusLocalJetData tangentBasis
      hTangentBasis normalBasis hNormalBasis basisData hDimension
      center base hValid).toReducedJet.2 first second =
      data.connectionDerivative first second -
        data.connectionDerivative second first := by
  rfl

structure ProjectedSeedNormalSpaceTrivializationStatus where
  tangentDerivativeConstructed : Prop
  tangentRangeIdentified : Prop
  projectedNormalEmbeddingConstructed : Prop
  normalRangeIdentifiedWithIntrinsicNormalSpace : Prop
  fixedNormalTrivializationConstructed : Prop
  continuousSecondFundamentalTransportConstructed : Prop
  correctedJetTransportedToFixedModel : Prop
  transportedCoefficientIdentifiedWithGeometricII : Prop
  smoothFamilyTransportProved : Prop
  transitionCompatibilityProved : Prop

def projectedSeedNormalSpaceTrivializationClosed
    (s : ProjectedSeedNormalSpaceTrivializationStatus) : Prop :=
  s.tangentDerivativeConstructed ∧
  s.tangentRangeIdentified ∧
  s.projectedNormalEmbeddingConstructed ∧
  s.normalRangeIdentifiedWithIntrinsicNormalSpace ∧
  s.fixedNormalTrivializationConstructed ∧
  s.continuousSecondFundamentalTransportConstructed ∧
  s.correctedJetTransportedToFixedModel ∧
  s.transportedCoefficientIdentifiedWithGeometricII ∧
  s.smoothFamilyTransportProved ∧
  s.transitionCompatibilityProved

theorem missing_smooth_family_transport_blocks_closure
    (s : ProjectedSeedNormalSpaceTrivializationStatus)
    (hMissing : Not s.smoothFamilyTransportProved) :
    Not (projectedSeedNormalSpaceTrivializationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusProjectedSeedNormalSpaceTrivialization
end JanusFormal
