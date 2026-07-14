import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedNormalRangeTransition

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorOpenCanonicalTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness

universe u v w x

variable {Base : Type w} {Model : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Model]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type x}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Physical normal subspace determined by orthogonality to every vector of the
supplied tangent frame. -/
def tangentFrameNormalSubspace
    (tangentFrame : ι → Base → Ambient) (base : Base) :
    Submodule ℝ Ambient :=
  ⨅ i, (ℝ ∙ tangentFrame i base)ᗮ

/-- Every projected-seed Gram--Schmidt normal vector belongs to the physical
normal subspace. -/
theorem projectedSeedNormalFrame_mem_tangentFrameNormalSubspace
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base) (k : κ) :
    projectedSeedNormalFrame basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center k base ∈
      tangentFrameNormalSubspace basisData.tangentFrame base := by
  simp only [tangentFrameNormalSubspace, Submodule.mem_iInf]
  intro i
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact tangent_inner_projectedSeedNormalFrame_eq_zero
    basisData.tangentFrame (pointwiseNormalSeedCharts basisData)
    basisData.tangent_orthonormal center base i k

/-- The ambient range of the packaged Gram--Schmidt frame is contained in the
physical normal subspace. -/
theorem pointwiseBasisSmoothNormalFrameFamilyOn_range_le
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
          hCoordinateOrthonormal basisData center).frame base) ≤
      tangentFrameNormalSubspace basisData.tangentFrame base := by
  rw [pointwiseBasisSmoothNormalFrameFamilyOn_range
    coordinateBasis hCoordinateOrthonormal basisData center base hValid]
  apply Submodule.span_le.2
  rintro vector ⟨k, rfl⟩
  exact projectedSeedNormalFrame_mem_tangentFrameNormalSubspace
    basisData center base k

/-- In constant normal rank, containment plus dimension equality identifies the
packaged Gram--Schmidt frame range with the full physical normal subspace. -/
theorem pointwiseBasisSmoothNormalFrameFamilyOn_range_eq
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hNormalRank : ∀ base,
      Module.finrank ℝ Model =
        Module.finrank ℝ (tangentFrameNormalSubspace
          basisData.tangentFrame base))
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
          hCoordinateOrthonormal basisData center).frame base) =
      tangentFrameNormalSubspace basisData.tangentFrame base := by
  let frame := pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
    hCoordinateOrthonormal basisData center
  apply Submodule.eq_of_le_of_finrank_eq
  · exact pointwiseBasisSmoothNormalFrameFamilyOn_range_le
      coordinateBasis hCoordinateOrthonormal basisData center base hValid
  · have hEquiv : Model ≃ₗ[ℝ]
        normalFrameRange (frame.frame base) :=
      (frame.frame base).equivRange.toLinearEquiv
    exact (LinearEquiv.finrank_eq hEquiv).symm.trans (hNormalRank base)

/-- Restrict an open-domain smooth isometric frame family to a smaller domain. -/
def SmoothIsometricFrameFamilyOn.restrict
    {domain restricted : Set Base}
    (family : SmoothIsometricFrameFamilyOn Base Model Ambient domain)
    (hSubset : restricted ⊆ domain) :
    SmoothIsometricFrameFamilyOn Base Model Ambient restricted where
  frame := family.frame
  forward_contDiffOn := family.forward_contDiffOn.mono hSubset

/-- Intersection of two pointwise-basis projected-seed chart domains. -/
def pointwiseBasisOverlapDomain
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (first second : Base) : Set Base :=
  {base | projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) first base} ∩
    {base | projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) second base}

/-- Canonical smooth orthogonal transition between two pointwise-basis
Gram--Schmidt normal frames on their overlap. -/
def pointwiseBasisNormalTransitionOnOverlap
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hNormalRank : ∀ base,
      Module.finrank ℝ Model =
        Module.finrank ℝ (tangentFrameNormalSubspace
          basisData.tangentFrame base))
    (first second : Base) :
    P0EFTJanusRieszShapeOperatorOpenMovingFrame.SmoothOrthogonalFrameFamilyOn
      Base Model (pointwiseBasisOverlapDomain basisData first second) := by
  let firstFrame : SmoothIsometricFrameFamilyOn
      Base Model Ambient (pointwiseBasisOverlapDomain basisData first second) :=
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData first).restrict
        (by
          intro base hBase
          exact hBase.1)
  let secondFrame : SmoothIsometricFrameFamilyOn
      Base Model Ambient (pointwiseBasisOverlapDomain basisData first second) :=
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData second).restrict
        (by
          intro base hBase
          exact hBase.2)
  apply openCanonicalFrameTransition firstFrame secondFrame
  intro base hBase
  exact
    (pointwiseBasisSmoothNormalFrameFamilyOn_range_eq
      coordinateBasis hCoordinateOrthonormal basisData hNormalRank
      first base hBase.1).trans
    (pointwiseBasisSmoothNormalFrameFamilyOn_range_eq
      coordinateBasis hCoordinateOrthonormal basisData hNormalRank
      second base hBase.2).symm

/-- The canonical overlap transition has the expected physical-frame
intertwining law. -/
theorem pointwiseBasisNormalTransitionOnOverlap_spec
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hNormalRank : ∀ base,
      Module.finrank ℝ Model =
        Module.finrank ℝ (tangentFrameNormalSubspace
          basisData.tangentFrame base))
    (first second base : Base)
    (hBase : base ∈ pointwiseBasisOverlapDomain basisData first second)
    (normal : Model) :
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData first).frame base
        ((pointwiseBasisNormalTransitionOnOverlap coordinateBasis
          hCoordinateOrthonormal basisData hNormalRank first second).frame
          base normal) =
      (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
        hCoordinateOrthonormal basisData second).frame base normal := by
  let firstFrame : SmoothIsometricFrameFamilyOn
      Base Model Ambient (pointwiseBasisOverlapDomain basisData first second) :=
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData first).restrict
        (by
          intro point hPoint
          exact hPoint.1)
  let secondFrame : SmoothIsometricFrameFamilyOn
      Base Model Ambient (pointwiseBasisOverlapDomain basisData first second) :=
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData second).restrict
        (by
          intro point hPoint
          exact hPoint.2)
  change firstFrame.frame base
      ((pointwiseBasisNormalTransitionOnOverlap coordinateBasis
        hCoordinateOrthonormal basisData hNormalRank first second).frame
        base normal) =
    secondFrame.frame base normal
  exact openCanonicalFrameTransition_spec firstFrame secondFrame
    (by
      intro point hPoint
      exact
        (pointwiseBasisSmoothNormalFrameFamilyOn_range_eq
          coordinateBasis hCoordinateOrthonormal basisData hNormalRank
          first point hPoint.1).trans
        (pointwiseBasisSmoothNormalFrameFamilyOn_range_eq
          coordinateBasis hCoordinateOrthonormal basisData hNormalRank
          second point hPoint.2).symm)
    base hBase normal

/-- Exact closure status after normal-range identification and overlap
transition construction. -/
structure ProjectedSeedNormalRangeTransitionStatus where
  physicalNormalSubspaceDefined : Prop
  gramSchmidtVectorsNormal : Prop
  packagedFrameRangeContained : Prop
  constantRankRangeEqualityProved : Prop
  openDomainRestrictionConstructed : Prop
  overlapTransitionConstructed : Prop
  overlapIntertwiningLawProved : Prop
  tangentTransitionConnected : Prop
  localRieszOverlapConnected : Prop

/-- Closure of projected-seed normal-range transitions. -/
def projectedSeedNormalRangeTransitionClosed
    (s : ProjectedSeedNormalRangeTransitionStatus) : Prop :=
  s.physicalNormalSubspaceDefined ∧
  s.gramSchmidtVectorsNormal ∧
  s.packagedFrameRangeContained ∧
  s.constantRankRangeEqualityProved ∧
  s.openDomainRestrictionConstructed ∧
  s.overlapTransitionConstructed ∧
  s.overlapIntertwiningLawProved ∧
  s.tangentTransitionConnected ∧
  s.localRieszOverlapConnected

/-- The remaining bridge is the tangent component and its insertion into the
Riesz overlap package. -/
theorem missing_tangent_bridge_blocks_full_overlap_connection
    (s : ProjectedSeedNormalRangeTransitionStatus)
    (hMissing : Not s.tangentTransitionConnected) :
    Not (projectedSeedNormalRangeTransitionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusRieszShapeOperatorProjectedSeedNormalRangeTransition
end JanusFormal
