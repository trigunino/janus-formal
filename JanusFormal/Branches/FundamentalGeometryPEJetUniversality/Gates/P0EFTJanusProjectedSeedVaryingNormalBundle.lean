import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFixedNormalTrivializationFamily
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedNormalSpaceTrivialization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedNormalCoefficientOverlap
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedNormalRangeTransition

namespace JanusFormal
namespace P0EFTJanusProjectedSeedVaryingNormalBundle

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorOpenCanonicalTransition
open P0EFTJanusRieszShapeOperatorOpenMovingFrame
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedNormalRangeTransition
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusFixedNormalTrivializationFamily
open P0EFTJanusProjectedSeedNormalSpaceTrivialization
open P0EFTJanusProjectedSeedNormalCoefficientOverlap

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

/-- The projected-seed coordinate map really synthesizes the intrinsic normal
vector through its chart frame. -/
@[simp]
theorem projectedSeedNormalTrivialization_synthesis
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (normal : NormalSpace
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base)) :
    projectedSeedNormalEmbedding normalBasis hNormalBasis basisData center base
        (projectedSeedNormalTrivialization tangentBasis hTangentBasis
          normalBasis hNormalBasis basisData hDimension center base hValid normal) =
      normal.1 := by
  let equivalence := projectedSeedNormalModelEquivNormalSpace tangentBasis
    hTangentBasis normalBasis hNormalBasis basisData hDimension center base hValid
  have hInverse : equivalence (equivalence.symm normal) = normal :=
    equivalence.apply_symm_apply normal
  exact congrArg Subtype.val hInverse

/-- Smooth normal-coordinate change between two projected-seed charts. -/
def projectedSeedNormalTransitionOnOverlap
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (first second : Base) :
    SmoothOrthogonalFrameFamilyOn Base Normal
      (pointwiseBasisOverlapDomain basisData first second) := by
  let firstFrame : SmoothIsometricFrameFamilyOn Base Normal Ambient
      (pointwiseBasisOverlapDomain basisData first second) :=
    restrictSmoothIsometricFrameFamilyOn
      (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData first) (by
        intro base hBase
        exact hBase.1)
  let secondFrame : SmoothIsometricFrameFamilyOn Base Normal Ambient
      (pointwiseBasisOverlapDomain basisData first second) :=
    restrictSmoothIsometricFrameFamilyOn
      (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData second) (by
        intro base hBase
        exact hBase.2)
  exact openCanonicalFrameTransition firstFrame secondFrame (by
    intro base hBase
    simpa [firstFrame, secondFrame, restrictSmoothIsometricFrameFamilyOn] using
      projectedSeedNormalFrames_sameRange normalBasis hNormalBasis
        basisData hDimension first second base hBase.1 hBase.2)

/-- The smooth overlap transition intertwines the two ambient normal frames. -/
theorem projectedSeedNormalTransitionOnOverlap_spec
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (first second base : Base)
    (hBase : base ∈ pointwiseBasisOverlapDomain basisData first second)
    (normal : Normal) :
    projectedSeedNormalEmbedding normalBasis hNormalBasis basisData first base
        ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
          basisData hDimension first second).frame base normal) =
      projectedSeedNormalEmbedding normalBasis hNormalBasis basisData second base
        normal := by
  let firstFrame : SmoothIsometricFrameFamilyOn Base Normal Ambient
      (pointwiseBasisOverlapDomain basisData first second) :=
    restrictSmoothIsometricFrameFamilyOn
      (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData first) (by
        intro point hPoint
        exact hPoint.1)
  let secondFrame : SmoothIsometricFrameFamilyOn Base Normal Ambient
      (pointwiseBasisOverlapDomain basisData first second) :=
    restrictSmoothIsometricFrameFamilyOn
      (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData second) (by
        intro point hPoint
        exact hPoint.2)
  exact openCanonicalFrameTransition_spec firstFrame secondFrame (by
    intro point hPoint
    simpa [firstFrame, secondFrame, restrictSmoothIsometricFrameFamilyOn] using
      projectedSeedNormalFrames_sameRange normalBasis hNormalBasis
        basisData hDimension first second point hPoint.1 hPoint.2)
    base hBase normal

/-- The canonical intrinsic normal trivializations change by exactly the
smooth projected-seed overlap transition. -/
theorem projectedSeedNormalTrivialization_transition
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (first second base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) first base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) second base)
    (normal : NormalSpace
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base)) :
    projectedSeedNormalTrivialization tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension first base hFirst normal =
      (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
        basisData hDimension first second).frame base
        (projectedSeedNormalTrivialization tangentBasis hTangentBasis normalBasis
          hNormalBasis basisData hDimension second base hSecond normal) := by
  apply (projectedSeedNormalEmbedding normalBasis hNormalBasis
    basisData first base).injective
  rw [projectedSeedNormalTrivialization_synthesis tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension first base hFirst normal]
  rw [projectedSeedNormalTransitionOnOverlap_spec normalBasis hNormalBasis
    basisData hDimension first second base ⟨hFirst, hSecond⟩]
  exact (projectedSeedNormalTrivialization_synthesis tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension second base hSecond normal).symm

/-- Concrete atlas data for the varying family of intrinsic normal spaces. -/
structure ProjectedSeedVaryingNormalBundleFamily
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) where
  trivialization :
    ∀ center base,
      projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center base →
        NormalSpace (projectedSeedTangentDerivative tangentBasis
          hTangentBasis basisData base) ≃ₗᵢ[ℝ] Normal
  transitionOnOverlap :
    ∀ first second,
      SmoothOrthogonalFrameFamilyOn Base Normal
        (pointwiseBasisOverlapDomain basisData first second)
  center_mem_domain :
    ∀ center, projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center center
  trivialization_change :
    ∀ first second base hFirst hSecond normal,
      trivialization first base hFirst normal =
        (transitionOnOverlap first second).frame base
          (trivialization second base hSecond normal)

/-- The projected-seed atlas constructs the varying normal bundle family, with
smooth transition maps and no extra choice of frames. -/
def projectedSeedVaryingNormalBundleFamily
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    ProjectedSeedVaryingNormalBundleFamily tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension where
  trivialization := fun center base hValid =>
    projectedSeedNormalTrivialization tangentBasis hTangentBasis normalBasis
      hNormalBasis basisData hDimension center base hValid
  transitionOnOverlap := fun first second =>
    projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
      basisData hDimension first second
  center_mem_domain := pointwiseNormalSeedChart_valid_at_center basisData
  trivialization_change := by
    intro first second base hFirst hSecond normal
    exact projectedSeedNormalTrivialization_transition tangentBasis
      hTangentBasis normalBasis hNormalBasis basisData hDimension
      first second base hFirst hSecond normal

/-- Transported second-fundamental coefficients obey the same overlap law as
the normal-bundle trivializations. -/
theorem projectedSeedActualJanusLocalJetData_normalQuadratic_transition
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (first second base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) first base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) second base)
    (data : ConnectionCorrectedActualJanusLocalJetData
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base))
    (x y : Tangent) :
    (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension first base hFirst data).normalQuadratic
        x y =
      (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
        basisData hDimension first second).frame base
        ((projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
          normalBasis hNormalBasis basisData hDimension second base hSecond data).normalQuadratic
          x y) := by
  rw [projectedSeedActualJanusLocalJetData_normalQuadratic_apply,
    projectedSeedActualJanusLocalJetData_normalQuadratic_apply]
  exact projectedSeedNormalTrivialization_transition tangentBasis
    hTangentBasis normalBasis hNormalBasis basisData hDimension
    first second base hFirst hSecond (data.normalQuadratic x y)

/-- Transported physical normals obey the projected-seed overlap law. -/
theorem projectedSeedActualJanusLocalJetData_physicalNormal_transition
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (first second base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) first base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) second base)
    (data : ConnectionCorrectedActualJanusLocalJetData
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base)) :
    (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension first base hFirst data).physicalNormal =
      (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
        basisData hDimension first second).frame base
        ((projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
          normalBasis hNormalBasis basisData hDimension second base hSecond data).physicalNormal) := by
  exact projectedSeedNormalTrivialization_transition tangentBasis
    hTangentBasis normalBasis hNormalBasis basisData hDimension
    first second base hFirst hSecond data.physicalNormal

/-- A globally valid projected-seed chart plus smooth transported coefficients
instantiates the fixed-normal family interface used by the Riesz pipeline. -/
def fixedNormalFamilyOfProjectedSeedChart
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center : Base)
    (hValid : ∀ base, projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (correctedJet : ∀ base, ConnectionCorrectedActualJanusLocalJetData
      (projectedSeedTangentDerivative tangentBasis
        hTangentBasis basisData base))
    (hTangential : ContDiff ℝ ∞
      (fun base => (correctedJet base).sourceConnection))
    (hNormalQuadratic : ContDiff ℝ ∞
      (fun base =>
        (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
          normalBasis hNormalBasis basisData hDimension center base
          (hValid base) (correctedJet base)).normalQuadratic))
    (hConnectionValue : ContDiff ℝ ∞
      (fun base => (correctedJet base).connectionValue))
    (hConnectionDerivative : ContDiff ℝ ∞
      (fun base => (correctedJet base).connectionDerivative))
    (hPhysicalNormal : ContDiff ℝ ∞
      (fun base =>
        (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
          normalBasis hNormalBasis basisData hDimension center base
          (hValid base) (correctedJet base)).physicalNormal)) :
    FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := Normal) where
  derivative := projectedSeedTangentDerivative tangentBasis
    hTangentBasis basisData
  correctedJet := correctedJet
  normalTrivialization := fun base =>
    projectedSeedNormalTrivialization tangentBasis hTangentBasis normalBasis
      hNormalBasis basisData hDimension center base (hValid base)
  tangentialQuadratic := fun base => (correctedJet base).sourceConnection
  normalQuadratic := fun base =>
    (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension center base
      (hValid base) (correctedJet base)).normalQuadratic
  connectionValue := fun base => (correctedJet base).connectionValue
  connectionDerivative := fun base => (correctedJet base).connectionDerivative
  physicalNormal := fun base =>
    (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension center base
      (hValid base) (correctedJet base)).physicalNormal
  tangentialQuadratic_apply := fun _ => rfl
  normalQuadratic_apply := by
    intro base first second
    exact projectedSeedActualJanusLocalJetData_normalQuadratic_apply
      tangentBasis hTangentBasis normalBasis hNormalBasis basisData hDimension
      center base (hValid base) (correctedJet base) first second
  connectionValue_apply := fun _ => rfl
  connectionDerivative_apply := fun _ => rfl
  physicalNormal_apply := fun _ => rfl
  tangentialQuadratic_contDiff := hTangential
  normalQuadratic_contDiff := hNormalQuadratic
  connectionValue_contDiff := hConnectionValue
  connectionDerivative_contDiff := hConnectionDerivative
  physicalNormal_contDiff := hPhysicalNormal

end

end P0EFTJanusProjectedSeedVaryingNormalBundle
end JanusFormal
