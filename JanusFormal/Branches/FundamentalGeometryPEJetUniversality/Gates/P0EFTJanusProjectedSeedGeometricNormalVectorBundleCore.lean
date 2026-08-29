import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedVaryingNormalBundle

namespace JanusFormal
namespace P0EFTJanusProjectedSeedGeometricNormalVectorBundleCore

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace Manifold
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedNormalRangeTransition
open P0EFTJanusProjectedSeedNormalSpaceTrivialization
open P0EFTJanusProjectedSeedVaryingNormalBundle

universe uBase uNormal uAmbient uIndex

variable {Base : Type uBase}
variable {Normal : Type uNormal} {Ambient : Type uAmbient}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type uIndex}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Open domain of the projected-seed normal chart centred at `center`. -/
def projectedSeedGeometricNormalDomain
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) : Set Base :=
  {base | projectedSeedChartValid basisData.tangentFrame
    (pointwiseNormalSeedCharts basisData) center base}

/-- Coordinate transport from the chart `first` to the chart `second`.
The projected-seed transition is written in the opposite frame convention, so
its arguments are reversed here. -/
def projectedSeedGeometricNormalCoordChange
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (first second base : Base) : Normal →L[ℝ] Normal :=
  (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
      basisData hDimension second first).frame base
    |>.toContinuousLinearEquiv.toContinuousLinearMap

/-- The intrinsic projected-seed normal bundle as an actual vector-bundle
core.  Its chart cover, fiber maps, identity law and cocycle all come from the
geometric normal frames. -/
def projectedSeedGeometricNormalCore
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    VectorBundleCore ℝ Base Normal Base where
  baseSet := projectedSeedGeometricNormalDomain basisData
  isOpen_baseSet center :=
    projectedSeedChartValid_isOpen basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) basisData.tangent_contDiff center
  indexAt base := base
  mem_baseSet_at base :=
    pointwiseNormalSeedChart_valid_at_center basisData base
  coordChange := projectedSeedGeometricNormalCoordChange normalBasis
    hNormalBasis basisData hDimension
  coordChange_self chart base hBase vector := by
    apply (projectedSeedNormalEmbedding normalBasis hNormalBasis
      basisData chart base).injective
    change
      projectedSeedNormalEmbedding normalBasis hNormalBasis basisData chart base
          ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
            basisData hDimension chart chart).frame base vector) =
        projectedSeedNormalEmbedding normalBasis hNormalBasis basisData chart base
          vector
    exact projectedSeedNormalTransitionOnOverlap_spec normalBasis hNormalBasis
      basisData hDimension chart chart base ⟨hBase, hBase⟩ vector
  continuousOn_coordChange first second := by
    rw [show
      projectedSeedGeometricNormalDomain basisData first ∩
          projectedSeedGeometricNormalDomain basisData second =
        pointwiseBasisOverlapDomain basisData second first by
      simp only [projectedSeedGeometricNormalDomain,
        pointwiseBasisOverlapDomain, inter_comm]]
    have hContinuous :=
      (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
        basisData hDimension second first).forward_contDiffOn.continuousOn
    apply hContinuous.congr
    intro base hBase
    rfl
  coordChange_comp first second third base hBase vector := by
    apply (projectedSeedNormalEmbedding normalBasis hNormalBasis
      basisData third base).injective
    change
      projectedSeedNormalEmbedding normalBasis hNormalBasis basisData third base
          ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
            basisData hDimension third second).frame base
            ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
              basisData hDimension second first).frame base vector)) =
        projectedSeedNormalEmbedding normalBasis hNormalBasis basisData third base
          ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
            basisData hDimension third first).frame base vector)
    calc
      projectedSeedNormalEmbedding normalBasis hNormalBasis basisData third base
          ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
            basisData hDimension third second).frame base
            ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
              basisData hDimension second first).frame base vector)) =
        projectedSeedNormalEmbedding normalBasis hNormalBasis basisData second base
          ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
            basisData hDimension second first).frame base vector) :=
        projectedSeedNormalTransitionOnOverlap_spec normalBasis hNormalBasis
          basisData hDimension third second base ⟨hBase.2, hBase.1.2⟩ _
      _ = projectedSeedNormalEmbedding normalBasis hNormalBasis basisData first base
          vector :=
        projectedSeedNormalTransitionOnOverlap_spec normalBasis hNormalBasis
          basisData hDimension second first base ⟨hBase.1.2, hBase.1.1⟩ vector
      _ = projectedSeedNormalEmbedding normalBasis hNormalBasis basisData third base
          ((projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
            basisData hDimension third first).frame base vector) :=
        (projectedSeedNormalTransitionOnOverlap_spec normalBasis hNormalBasis
          basisData hDimension third first base ⟨hBase.2, hBase.1.1⟩ vector).symm

/-- Smoothness of the geometric normal core is exactly the already proved
smoothness of the projected-seed overlap transitions. -/
theorem projectedSeedGeometricNormalCore_isContMDiff
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    (projectedSeedGeometricNormalCore normalBasis hNormalBasis
      basisData hDimension).IsContMDiff 𝓘(ℝ, Base) ∞ := by
  constructor
  intro first second
  change ContMDiffOn 𝓘(ℝ, Base) 𝓘(ℝ, Normal →L[ℝ] Normal) ∞
    (projectedSeedGeometricNormalCoordChange normalBasis hNormalBasis
      basisData hDimension first second)
    (projectedSeedGeometricNormalDomain basisData first ∩
      projectedSeedGeometricNormalDomain basisData second)
  rw [show
    projectedSeedGeometricNormalDomain basisData first ∩
        projectedSeedGeometricNormalDomain basisData second =
      pointwiseBasisOverlapDomain basisData second first by
    simp only [projectedSeedGeometricNormalDomain,
      pointwiseBasisOverlapDomain, inter_comm]]
  have hSmooth :=
    (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
      basisData hDimension second first).forward_contDiffOn.contMDiffOn
  apply hSmooth.congr
  intro base hBase
  rfl

/-- The preferred chart at each base point is the point-centred geometric
normal chart. -/
@[simp]
theorem projectedSeedGeometricNormalCore_indexAt
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (base : Base) :
    (projectedSeedGeometricNormalCore normalBasis hNormalBasis
      basisData hDimension).indexAt base = base :=
  rfl

end

end P0EFTJanusProjectedSeedGeometricNormalVectorBundleCore
end JanusFormal
