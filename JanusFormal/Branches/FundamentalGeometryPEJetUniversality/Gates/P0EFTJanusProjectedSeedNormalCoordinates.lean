import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFixedNormalTrivializationFamily
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair

namespace JanusFormal
namespace P0EFTJanusProjectedSeedNormalCoordinates

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedPhysicalRangeBridge
open P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
open P0EFTJanusFixedNormalTrivializationFamily

universe u v w x y

variable {Base : Type w} {Tangent : Type u}
variable {NormalModel : Type v} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup NormalModel] [InnerProductSpace ℝ NormalModel]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ NormalModel]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Normal coordinates induced by a projected-seed isometric normal frame.
The key specification says that synthesizing the coordinates recovers the
original vector in the varying normal space. -/
structure ProjectedSeedNormalCoordinateData
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (derivative : Base → Tangent →ₗᵢ[ℝ] Ambient)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis) where
  coordinates :
    ∀ base, NormalSpace (derivative base) ≃ₗᵢ[ℝ] NormalModel
  synthesis_spec :
    ∀ base
      (hValid : projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base)
      (normal : NormalSpace (derivative base)),
      (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData center).frame base (coordinates base normal) = normal.1

/-- The projected-seed coordinate equivalence is uniquely determined by its
synthesis equation. -/
theorem ProjectedSeedNormalCoordinateData.coordinates_unique
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (derivative : Base → Tangent →ₗᵢ[ℝ] Ambient)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (first second : ProjectedSeedNormalCoordinateData
      basisData center derivative normalBasis hNormalBasis)
    (base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    first.coordinates base = second.coordinates base := by
  apply LinearIsometryEquiv.ext
  intro normal
  apply (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
    hNormalBasis basisData center).frame base |>.injective
  rw [first.synthesis_spec base hValid normal,
    second.synthesis_spec base hValid normal]

/-- Add projected-seed provenance to an already transported fixed-normal family. -/
structure ProjectedSeedFixedNormalFamilyData
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis) where
  fixedFamily : FixedNormalTrivializedActualJetFamilyData
    (Base := Base) (Tangent := Tangent)
    (Ambient := Ambient) (Normal := NormalModel)
  coordinates : ProjectedSeedNormalCoordinateData
    basisData center fixedFamily.derivative normalBasis hNormalBasis
  trivialization_eq :
    ∀ base,
      fixedFamily.normalTrivialization base = coordinates.coordinates base

/-- The projected-seed family reduces to the fixed-normal family already
connected to smooth reduced jets. -/
def ProjectedSeedFixedNormalFamilyData.toFixedNormalFamily
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (data : ProjectedSeedFixedNormalFamilyData
      basisData center normalBasis hNormalBasis) :
    FixedNormalTrivializedActualJetFamilyData
      (Base := Base) (Tangent := Tangent)
      (Ambient := Ambient) (Normal := NormalModel) :=
  data.fixedFamily

theorem ProjectedSeedFixedNormalFamilyData.reducedJet_contDiff
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (data : ProjectedSeedFixedNormalFamilyData
      basisData center normalBasis hNormalBasis) :
    ContDiff ℝ ∞
      data.toFixedNormalFamily.toActualJanusLocalJetFamilyData.reducedJet :=
  data.toFixedNormalFamily.reducedJet_contDiff

/-- Exact remaining boundary: construct the coordinate equivalence itself from
the projected-seed frame and the theorem identifying its range with the true
normal space. -/
structure ProjectedSeedNormalCoordinatesStatus where
  projectedSeedNormalFrameAvailable : Prop
  frameRangeEqualsNormalSpace : Prop
  coordinateEquivalenceConstructed : Prop
  synthesisSpecificationProved : Prop
  uniquenessProved : Prop
  fixedNormalFamilyConnected : Prop
  reducedJetSmoothnessInherited : Prop


def projectedSeedNormalCoordinatesClosed
    (s : ProjectedSeedNormalCoordinatesStatus) : Prop :=
  s.projectedSeedNormalFrameAvailable ∧
  s.frameRangeEqualsNormalSpace ∧
  s.coordinateEquivalenceConstructed ∧
  s.synthesisSpecificationProved ∧
  s.uniquenessProved ∧
  s.fixedNormalFamilyConnected ∧
  s.reducedJetSmoothnessInherited


theorem missing_coordinate_equivalence_blocks_closure
    (s : ProjectedSeedNormalCoordinatesStatus)
    (hMissing : Not s.coordinateEquivalenceConstructed) :
    Not (projectedSeedNormalCoordinatesClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

end

end P0EFTJanusProjectedSeedNormalCoordinates
end JanusFormal
