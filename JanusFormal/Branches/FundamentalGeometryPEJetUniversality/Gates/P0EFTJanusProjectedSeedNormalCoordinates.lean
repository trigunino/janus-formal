import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFixedNormalTrivializationFamily
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedOrthogonalRange

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
open P0EFTJanusRieszShapeOperatorProjectedSeedOrthogonalRange
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

/-- Canonical coordinates on a normal subspace from an isometric frame whose
ambient range is exactly that subspace. -/
def normalCoordinatesOfFrameRange
    (frame : NormalModel →ₗᵢ[ℝ] Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange frame = NormalSpace derivative) :
    NormalSpace derivative ≃ₗᵢ[ℝ] NormalModel :=
  (LinearIsometryEquiv.ofEq
      (NormalSpace derivative) (normalFrameRange frame) hRange.symm).trans
    frame.equivRange.symm

/-- Synthesizing the canonical coordinates recovers the original normal vector. -/
@[simp]
theorem normalCoordinatesOfFrameRange_spec
    (frame : NormalModel →ₗᵢ[ℝ] Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange frame = NormalSpace derivative)
    (normal : NormalSpace derivative) :
    frame (normalCoordinatesOfFrameRange frame derivative hRange normal) =
      normal.1 := by
  let pointInRange : normalFrameRange frame :=
    LinearIsometryEquiv.ofEq
      (NormalSpace derivative) (normalFrameRange frame) hRange.symm normal
  have hInverse :
      frame.equivRange (frame.equivRange.symm pointInRange) = pointInRange :=
    frame.equivRange.apply_symm_apply pointInRange
  change frame (frame.equivRange.symm pointInRange) = normal.1
  calc
    frame (frame.equivRange.symm pointInRange) =
        (pointInRange : Ambient) := by
      exact congrArg Subtype.val hInverse
    _ = normal.1 := by
      rfl

/-- The synthesis equation characterizes the canonical coordinate equivalence. -/
theorem normalCoordinatesOfFrameRange_unique
    (frame : NormalModel →ₗᵢ[ℝ] Ambient)
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (hRange : normalFrameRange frame = NormalSpace derivative)
    (candidate : NormalSpace derivative ≃ₗᵢ[ℝ] NormalModel)
    (hCandidate : ∀ normal, frame (candidate normal) = normal.1) :
    candidate = normalCoordinatesOfFrameRange frame derivative hRange := by
  apply LinearIsometryEquiv.ext
  intro normal
  apply frame.injective
  rw [hCandidate normal,
    normalCoordinatesOfFrameRange_spec frame derivative hRange normal]

/-- The projected-seed frame range is the intrinsic normal space as soon as its
tangent span is identified with the range of the immersion derivative. -/
theorem projectedSeedFrame_range_eq_normalSpace
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center : Base)
    (derivative : Base → Tangent →ₗᵢ[ℝ] Ambient)
    (base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (hTangentRange : tangentFrameSpan basisData base =
      tangentRange (derivative base)) :
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
          hNormalBasis basisData center).frame base) =
      NormalSpace (derivative base) := by
  calc
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
          hNormalBasis basisData center).frame base) =
        projectedSeedNormalSpan basisData center base :=
      pointwiseBasisSmoothNormalFrameFamilyOn_range
        normalBasis hNormalBasis basisData center base hValid
    _ = (tangentFrameSpan basisData base)ᗮ :=
      projectedSeedNormalSpan_eq_tangentFrameSpan_orthogonal
        basisData hDimension center base hValid
    _ = NormalSpace (derivative base) :=
      congrArg (fun subspace : Submodule ℝ Ambient => subspaceᗮ)
        hTangentRange

/-- Canonical projected-seed coordinates at one valid chart point. -/
def projectedSeedNormalCoordinatesAt
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center : Base)
    (derivative : Base → Tangent →ₗᵢ[ℝ] Ambient)
    (base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (hTangentRange : tangentFrameSpan basisData base =
      tangentRange (derivative base)) :
    NormalSpace (derivative base) ≃ₗᵢ[ℝ] NormalModel :=
  normalCoordinatesOfFrameRange
    ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData center).frame base)
    (derivative base)
    (projectedSeedFrame_range_eq_normalSpace normalBasis hNormalBasis
      basisData hDimension center derivative base hValid hTangentRange)

/-- The projected-seed coordinates satisfy the expected frame synthesis law. -/
@[simp]
theorem projectedSeedNormalCoordinatesAt_spec
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center : Base)
    (derivative : Base → Tangent →ₗᵢ[ℝ] Ambient)
    (base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (hTangentRange : tangentFrameSpan basisData base =
      tangentRange (derivative base))
    (normal : NormalSpace (derivative base)) :
    (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData center).frame base
        (projectedSeedNormalCoordinatesAt normalBasis hNormalBasis basisData
          hDimension center derivative base hValid hTangentRange normal) =
      normal.1 := by
  exact normalCoordinatesOfFrameRange_spec
    ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData center).frame base)
    (derivative base)
    (projectedSeedFrame_range_eq_normalSpace normalBasis hNormalBasis
      basisData hDimension center derivative base hValid hTangentRange)
    normal

/-- Normal coordinates induced by a projected-seed isometric normal frame on
its valid chart domain. -/
structure ProjectedSeedNormalCoordinateData
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (derivative : Base → Tangent →ₗᵢ[ℝ] Ambient)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis) where
  coordinates :
    ∀ base,
      projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center base →
        NormalSpace (derivative base) ≃ₗᵢ[ℝ] NormalModel
  synthesis_spec :
    ∀ base
      (hValid : projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base)
      (normal : NormalSpace (derivative base)),
      (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
        hNormalBasis basisData center).frame base
          (coordinates base hValid normal) = normal.1

/-- Construct the complete local coordinate family from the tangent-range
identification and the ambient dimension identity. -/
def projectedSeedNormalCoordinateDataOfTangentRange
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center : Base)
    (derivative : Base → Tangent →ₗᵢ[ℝ] Ambient)
    (hTangentRange :
      ∀ base,
        projectedSeedChartValid basisData.tangentFrame
            (pointwiseNormalSeedCharts basisData) center base →
          tangentFrameSpan basisData base = tangentRange (derivative base)) :
    ProjectedSeedNormalCoordinateData
      basisData center derivative normalBasis hNormalBasis where
  coordinates := by
    intro base hValid
    exact projectedSeedNormalCoordinatesAt normalBasis hNormalBasis basisData
      hDimension center derivative base hValid (hTangentRange base hValid)
  synthesis_spec := by
    intro base hValid normal
    exact projectedSeedNormalCoordinatesAt_spec normalBasis hNormalBasis
      basisData hDimension center derivative base hValid
      (hTangentRange base hValid) normal

/-- The projected-seed coordinate equivalence is uniquely determined by its
synthesis equation at every valid chart point. -/
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
    first.coordinates base hValid = second.coordinates base hValid := by
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
    ∀ base
      (hValid : projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base),
      fixedFamily.normalTrivialization base = coordinates.coordinates base hValid

/-- The projected-seed family reduces to the fixed-normal family already
connected to smooth reduced jets. -/
def ProjectedSeedFixedNormalFamilyData.toFixedNormalFamily
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (data : ProjectedSeedFixedNormalFamilyData
      (Tangent := Tangent) (NormalModel := NormalModel) (Ambient := Ambient)
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
      (Tangent := Tangent) (NormalModel := NormalModel) (Ambient := Ambient)
      basisData center normalBasis hNormalBasis) :
    ContDiff ℝ ∞
      data.toFixedNormalFamily.toActualJanusLocalJetFamilyData.reducedJet :=
  data.toFixedNormalFamily.reducedJet_contDiff

/-- Status after constructing projected-seed coordinates from tangent-range
identification. -/
structure ProjectedSeedNormalCoordinatesStatus where
  projectedSeedNormalFrameAvailable : Prop
  frameRangeEqualsNormalSpace : Prop
  coordinateEquivalenceConstructed : Prop
  synthesisSpecificationProved : Prop
  uniquenessProved : Prop
  fixedNormalFamilyConnected : Prop
  reducedJetSmoothnessInherited : Prop
  tangentRangeIdentifiedWithImmersionDerivative : Prop


def projectedSeedNormalCoordinatesClosed
    (s : ProjectedSeedNormalCoordinatesStatus) : Prop :=
  s.projectedSeedNormalFrameAvailable ∧
  s.frameRangeEqualsNormalSpace ∧
  s.coordinateEquivalenceConstructed ∧
  s.synthesisSpecificationProved ∧
  s.uniquenessProved ∧
  s.fixedNormalFamilyConnected ∧
  s.reducedJetSmoothnessInherited ∧
  s.tangentRangeIdentifiedWithImmersionDerivative


theorem missing_tangent_range_identification_blocks_closure
    (s : ProjectedSeedNormalCoordinatesStatus)
    (hMissing : Not s.tangentRangeIdentifiedWithImmersionDerivative) :
    Not (projectedSeedNormalCoordinatesClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2

end

end P0EFTJanusProjectedSeedNormalCoordinates
end JanusFormal
