import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenCanonicalTransition

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedPhysicalRangeBridge

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
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- A smooth physical normal frame on one projected-seed chart, together with
an exact identification of its ambient range. -/
structure PhysicalNormalFrameOn
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) where
  frame : SmoothIsometricFrameFamilyOn Base Model Ambient
    {base | projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base}
  physicalRange : Base → Submodule ℝ Ambient
  frame_range_eq :
    ∀ base,
      projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base →
      normalFrameRange (frame.frame base) = physicalRange base

/-- Exact geometric obligation required to identify the projected-seed
Gram--Schmidt frame with the physical normal bundle on a chart. -/
structure ProjectedSeedPhysicalRangeIdentification
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (physical : PhysicalNormalFrameOn
      (Model := Model) basisData center) where
  projected_range_eq :
    ∀ base,
      projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base →
      Submodule.span ℝ
        (Set.range (fun k => projectedSeedNormalFrame
          basisData.tangentFrame (pointwiseNormalSeedCharts basisData)
          center k base)) = physical.physicalRange base

/-- The packaged projected-seed frame has the same ambient range as the physical
normal frame on every valid point of the chart. -/
theorem projectedSeedFrame_range_eq_physicalFrame
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (physical : PhysicalNormalFrameOn
      (Model := Model) basisData center)
    (identification : ProjectedSeedPhysicalRangeIdentification
      coordinateBasis hCoordinateOrthonormal basisData center physical)
    (base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
          hCoordinateOrthonormal basisData center).frame base) =
      normalFrameRange (physical.frame.frame base) := by
  rw [pointwiseBasisSmoothNormalFrameFamilyOn_range
    coordinateBasis hCoordinateOrthonormal basisData center base hValid]
  rw [identification.projected_range_eq base hValid]
  exact (physical.frame_range_eq base hValid).symm

/-- Therefore the projected-seed Gram--Schmidt frame and the physical normal
frame determine a canonical smooth orthogonal coordinate transition on the open
chart domain. -/
def projectedSeedToPhysicalNormalTransition
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (physical : PhysicalNormalFrameOn
      (Model := Model) basisData center)
    (identification : ProjectedSeedPhysicalRangeIdentification
      coordinateBasis hCoordinateOrthonormal basisData center physical) :
    P0EFTJanusRieszShapeOperatorOpenMovingFrame.SmoothOrthogonalFrameFamilyOn
      Base Model
      {base | projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base} :=
  openCanonicalFrameTransition
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData center)
    physical.frame
    (projectedSeedFrame_range_eq_physicalFrame coordinateBasis
      hCoordinateOrthonormal basisData center physical identification)

/-- On its valid domain, the canonical transition maps projected-seed normal
coordinates to the physical normal frame. -/
theorem projectedSeedToPhysicalNormalTransition_spec
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (physical : PhysicalNormalFrameOn
      (Model := Model) basisData center)
    (identification : ProjectedSeedPhysicalRangeIdentification
      coordinateBasis hCoordinateOrthonormal basisData center physical)
    (base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base)
    (normal : Model) :
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData center).frame base
        ((projectedSeedToPhysicalNormalTransition coordinateBasis
          hCoordinateOrthonormal basisData center physical identification).frame
          base normal) =
      physical.frame.frame base normal := by
  exact openCanonicalFrameTransition_spec
    (pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData center)
    physical.frame
    (projectedSeedFrame_range_eq_physicalFrame coordinateBasis
      hCoordinateOrthonormal basisData center physical identification)
    base hValid normal

/-- Status after isolating the exact physical-range theorem. -/
structure ProjectedSeedPhysicalRangeBridgeStatus where
  projectedSeedFramePackaged : Prop
  physicalNormalFrameSupplied : Prop
  projectedRangeIdentified : Prop
  commonRangeProved : Prop
  canonicalTransitionConstructed : Prop
  transitionSpecificationProved : Prop
  tangentTransitionConnected : Prop
  fullResidualTransitionConnected : Prop

/-- Closure of the projected-seed physical-range bridge. -/
def projectedSeedPhysicalRangeBridgeClosed
    (s : ProjectedSeedPhysicalRangeBridgeStatus) : Prop :=
  s.projectedSeedFramePackaged ∧
  s.physicalNormalFrameSupplied ∧
  s.projectedRangeIdentified ∧
  s.commonRangeProved ∧
  s.canonicalTransitionConstructed ∧
  s.transitionSpecificationProved ∧
  s.tangentTransitionConnected ∧
  s.fullResidualTransitionConnected

/-- After frame packaging and transition theory, the only remaining normal-side
geometric theorem is equality of the projected Gram--Schmidt span with the
physical normal range. -/
theorem missing_projected_range_identification_blocks_bridge
    (s : ProjectedSeedPhysicalRangeBridgeStatus)
    (hMissing : Not s.projectedRangeIdentified) :
    Not (projectedSeedPhysicalRangeBridgeClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.1

end

end P0EFTJanusRieszShapeOperatorProjectedSeedPhysicalRangeBridge
end JanusFormal
