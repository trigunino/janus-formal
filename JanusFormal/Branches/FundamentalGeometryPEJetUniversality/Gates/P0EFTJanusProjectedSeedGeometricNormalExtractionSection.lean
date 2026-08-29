import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedGeometricNormalVectorBundleCore

namespace JanusFormal
namespace P0EFTJanusProjectedSeedGeometricNormalExtractionSection

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace Manifold
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusProjectedSeedNormalSpaceTrivialization
open P0EFTJanusProjectedSeedVaryingNormalBundle
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
open P0EFTJanusProjectedSeedGeometricNormalVectorBundleCore

universe uBase uTangent uNormal uAmbient uIndex

variable {Base : Type uBase} {Tangent : Type uTangent}
variable {Normal : Type uNormal} {Ambient : Type uAmbient}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type uIndex}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Preferred point-centred coordinate of the intrinsic physical normal. -/
def projectedSeedPreferredPhysicalNormal
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (base : Base) : Normal :=
  (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension base base
    (pointwiseNormalSeedChart_valid_at_center basisData base)
    (correctedJet base)).physicalNormal

/-- Local physical-normal coordinate extracted geometrically in the chart
centred at `center`.  Outside its chart domain the value is set to zero only to
give a total function; every theorem below is restricted to the exact domain. -/
def projectedSeedLocalPhysicalNormal
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (center base : Base) : Normal := by
  classical
  exact if hValid : projectedSeedGeometricNormalDomain basisData center base then
    (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension center base hValid
      (correctedJet base)).physicalNormal
  else 0

/-- On a valid chart the total local coordinate is definitionally the genuine
projected-seed extraction. -/
theorem projectedSeedLocalPhysicalNormal_eq_extraction
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (center base : Base)
    (hValid : projectedSeedGeometricNormalDomain basisData center base) :
    projectedSeedLocalPhysicalNormal tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension correctedJet center base =
      (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hValid
        (correctedJet base)).physicalNormal := by
  rw [projectedSeedLocalPhysicalNormal, dif_pos hValid]

/-- Exact coordinate law: transporting the preferred point-centred normal into
any valid chart gives the real geometric extractor in that chart. -/
theorem projectedSeedPhysicalNormal_coordinate_eq
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (center base : Base)
    (hValid : base ∈
      (projectedSeedGeometricNormalCore normalBasis hNormalBasis
        basisData hDimension).baseSet center) :
    (projectedSeedGeometricNormalCore normalBasis hNormalBasis
        basisData hDimension).coordChange
      ((projectedSeedGeometricNormalCore normalBasis hNormalBasis
        basisData hDimension).indexAt base)
      center base
      (projectedSeedPreferredPhysicalNormal tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension correctedJet base) =
      projectedSeedLocalPhysicalNormal tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension correctedJet center base := by
  have hCenter : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base := hValid
  have hPoint : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) base base :=
    pointwiseNormalSeedChart_valid_at_center basisData base
  rw [projectedSeedLocalPhysicalNormal_eq_extraction tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension correctedJet center base hValid]
  change
    (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
      basisData hDimension center base).frame base
        ((projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
          normalBasis hNormalBasis basisData hDimension base base hPoint
          (correctedJet base)).physicalNormal) =
      (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hCenter
        (correctedJet base)).physicalNormal
  exact (projectedSeedActualJanusLocalJetData_physicalNormal_transition
    tangentBasis hTangentBasis normalBasis hNormalBasis basisData hDimension
    center base base hCenter hPoint (correctedJet base)).symm

/-- Preferred point-centred coordinate of the real second fundamental form. -/
def projectedSeedPreferredNormalQuadratic
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (base : Base) :
    ContinuousSecondFundamentalForm (Tangent := Tangent) (Normal := Normal) :=
  (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension base base
    (pointwiseNormalSeedChart_valid_at_center basisData base)
    (correctedJet base)).normalQuadratic

/-- Local second-fundamental-form coordinate obtained from the same corrected
immersion jet and normal trivialization as `physicalNormal`. -/
def projectedSeedLocalNormalQuadratic
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (center base : Base) :
    ContinuousSecondFundamentalForm (Tangent := Tangent) (Normal := Normal) := by
  classical
  exact if hValid : projectedSeedGeometricNormalDomain basisData center base then
    (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension center base hValid
      (correctedJet base)).normalQuadratic
  else 0

/-- The extracted local second fundamental form is symmetric, with no external
normal coefficient. -/
theorem projectedSeedLocalNormalQuadratic_symmetric
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (center base : Base)
    (hValid : projectedSeedGeometricNormalDomain basisData center base)
    (first second : Tangent) :
    projectedSeedLocalNormalQuadratic tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension correctedJet center base first second =
      projectedSeedLocalNormalQuadratic tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension correctedJet center base second first := by
  rw [projectedSeedLocalNormalQuadratic, dif_pos hValid]
  exact (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension center base hValid
    (correctedJet base)).normalQuadratic_symmetric first second

/-- The only analytic input still required for a global smooth normal section is
regularity of the exact chartwise geometric extraction defined above.  No
independent normal field is stored here. -/
structure ProjectedSeedGeometricNormalExtractionRegularity
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base)) where
  physicalNormal_contDiffOn : ∀ center,
    ContDiffOn ℝ ∞
      (projectedSeedLocalPhysicalNormal tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension correctedJet center)
      (projectedSeedGeometricNormalDomain basisData center)
  normalQuadratic_contDiffOn : ∀ center,
    ContDiffOn ℝ ∞
      (projectedSeedLocalNormalQuadratic tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension correctedJet center)
      (projectedSeedGeometricNormalDomain basisData center)

/-- The genuine extracted physical normal as a smooth coordinate package for
the intrinsic projected-seed normal bundle. -/
def projectedSeedGeometricPhysicalNormalCoordinates
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (regularity : ProjectedSeedGeometricNormalExtractionRegularity
      tangentBasis hTangentBasis normalBasis hNormalBasis basisData hDimension
      correctedJet) :
    SmoothCoreSectionCoordinates 𝓘(ℝ, Base)
      (projectedSeedGeometricNormalCore normalBasis hNormalBasis
        basisData hDimension) where
  value := projectedSeedPreferredPhysicalNormal tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension correctedJet
  extractor := projectedSeedLocalPhysicalNormal tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension correctedJet
  coordinate_eq := by
    intro center base hValid
    exact projectedSeedPhysicalNormal_coordinate_eq tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension correctedJet center base hValid
  extractor_contMDiffOn := by
    intro center
    exact (regularity.physicalNormal_contDiffOn center).contMDiffOn

end

end P0EFTJanusProjectedSeedGeometricNormalExtractionSection
end JanusFormal
