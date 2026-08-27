import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedSmoothCoefficientTransport
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedGeometricNormalExtractionSection

namespace JanusFormal
namespace P0EFTJanusProjectedSeedGeometricNormalRegularityFromAmbientJet

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusProjectedSeedNormalSpaceTrivialization
open P0EFTJanusProjectedSeedSmoothCoefficientTransport
open P0EFTJanusProjectedSeedGeometricNormalVectorBundleCore
open P0EFTJanusProjectedSeedGeometricNormalExtractionSection

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

/-- A chartwise smooth ambient jet realizes the intrinsic corrected immersion
jet when their complete fixed-model local coefficient packages agree.  This
stores no extra normal or second fundamental form: both are fields of the two
packages whose equality is required. -/
structure ProjectedSeedAmbientJetRealization
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base)) where
  ambientJet : ∀ center,
    ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center
  localJet_eq : ∀ center base
      (hValid : projectedSeedGeometricNormalDomain basisData center base),
    (ambientJet center).localJet base =
      projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hValid
        (correctedJet base)

/-- The smooth ambient realization proves regularity of the exact intrinsic
`physicalNormal` and `normalQuadratic` extraction functions. -/
def ProjectedSeedAmbientJetRealization.toExtractionRegularity
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (realization : ProjectedSeedAmbientJetRealization tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension correctedJet) :
    ProjectedSeedGeometricNormalExtractionRegularity tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension correctedJet where
  physicalNormal_contDiffOn center := by
    apply (realization.ambientJet center).physicalNormal_contDiffOn.congr
    intro base hValid
    have hGeometric : base ∈ projectedSeedGeometricNormalDomain basisData center := by
      simpa only [projectedSeedCoefficientDomain,
        projectedSeedGeometricNormalDomain] using hValid
    rw [projectedSeedLocalPhysicalNormal_eq_extraction tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension correctedJet center base hGeometric]
    exact (congrArg ActualJanusLocalJetData.physicalNormal
      (realization.localJet_eq center base hGeometric)).symm
  normalQuadratic_contDiffOn center := by
    apply (realization.ambientJet center).normalQuadratic_contDiffOn.congr
    intro base hValid
    have hGeometric : base ∈ projectedSeedGeometricNormalDomain basisData center := by
      simpa only [projectedSeedCoefficientDomain,
        projectedSeedGeometricNormalDomain] using hValid
    have hGeometricCall :
        projectedSeedGeometricNormalDomain basisData center base := by
      change base ∈ projectedSeedGeometricNormalDomain basisData center
      exact hGeometric
    rw [projectedSeedLocalNormalQuadratic, dif_pos hGeometricCall]
    exact (congrArg ActualJanusLocalJetData.normalQuadratic
      (realization.localJet_eq center base hGeometric)).symm

/-- The physical-normal smooth coordinate package obtained with no independent
normal regularity premise. -/
def ProjectedSeedAmbientJetRealization.physicalNormalCoordinates
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (correctedJet : ∀ base,
      ConnectionCorrectedActualJanusLocalJetData
        (projectedSeedTangentDerivative tangentBasis hTangentBasis basisData base))
    (realization : ProjectedSeedAmbientJetRealization tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension correctedJet) :=
  projectedSeedGeometricPhysicalNormalCoordinates tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension correctedJet
    (realization.toExtractionRegularity tangentBasis hTangentBasis normalBasis
      hNormalBasis basisData hDimension correctedJet)

end

end P0EFTJanusProjectedSeedGeometricNormalRegularityFromAmbientJet
end JanusFormal
