import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedGeometricNormalRegularityFromAmbientJet

namespace JanusFormal
namespace P0EFTJanusProjectedSeedGeometricNormalQuadraticBundleCore

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff InnerProductSpace Manifold
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusProjectedSeedNormalSpaceTrivialization
open P0EFTJanusProjectedSeedVaryingNormalBundle
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
open P0EFTJanusProjectedSeedGeometricNormalVectorBundleCore
open P0EFTJanusProjectedSeedGeometricNormalExtractionSection
open P0EFTJanusProjectedSeedGeometricNormalRegularityFromAmbientJet

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

/-- Postcomposition of both layers of a continuous second fundamental form by
one normal-coordinate linear map. -/
def continuousSecondFundamentalFormTransportCLM
    (transport : Normal →L[ℝ] Normal) :
    ContinuousSecondFundamentalForm (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousSecondFundamentalForm (Tangent := Tangent) (Normal := Normal) :=
  ContinuousLinearMap.compL ℝ Tangent
    (Tangent →L[ℝ] Normal) (Tangent →L[ℝ] Normal)
    (ContinuousLinearMap.compL ℝ Tangent Normal Normal transport)

@[simp]
theorem continuousSecondFundamentalFormTransportCLM_apply
    (transport : Normal →L[ℝ] Normal)
    (form : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (first second : Tangent) :
    continuousSecondFundamentalFormTransportCLM transport form first second =
      transport (form first second) :=
  rfl

/-- Continuous linear dependence of the induced coefficient transport on the
normal-coordinate transport. -/
def continuousSecondFundamentalFormTransportOperator :
    (Normal →L[ℝ] Normal) →L[ℝ]
      (ContinuousSecondFundamentalForm
          (Tangent := Tangent) (Normal := Normal) →L[ℝ]
        ContinuousSecondFundamentalForm
          (Tangent := Tangent) (Normal := Normal)) :=
  (ContinuousLinearMap.compL ℝ Tangent
    (Tangent →L[ℝ] Normal) (Tangent →L[ℝ] Normal)).comp
      (ContinuousLinearMap.compL ℝ Tangent Normal Normal)

@[simp]
theorem continuousSecondFundamentalFormTransportOperator_apply
    (transport : Normal →L[ℝ] Normal) :
    continuousSecondFundamentalFormTransportOperator
        (Tangent := Tangent) (Normal := Normal) transport =
      continuousSecondFundamentalFormTransportCLM transport :=
  rfl

/-- The bundle of normal-valued second fundamental forms induced functorially
from the intrinsic projected-seed normal bundle. -/
def projectedSeedGeometricNormalQuadraticCore
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    VectorBundleCore ℝ Base
      (ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal)) Base := by
  let normalCore := projectedSeedGeometricNormalCore normalBasis hNormalBasis
    basisData hDimension
  exact
    { baseSet := normalCore.baseSet
      isOpen_baseSet := normalCore.isOpen_baseSet
      indexAt := normalCore.indexAt
      mem_baseSet_at := normalCore.mem_baseSet_at
      coordChange := fun first second base =>
        continuousSecondFundamentalFormTransportCLM
          (normalCore.coordChange first second base)
      coordChange_self := by
        intro chart base hBase form
        apply ContinuousLinearMap.ext
        intro first
        apply ContinuousLinearMap.ext
        intro second
        exact normalCore.coordChange_self chart base hBase (form first second)
      continuousOn_coordChange := by
        intro first second
        exact continuousSecondFundamentalFormTransportOperator.continuous.comp_continuousOn
          (normalCore.continuousOn_coordChange first second)
      coordChange_comp := by
        intro first second third base hBase form
        apply ContinuousLinearMap.ext
        intro x
        apply ContinuousLinearMap.ext
        intro y
        exact normalCore.coordChange_comp first second third base hBase (form x y) }

/-- Smoothness of the induced second-fundamental-form core follows by smooth
linear functoriality from the geometric normal core. -/
theorem projectedSeedGeometricNormalQuadraticCore_isContMDiff
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    (projectedSeedGeometricNormalQuadraticCore
      (Tangent := Tangent) normalBasis hNormalBasis basisData hDimension).IsContMDiff
        𝓘(ℝ, Base) ∞ := by
  let normalCore := projectedSeedGeometricNormalCore normalBasis hNormalBasis
    basisData hDimension
  letI normalCoreSmooth : normalCore.IsContMDiff 𝓘(ℝ, Base) ∞ :=
    projectedSeedGeometricNormalCore_isContMDiff normalBasis hNormalBasis
      basisData hDimension
  constructor
  intro first second
  have hNormal : ContDiffOn ℝ ∞
      (normalCore.coordChange first second)
      (normalCore.baseSet first ∩ normalCore.baseSet second) :=
    (normalCore.contMDiffOn_coordChange 𝓘(ℝ, Base) first second).contDiffOn
  have hTransport : ContDiffOn ℝ ∞
      (fun base => continuousSecondFundamentalFormTransportOperator
        (Tangent := Tangent) (Normal := Normal)
        (normalCore.coordChange first second base))
      (normalCore.baseSet first ∩ normalCore.baseSet second) :=
    continuousSecondFundamentalFormTransportOperator.contDiff.comp_contDiffOn hNormal
  exact hTransport.contMDiffOn

/-- Exact overlap law for the real geometrically extracted normal quadratic. -/
theorem projectedSeedNormalQuadratic_coordinate_eq
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
      (projectedSeedGeometricNormalQuadraticCore
        (Tangent := Tangent) normalBasis hNormalBasis basisData hDimension).baseSet
        center) :
    (projectedSeedGeometricNormalQuadraticCore
        (Tangent := Tangent) normalBasis hNormalBasis basisData hDimension).coordChange
      ((projectedSeedGeometricNormalQuadraticCore
        (Tangent := Tangent) normalBasis hNormalBasis basisData hDimension).indexAt base)
      center base
      (projectedSeedPreferredNormalQuadratic tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension correctedJet base) =
      projectedSeedLocalNormalQuadratic tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension correctedJet center base := by
  have hCenter : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base := hValid
  have hPoint : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) base base :=
    pointwiseNormalSeedChart_valid_at_center basisData base
  rw [projectedSeedLocalNormalQuadratic, dif_pos hValid]
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change
    (projectedSeedNormalTransitionOnOverlap normalBasis hNormalBasis
      basisData hDimension center base).frame base
        ((projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
          normalBasis hNormalBasis basisData hDimension base base hPoint
          (correctedJet base)).normalQuadratic first second) =
      (projectedSeedActualJanusLocalJetData tangentBasis hTangentBasis
        normalBasis hNormalBasis basisData hDimension center base hCenter
        (correctedJet base)).normalQuadratic first second
  exact (projectedSeedActualJanusLocalJetData_normalQuadratic_transition
    tangentBasis hTangentBasis normalBasis hNormalBasis basisData hDimension
    center base base hCenter hPoint (correctedJet base) first second).symm

/-- Smooth section coordinates for the real second fundamental form on its
induced bundle. -/
def projectedSeedGeometricNormalQuadraticCoordinates
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
      (projectedSeedGeometricNormalQuadraticCore
        (Tangent := Tangent) normalBasis hNormalBasis basisData hDimension) where
  value := projectedSeedPreferredNormalQuadratic tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension correctedJet
  extractor := projectedSeedLocalNormalQuadratic tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension correctedJet
  coordinate_eq := by
    intro center base hValid
    exact projectedSeedNormalQuadratic_coordinate_eq tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData hDimension correctedJet center base hValid
  extractor_contMDiffOn := by
    intro center
    exact (regularity.normalQuadratic_contDiffOn center).contMDiffOn

end

end P0EFTJanusProjectedSeedGeometricNormalQuadraticBundleCore
end JanusFormal
