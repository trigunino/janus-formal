import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedNormalSpaceTrivialization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameSmoothTransition

namespace JanusFormal
namespace P0EFTJanusProjectedSeedSmoothCoefficientTransport

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusNormalFrameSmoothTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorOpenCanonicalTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusActualStructuredJetExtraction
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusProjectedSeedNormalSpaceTrivialization

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

/-- Valid domain of one point-centered projected-seed chart. -/
def projectedSeedCoefficientDomain
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) : Set Base :=
  {base | projectedSeedChartValid basisData.tangentFrame
    (pointwiseNormalSeedCharts basisData) center base}

/-- Smooth tangent derivative on one fixed projected-seed chart. -/
def projectedSeedChartTangentDerivativeCLM
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base) : Tangent →L[ℝ] Ambient :=
  ((pointwiseBasisSmoothTangentFrameFamilyOn tangentBasis
    hTangentBasis basisData center).frame base).toContinuousLinearMap

theorem projectedSeedChartTangentDerivativeCLM_contDiffOn
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    ContDiffOn ℝ ∞
      (projectedSeedChartTangentDerivativeCLM tangentBasis
        hTangentBasis basisData center)
      (projectedSeedCoefficientDomain basisData center) := by
  exact (pointwiseBasisSmoothTangentFrameFamilyOn tangentBasis
    hTangentBasis basisData center).forward_contDiffOn

/-- Adjoint normal-coordinate projection on one fixed projected-seed chart. -/
def projectedSeedChartNormalAdjointCLM
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base) : Ambient →L[ℝ] Normal :=
  realAdjointContinuousLinearMap
    ((pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData center).frame base).toContinuousLinearMap

theorem projectedSeedChartNormalAdjointCLM_contDiffOn
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    ContDiffOn ℝ ∞
      (projectedSeedChartNormalAdjointCLM normalBasis
        hNormalBasis basisData center)
      (projectedSeedCoefficientDomain basisData center) := by
  exact realAdjointContinuousLinearMap.contDiff.comp_contDiffOn
    (pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
      hNormalBasis basisData center).forward_contDiffOn

/-- Typed postcomposition operator used to apply the immersion derivative to a
source-connection bilinear coefficient. -/
def sourceConnectionPostcomposeCLM :
    (Tangent →L[ℝ] Ambient) →L[ℝ]
      ((Tangent →L[ℝ] Tangent) →L[ℝ]
        (Tangent →L[ℝ] Ambient)) :=
  ContinuousLinearMap.compL ℝ Tangent Tangent Ambient

/-- Ambient contribution of the source connection after applying the immersion
first derivative. -/
def sourceConnectionAmbientCorrection
    (derivative : Tangent →L[ℝ] Ambient)
    (sourceConnection : ContinuousTangentialQuadratic Tangent) :
    ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) :=
  (sourceConnectionPostcomposeCLM
    (Tangent := Tangent) (Ambient := Ambient) derivative).comp
      sourceConnection

@[simp]
theorem sourceConnectionAmbientCorrection_apply
    (derivative : Tangent →L[ℝ] Ambient)
    (sourceConnection : ContinuousTangentialQuadratic Tangent)
    (first second : Tangent) :
    sourceConnectionAmbientCorrection derivative sourceConnection first second =
      derivative (sourceConnection first second) := by
  rfl

theorem sourceConnectionAmbientCorrection_contDiffOn
    {domain : Set Base}
    (derivative : Base → Tangent →L[ℝ] Ambient)
    (sourceConnection : Base → ContinuousTangentialQuadratic Tangent)
    (hDerivative : ContDiffOn ℝ ∞ derivative domain)
    (hSourceConnection : ContDiffOn ℝ ∞ sourceConnection domain) :
    ContDiffOn ℝ ∞
      (fun base => sourceConnectionAmbientCorrection
        (derivative base) (sourceConnection base)) domain := by
  have hPostcompose : ContDiffOn ℝ ∞
      (fun base => sourceConnectionPostcomposeCLM
        (Tangent := Tangent) (Ambient := Ambient) (derivative base)) domain := by
    fun_prop
  exact hPostcompose.clm_apply hSourceConnection

/-- Connection-corrected ambient second derivative as a bundled continuous
bilinear map. -/
def projectedSeedAmbientCovariantSecondDerivative
    (derivative : Tangent →L[ℝ] Ambient)
    (rawSecond ambientConnection : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (sourceConnection : ContinuousTangentialQuadratic Tangent) :
    ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) :=
  rawSecond + ambientConnection -
    sourceConnectionAmbientCorrection derivative sourceConnection

@[simp]
theorem projectedSeedAmbientCovariantSecondDerivative_apply
    (derivative : Tangent →L[ℝ] Ambient)
    (rawSecond ambientConnection : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (sourceConnection : ContinuousTangentialQuadratic Tangent)
    (first second : Tangent) :
    projectedSeedAmbientCovariantSecondDerivative derivative rawSecond
        ambientConnection sourceConnection first second =
      rawSecond first second + ambientConnection first second -
        derivative (sourceConnection first second) := by
  rfl

theorem projectedSeedAmbientCovariantSecondDerivative_contDiffOn
    {domain : Set Base}
    (derivative : Base → Tangent →L[ℝ] Ambient)
    (rawSecond ambientConnection : Base → ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (sourceConnection : Base → ContinuousTangentialQuadratic Tangent)
    (hDerivative : ContDiffOn ℝ ∞ derivative domain)
    (hRawSecond : ContDiffOn ℝ ∞ rawSecond domain)
    (hAmbientConnection : ContDiffOn ℝ ∞ ambientConnection domain)
    (hSourceConnection : ContDiffOn ℝ ∞ sourceConnection domain) :
    ContDiffOn ℝ ∞
      (fun base => projectedSeedAmbientCovariantSecondDerivative
        (derivative base) (rawSecond base) (ambientConnection base)
        (sourceConnection base)) domain := by
  exact (hRawSecond.add hAmbientConnection).sub
    (sourceConnectionAmbientCorrection_contDiffOn derivative sourceConnection
      hDerivative hSourceConnection)

/-- Typed postcomposition operator used to transport an ambient-valued
bilinear form into fixed normal coordinates. -/
def normalQuadraticPostcomposeCLM :
    (Ambient →L[ℝ] Normal) →L[ℝ]
      ((Tangent →L[ℝ] Ambient) →L[ℝ]
        (Tangent →L[ℝ] Normal)) :=
  ContinuousLinearMap.compL ℝ Tangent Ambient Normal

/-- Postcompose an ambient-valued continuous bilinear form by fixed-model normal
coordinates. -/
def projectedSeedFixedNormalQuadratic
    (normalAdjoint : Ambient →L[ℝ] Normal)
    (ambientForm : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient)) :
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  (normalQuadraticPostcomposeCLM
    (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
    normalAdjoint).comp ambientForm

@[simp]
theorem projectedSeedFixedNormalQuadratic_apply
    (normalAdjoint : Ambient →L[ℝ] Normal)
    (ambientForm : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (first second : Tangent) :
    projectedSeedFixedNormalQuadratic normalAdjoint ambientForm first second =
      normalAdjoint (ambientForm first second) := by
  rfl

theorem projectedSeedFixedNormalQuadratic_contDiffOn
    {domain : Set Base}
    (normalAdjoint : Base → Ambient →L[ℝ] Normal)
    (ambientForm : Base → ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient))
    (hNormalAdjoint : ContDiffOn ℝ ∞ normalAdjoint domain)
    (hAmbientForm : ContDiffOn ℝ ∞ ambientForm domain) :
    ContDiffOn ℝ ∞
      (fun base => projectedSeedFixedNormalQuadratic
        (normalAdjoint base) (ambientForm base)) domain := by
  have hPostcompose : ContDiffOn ℝ ∞
      (fun base => normalQuadraticPostcomposeCLM
        (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
        (normalAdjoint base)) domain := by
    fun_prop
  exact hPostcompose.clm_apply hAmbientForm

/-- Ambient corrected-jet family on one projected-seed chart. -/
structure ProjectedSeedSmoothAmbientJetFamilyOn
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) where
  rawSecond : Base → ContinuousAmbientQuadratic
    (Tangent := Tangent) (Ambient := Ambient)
  ambientConnection : Base → ContinuousAmbientQuadratic
    (Tangent := Tangent) (Ambient := Ambient)
  sourceConnection : Base → ContinuousTangentialQuadratic Tangent
  connectionValue : Base → ContinuousConnectionValue Tangent
  connectionDerivative : Base → ContinuousConnectionDerivative Tangent
  physicalNormalAmbient : Base → Ambient
  rawSecond_contDiffOn : ContDiffOn ℝ ∞ rawSecond
    (projectedSeedCoefficientDomain basisData center)
  ambientConnection_contDiffOn : ContDiffOn ℝ ∞ ambientConnection
    (projectedSeedCoefficientDomain basisData center)
  sourceConnection_contDiffOn : ContDiffOn ℝ ∞ sourceConnection
    (projectedSeedCoefficientDomain basisData center)
  connectionValue_contDiffOn : ContDiffOn ℝ ∞ connectionValue
    (projectedSeedCoefficientDomain basisData center)
  connectionDerivative_contDiffOn : ContDiffOn ℝ ∞ connectionDerivative
    (projectedSeedCoefficientDomain basisData center)
  physicalNormalAmbient_contDiffOn : ContDiffOn ℝ ∞ physicalNormalAmbient
    (projectedSeedCoefficientDomain basisData center)
  rawSecond_symmetric :
    ∀ base first second,
      rawSecond base first second = rawSecond base second first
  ambientConnection_symmetric :
    ∀ base first second,
      ambientConnection base first second =
        ambientConnection base second first
  sourceConnection_symmetric :
    ∀ base first second,
      sourceConnection base first second =
        sourceConnection base second first

variable {tangentBasis : Basis ι ℝ Tangent}
variable {hTangentBasis : Orthonormal ℝ tangentBasis}
variable {normalBasis : Basis κ ℝ Normal}
variable {hNormalBasis : Orthonormal ℝ normalBasis}
variable {basisData : PointwiseNormalBasisData Base Ambient ι κ}
variable {center : Base}

/-- Corrected ambient second derivative associated with the chart family. -/
def ProjectedSeedSmoothAmbientJetFamilyOn.correctedAmbientSecondDerivative
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) :=
  projectedSeedAmbientCovariantSecondDerivative
    (projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
      basisData center base)
    (data.rawSecond base) (data.ambientConnection base)
    (data.sourceConnection base)

theorem ProjectedSeedSmoothAmbientJetFamilyOn.correctedAmbientSecondDerivative_contDiffOn
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center) :
    ContDiffOn ℝ ∞ data.correctedAmbientSecondDerivative
      (projectedSeedCoefficientDomain basisData center) := by
  exact projectedSeedAmbientCovariantSecondDerivative_contDiffOn
    (projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
      basisData center)
    data.rawSecond data.ambientConnection data.sourceConnection
    (projectedSeedChartTangentDerivativeCLM_contDiffOn tangentBasis
      hTangentBasis basisData center)
    data.rawSecond_contDiffOn data.ambientConnection_contDiffOn
    data.sourceConnection_contDiffOn

/-- Fixed-model second fundamental coefficient extracted by the smooth adjoint
normal frame. -/
def ProjectedSeedSmoothAmbientJetFamilyOn.normalQuadratic
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) : ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  projectedSeedFixedNormalQuadratic
    (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
      basisData center base)
    (data.correctedAmbientSecondDerivative base)

theorem ProjectedSeedSmoothAmbientJetFamilyOn.normalQuadratic_contDiffOn
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center) :
    ContDiffOn ℝ ∞ data.normalQuadratic
      (projectedSeedCoefficientDomain basisData center) := by
  exact projectedSeedFixedNormalQuadratic_contDiffOn
    (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
      basisData center)
    data.correctedAmbientSecondDerivative
    (projectedSeedChartNormalAdjointCLM_contDiffOn normalBasis
      hNormalBasis basisData center)
    data.correctedAmbientSecondDerivative_contDiffOn

/-- Fixed-model coordinates of an ambient normal field. -/
def ProjectedSeedSmoothAmbientJetFamilyOn.physicalNormal
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) : Normal :=
  projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
    basisData center base (data.physicalNormalAmbient base)

theorem ProjectedSeedSmoothAmbientJetFamilyOn.physicalNormal_contDiffOn
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center) :
    ContDiffOn ℝ ∞ data.physicalNormal
      (projectedSeedCoefficientDomain basisData center) := by
  exact (projectedSeedChartNormalAdjointCLM_contDiffOn normalBasis
    hNormalBasis basisData center).clm_apply
      data.physicalNormalAmbient_contDiffOn

/-- Actual fixed-model local coefficient package extracted at one chart point. -/
def ProjectedSeedSmoothAmbientJetFamilyOn.localJet
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal) where
  tangentialQuadratic := data.sourceConnection base
  normalQuadratic := data.normalQuadratic base
  connectionValue := data.connectionValue base
  connectionDerivative := data.connectionDerivative base
  physicalNormal := data.physicalNormal base
  tangentialQuadratic_symmetric := data.sourceConnection_symmetric base
  normalQuadratic_symmetric := by
    intro first second
    change
      projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
          basisData center base
          (projectedSeedAmbientCovariantSecondDerivative
            (projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
              basisData center base)
            (data.rawSecond base) (data.ambientConnection base)
            (data.sourceConnection base) first second) =
        projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
          basisData center base
          (projectedSeedAmbientCovariantSecondDerivative
            (projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
              basisData center base)
            (data.rawSecond base) (data.ambientConnection base)
            (data.sourceConnection base) second first)
    apply congrArg
      (projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
        basisData center base)
    rw [projectedSeedAmbientCovariantSecondDerivative_apply,
      projectedSeedAmbientCovariantSecondDerivative_apply,
      data.rawSecond_symmetric base first second,
      data.ambientConnection_symmetric base first second,
      data.sourceConnection_symmetric base first second]

/-- Structured fixed-model jet family on the chart. -/
def ProjectedSeedSmoothAmbientJetFamilyOn.structuredJet
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) : SmoothLowOrderStructuredJet Tangent Normal :=
  ((data.sourceConnection base, data.normalQuadratic base),
    (data.connectionValue base, data.connectionDerivative base))

theorem ProjectedSeedSmoothAmbientJetFamilyOn.structuredJet_contDiffOn
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center) :
    ContDiffOn ℝ ∞ data.structuredJet
      (projectedSeedCoefficientDomain basisData center) := by
  exact (data.sourceConnection_contDiffOn.prodMk
    data.normalQuadratic_contDiffOn).prodMk
      (data.connectionValue_contDiffOn.prodMk
        data.connectionDerivative_contDiffOn)

/-- Reduced `(II,F)` family extracted on the chart. -/
def ProjectedSeedSmoothAmbientJetFamilyOn.reducedJet
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) : SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal) :=
  smoothLowOrderReduction (data.structuredJet base)

theorem ProjectedSeedSmoothAmbientJetFamilyOn.reducedJet_contDiffOn
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center) :
    ContDiffOn ℝ ∞ data.reducedJet
      (projectedSeedCoefficientDomain basisData center) := by
  exact (smoothLowOrderReduction_contDiff
    (Tangent := Tangent) (Normal := Normal)).comp_contDiffOn
      data.structuredJet_contDiffOn

/-- Physical Riesz shape-operator family on the chart. -/
def ProjectedSeedSmoothAmbientJetFamilyOn.physicalOperator
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) : Tangent →L[ℝ] Tangent :=
  continuousIIRieszShapeOperator
    (data.normalQuadratic base) (data.physicalNormal base)

theorem ProjectedSeedSmoothAmbientJetFamilyOn.physicalOperator_contDiffOn
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center) :
    ContDiffOn ℝ ∞ data.physicalOperator
      (projectedSeedCoefficientDomain basisData center) := by
  change ContDiffOn ℝ ∞
    (fun base => continuousIIRieszShapeOperator
      (data.normalQuadratic base) (data.physicalNormal base))
    (projectedSeedCoefficientDomain basisData center)
  have hPair : ContDiffOn ℝ ∞
      (fun base => (data.normalQuadratic base, data.physicalNormal base))
      (projectedSeedCoefficientDomain basisData center) :=
    data.normalQuadratic_contDiffOn.prodMk data.physicalNormal_contDiffOn
  exact (continuousIIRieszShape_joint_contDiff
    (Tangent := Tangent) (Normal := Normal)).comp_contDiffOn hPair

/-- Exact fixed-coordinate formula for the transported second fundamental form. -/
@[simp]
theorem ProjectedSeedSmoothAmbientJetFamilyOn.normalQuadratic_apply
    (data : ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center)
    (base : Base) (first second : Tangent) :
    data.normalQuadratic base first second =
      projectedSeedChartNormalAdjointCLM normalBasis hNormalBasis
        basisData center base
        (data.rawSecond base first second +
          data.ambientConnection base first second -
          projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
            basisData center base
            (data.sourceConnection base first second)) := by
  rfl

structure ProjectedSeedSmoothCoefficientTransportStatus where
  chartTangentDerivativeSmooth : Prop
  chartNormalAdjointSmooth : Prop
  correctedAmbientSecondDerivativeSmooth : Prop
  fixedNormalSecondFundamentalFormSmooth : Prop
  fixedPhysicalNormalSmooth : Prop
  structuredJetSmoothOnChart : Prop
  reducedJetSmoothOnChart : Prop
  physicalRieszOperatorSmoothOnChart : Prop
  overlapCompatibilityProved : Prop
  genuineManifoldJetFamilySupplied : Prop

def projectedSeedSmoothCoefficientTransportClosed
    (s : ProjectedSeedSmoothCoefficientTransportStatus) : Prop :=
  s.chartTangentDerivativeSmooth ∧
  s.chartNormalAdjointSmooth ∧
  s.correctedAmbientSecondDerivativeSmooth ∧
  s.fixedNormalSecondFundamentalFormSmooth ∧
  s.fixedPhysicalNormalSmooth ∧
  s.structuredJetSmoothOnChart ∧
  s.reducedJetSmoothOnChart ∧
  s.physicalRieszOperatorSmoothOnChart ∧
  s.overlapCompatibilityProved ∧
  s.genuineManifoldJetFamilySupplied

theorem missing_overlap_compatibility_blocks_closure
    (s : ProjectedSeedSmoothCoefficientTransportStatus)
    (hMissing : Not s.overlapCompatibilityProved) :
    Not (projectedSeedSmoothCoefficientTransportClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusProjectedSeedSmoothCoefficientTransport
end JanusFormal
