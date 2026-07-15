import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedAmbientJetSmoothDescent

namespace JanusFormal
namespace P0EFTJanusEuclideanImmersionConnectionJetExtraction

set_option autoImplicit false

noncomputable section

open Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusProjectedSeedSmoothCoefficientTransport
open P0EFTJanusProjectedSeedAmbientJetDescent
open P0EFTJanusProjectedSeedAmbientJetSmoothDescent

universe u v y

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type*}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Genuine fixed-chart immersion and abelian connection data. The raw second
immersion coefficient and the connection derivative are not independent fields:
they are extracted below by applying `fderiv` twice and once, respectively. -/
structure EuclideanImmersionConnectionJetData where
  immersion : Tangent → Ambient
  gaugePotential : Tangent → ContinuousConnectionValue Tangent
  ambientConnection : Tangent → ContinuousAmbientQuadratic
    (Tangent := Tangent) (Ambient := Ambient)
  sourceConnection : Tangent → ContinuousTangentialQuadratic Tangent
  physicalNormalAmbient : Tangent → Ambient
  immersion_contDiff : ContDiff ℝ ∞ immersion
  gaugePotential_contDiff : ContDiff ℝ ∞ gaugePotential
  ambientConnection_contDiff : ContDiff ℝ ∞ ambientConnection
  sourceConnection_contDiff : ContDiff ℝ ∞ sourceConnection
  physicalNormalAmbient_contDiff : ContDiff ℝ ∞ physicalNormalAmbient
  ambientConnection_symmetric :
    ∀ base first second,
      ambientConnection base first second =
        ambientConnection base second first
  sourceConnection_symmetric :
    ∀ base first second,
      sourceConnection base first second =
        sourceConnection base second first

/-- First derivative of the actual immersion. -/
def EuclideanImmersionConnectionJetData.firstDerivative
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    Tangent → Tangent →L[ℝ] Ambient :=
  fderiv ℝ data.immersion

theorem EuclideanImmersionConnectionJetData.firstDerivative_contDiff
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ContDiff ℝ ∞ data.firstDerivative := by
  simpa [EuclideanImmersionConnectionJetData.firstDerivative] using
    data.immersion_contDiff.fderiv_right (m := ∞) (by simp)

/-- Raw second derivative of the actual immersion. -/
def EuclideanImmersionConnectionJetData.rawSecond
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    Tangent → ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) :=
  fderiv ℝ data.firstDerivative

theorem EuclideanImmersionConnectionJetData.rawSecond_contDiff
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ContDiff ℝ ∞ data.rawSecond := by
  simpa [EuclideanImmersionConnectionJetData.rawSecond] using
    data.firstDerivative_contDiff.fderiv_right (m := ∞) (by simp)

/-- Derivative of the local abelian connection potential. -/
def EuclideanImmersionConnectionJetData.connectionDerivative
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    Tangent → ContinuousConnectionDerivative Tangent :=
  fderiv ℝ data.gaugePotential

theorem EuclideanImmersionConnectionJetData.connectionDerivative_contDiff
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ContDiff ℝ ∞ data.connectionDerivative := by
  simpa [EuclideanImmersionConnectionJetData.connectionDerivative] using
    data.gaugePotential_contDiff.fderiv_right (m := ∞) (by simp)

/-- Schwarz symmetry of the raw second immersion derivative. -/
theorem EuclideanImmersionConnectionJetData.rawSecond_symmetric
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ∀ base first second,
      data.rawSecond base first second =
        data.rawSecond base second first := by
  intro base first second
  change fderiv ℝ (fderiv ℝ data.immersion) base first second =
    fderiv ℝ (fderiv ℝ data.immersion) base second first
  exact (ContDiffAt.isSymmSndFDerivAt
    (n := ∞) data.immersion_contDiff.contDiffAt (by exact le_top)) first second

/-- The actual immersion and gauge-potential data instantiate the global ambient
coefficient interface used by projected-seed descent. -/
def EuclideanImmersionConnectionJetData.toProjectedSeedGlobalAmbientJetData
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient)) :
    ProjectedSeedGlobalAmbientJetData
      (Base := Tangent) (Tangent := Tangent) (Ambient := Ambient) where
  rawSecond := data.rawSecond
  ambientConnection := data.ambientConnection
  sourceConnection := data.sourceConnection
  connectionValue := data.gaugePotential
  connectionDerivative := data.connectionDerivative
  physicalNormalAmbient := data.physicalNormalAmbient
  rawSecond_contDiff := data.rawSecond_contDiff
  ambientConnection_contDiff := data.ambientConnection_contDiff
  sourceConnection_contDiff := data.sourceConnection_contDiff
  connectionValue_contDiff := data.gaugePotential_contDiff
  connectionDerivative_contDiff := data.connectionDerivative_contDiff
  physicalNormalAmbient_contDiff := data.physicalNormalAmbient_contDiff
  rawSecond_symmetric := data.rawSecond_symmetric
  ambientConnection_symmetric := data.ambientConnection_symmetric
  sourceConnection_symmetric := data.sourceConnection_symmetric

@[simp]
theorem EuclideanImmersionConnectionJetData.toGlobal_rawSecond_apply
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient))
    (base first second : Tangent) :
    data.toProjectedSeedGlobalAmbientJetData.rawSecond base first second =
      fderiv ℝ (fderiv ℝ data.immersion) base first second := by
  rfl

@[simp]
theorem EuclideanImmersionConnectionJetData.toGlobal_connectionDerivative_apply
    (data : EuclideanImmersionConnectionJetData
      (Tangent := Tangent) (Ambient := Ambient))
    (base first second : Tangent) :
    data.toProjectedSeedGlobalAmbientJetData.connectionDerivative base
        first second =
      fderiv ℝ data.gaugePotential base first second := by
  rfl

/-- Actual Euclidean jet data together with the projected-seed geometry used to
express its normal coefficients and descend the physical operator. -/
structure EuclideanProjectedSeedImmersionData where
  coefficients : EuclideanImmersionConnectionJetData
    (Tangent := Tangent) (Ambient := Ambient)
  tangentBasis : Basis ι ℝ Tangent
  tangentBasis_orthonormal : Orthonormal ℝ tangentBasis
  normalBasis : Basis κ ℝ Normal
  normalBasis_orthonormal : Orthonormal ℝ normalBasis
  basisData : PointwiseNormalBasisData Tangent Ambient ι κ
  ambientDimension :
    Fintype.card ι + Fintype.card κ = finrank ℝ Ambient
  immersion_fderiv_eq_tangentSynthesis :
    ∀ base,
      coefficients.firstDerivative base =
        tangentFrameSynthesisCLM tangentBasis basisData base

/-- Global physical shape operator extracted from the actual immersion and
connection potential. -/
def EuclideanProjectedSeedImmersionData.physicalOperator
    (data : EuclideanProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    Tangent → Tangent →L[ℝ] Tangent :=
  ProjectedSeedGlobalAmbientJetData.descendedPhysicalOperator
    data.coefficients.toProjectedSeedGlobalAmbientJetData data.tangentBasis
    data.tangentBasis_orthonormal data.normalBasis
    data.normalBasis_orthonormal data.basisData data.ambientDimension

/-- The physical shape operator extracted from genuine fixed-chart derivatives
is globally smooth. -/
theorem EuclideanProjectedSeedImmersionData.physicalOperator_contDiff
    (data : EuclideanProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  exact ProjectedSeedGlobalAmbientJetData.descendedPhysicalOperator_contDiff
    data.coefficients.toProjectedSeedGlobalAmbientJetData data.tangentBasis
    data.tangentBasis_orthonormal data.normalBasis
    data.normalBasis_orthonormal data.basisData data.ambientDimension

/-- The center-independent corrected ambient coefficient is exactly
`D²i + Γᴹ - Di(ΓΣ)`, with both derivatives computed from the actual immersion. -/
theorem EuclideanProjectedSeedImmersionData.correctedAmbientSecondDerivative_apply
    (data : EuclideanProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (base first second : Tangent) :
    (ProjectedSeedGlobalAmbientJetData.correctedAmbientSecondDerivative
      data.coefficients.toProjectedSeedGlobalAmbientJetData
      data.tangentBasis data.basisData base) first second =
      fderiv ℝ (fderiv ℝ data.coefficients.immersion) base first second +
        data.coefficients.ambientConnection base first second -
        fderiv ℝ data.coefficients.immersion base
          (data.coefficients.sourceConnection base first second) := by
  change
    fderiv ℝ (fderiv ℝ data.coefficients.immersion) base first second +
        data.coefficients.ambientConnection base first second -
        tangentFrameSynthesisCLM data.tangentBasis data.basisData base
          (data.coefficients.sourceConnection base first second) = _
  rw [← data.immersion_fderiv_eq_tangentSynthesis base]
  rfl

/-- On every valid projected-seed chart, the fixed-model second fundamental
coefficient is the normal-frame adjoint applied to the actual corrected second
derivative. -/
theorem EuclideanProjectedSeedImmersionData.chart_normalQuadratic_apply
    (data : EuclideanProjectedSeedImmersionData
      (Tangent := Tangent) (Normal := Normal) (Ambient := Ambient)
      (ι := ι) (κ := κ))
    (center base : Tangent)
    (hValid : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) center base)
    (first second : Tangent) :
    ((ProjectedSeedGlobalAmbientJetData.toChartData
      data.coefficients.toProjectedSeedGlobalAmbientJetData
      data.tangentBasis data.tangentBasis_orthonormal data.normalBasis
      data.normalBasis_orthonormal data.basisData center).normalQuadratic base)
        first second =
      projectedSeedChartNormalAdjointCLM data.normalBasis
        data.normalBasis_orthonormal data.basisData center base
        (fderiv ℝ (fderiv ℝ data.coefficients.immersion) base first second +
          data.coefficients.ambientConnection base first second -
          fderiv ℝ data.coefficients.immersion base
            (data.coefficients.sourceConnection base first second)) := by
  change projectedSeedChartNormalAdjointCLM data.normalBasis
      data.normalBasis_orthonormal data.basisData center base
      (fderiv ℝ (fderiv ℝ data.coefficients.immersion) base first second +
        data.coefficients.ambientConnection base first second -
        projectedSeedChartTangentDerivativeCLM data.tangentBasis
          data.tangentBasis_orthonormal data.basisData center base
          (data.coefficients.sourceConnection base first second)) = _
  rw [projectedSeedChartTangentDerivativeCLM_eq_synthesis
    data.tangentBasis data.tangentBasis_orthonormal data.basisData
    center base hValid]
  rw [← data.immersion_fderiv_eq_tangentSynthesis base]
  rfl

/-- Audit boundary after extracting fixed-chart Janus coefficients from actual
smooth maps. -/
structure EuclideanImmersionConnectionJetExtractionStatus where
  smoothImmersionSupplied : Prop
  smoothGaugePotentialSupplied : Prop
  firstDerivativeExtracted : Prop
  rawSecondDerivativeExtracted : Prop
  rawSecondDerivativeSmooth : Prop
  rawSecondDerivativeSymmetric : Prop
  gaugeDerivativeExtracted : Prop
  gaugeDerivativeSmooth : Prop
  projectedTangentDerivativeIdentified : Prop
  globalAmbientJetInterfaceInstantiated : Prop
  globalPhysicalOperatorSmooth : Prop
  ambientAndSourceConnectionsDerivedFromMetrics : Prop
  globalSpinCConnectionPotentialConstructed : Prop

def euclideanImmersionConnectionJetExtractionClosed
    (s : EuclideanImmersionConnectionJetExtractionStatus) : Prop :=
  s.smoothImmersionSupplied ∧
  s.smoothGaugePotentialSupplied ∧
  s.firstDerivativeExtracted ∧
  s.rawSecondDerivativeExtracted ∧
  s.rawSecondDerivativeSmooth ∧
  s.rawSecondDerivativeSymmetric ∧
  s.gaugeDerivativeExtracted ∧
  s.gaugeDerivativeSmooth ∧
  s.projectedTangentDerivativeIdentified ∧
  s.globalAmbientJetInterfaceInstantiated ∧
  s.globalPhysicalOperatorSmooth ∧
  s.ambientAndSourceConnectionsDerivedFromMetrics ∧
  s.globalSpinCConnectionPotentialConstructed

theorem missing_metric_connection_extraction_blocks_closure
    (s : EuclideanImmersionConnectionJetExtractionStatus)
    (hMissing : Not s.ambientAndSourceConnectionsDerivedFromMetrics) :
    Not (euclideanImmersionConnectionJetExtractionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusEuclideanImmersionConnectionJetExtraction
end JanusFormal
