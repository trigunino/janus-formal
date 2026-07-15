import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedNormalCoefficientOverlap
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorMetricAtlasInterface

namespace JanusFormal
namespace P0EFTJanusProjectedSeedAmbientJetDescent

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
open P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusConnectionCorrectedActualJetBridge
open P0EFTJanusProjectedSeedSmoothCoefficientTransport
open P0EFTJanusProjectedSeedNormalCoefficientOverlap
open P0EFTJanusRieszShapeOperatorMetricAtlasInterface

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

/-- On a valid projected-seed chart, the packaged tangent isometry is exactly
its center-independent continuous synthesis map. -/
theorem projectedSeedChartTangentDerivativeCLM_eq_synthesis
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
        basisData center base =
      tangentFrameSynthesisCLM tangentBasis basisData base := by
  unfold projectedSeedChartTangentDerivativeCLM
  unfold pointwiseBasisSmoothTangentFrameFamilyOn
  exact synthesizedIsometryValue_toContinuousLinearMap
    ({ coordinateBasis := tangentBasis
       coordinateBasis_orthonormal := hTangentBasis
       vector := basisData.tangentFrame
       vector_orthonormal := by
         intro point hPoint
         exact basisData.tangent_orthonormal point
       synthesis := tangentFrameSynthesisCLM tangentBasis basisData
       synthesis_basis := tangentFrameSynthesisCLM_basis
         tangentBasis basisData
       synthesis_contDiffOn :=
         (tangentFrameSynthesisCLM_contDiff
           tangentBasis basisData).contDiffOn
       fallback := tangentFrameFallback tangentBasis
         hTangentBasis basisData center } :
      OrthonormalFrameSynthesisOn
        (Base := Base) (Model := Tangent) (Ambient := Ambient) (κ := ι)
        {point | projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center point})
    base hValid

/-- The tangent derivative used by two valid point-centered charts is the same
on their overlap. -/
theorem projectedSeedChartTangentDerivativeCLM_center_independent
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (firstCenter secondCenter base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) firstCenter base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) secondCenter base) :
    projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
        basisData firstCenter base =
      projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
        basisData secondCenter base := by
  calc
    projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
        basisData firstCenter base =
      tangentFrameSynthesisCLM tangentBasis basisData base :=
        projectedSeedChartTangentDerivativeCLM_eq_synthesis
          tangentBasis hTangentBasis basisData firstCenter base hFirst
    _ = projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
        basisData secondCenter base :=
      (projectedSeedChartTangentDerivativeCLM_eq_synthesis
        tangentBasis hTangentBasis basisData secondCenter base hSecond).symm

/-- Global fixed-space ambient jet coefficients. Restricting these globally
smooth fields to each projected-seed chart yields the local data constructed in
the preceding gate. -/
structure ProjectedSeedGlobalAmbientJetData where
  rawSecond : Base → ContinuousAmbientQuadratic
    (Tangent := Tangent) (Ambient := Ambient)
  ambientConnection : Base → ContinuousAmbientQuadratic
    (Tangent := Tangent) (Ambient := Ambient)
  sourceConnection : Base → ContinuousTangentialQuadratic Tangent
  connectionValue : Base → ContinuousConnectionValue Tangent
  connectionDerivative : Base → ContinuousConnectionDerivative Tangent
  physicalNormalAmbient : Base → Ambient
  rawSecond_contDiff : ContDiff ℝ ∞ rawSecond
  ambientConnection_contDiff : ContDiff ℝ ∞ ambientConnection
  sourceConnection_contDiff : ContDiff ℝ ∞ sourceConnection
  connectionValue_contDiff : ContDiff ℝ ∞ connectionValue
  connectionDerivative_contDiff : ContDiff ℝ ∞ connectionDerivative
  physicalNormalAmbient_contDiff : ContDiff ℝ ∞ physicalNormalAmbient
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

/-- Restrict global ambient jet data to one projected-seed chart. -/
def ProjectedSeedGlobalAmbientJetData.toChartData
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    ProjectedSeedSmoothAmbientJetFamilyOn tangentBasis hTangentBasis
      normalBasis hNormalBasis basisData center where
  rawSecond := data.rawSecond
  ambientConnection := data.ambientConnection
  sourceConnection := data.sourceConnection
  connectionValue := data.connectionValue
  connectionDerivative := data.connectionDerivative
  physicalNormalAmbient := data.physicalNormalAmbient
  rawSecond_contDiffOn := data.rawSecond_contDiff.contDiffOn
  ambientConnection_contDiffOn := data.ambientConnection_contDiff.contDiffOn
  sourceConnection_contDiffOn := data.sourceConnection_contDiff.contDiffOn
  connectionValue_contDiffOn := data.connectionValue_contDiff.contDiffOn
  connectionDerivative_contDiffOn := data.connectionDerivative_contDiff.contDiffOn
  physicalNormalAmbient_contDiffOn :=
    data.physicalNormalAmbient_contDiff.contDiffOn
  rawSecond_symmetric := data.rawSecond_symmetric
  ambientConnection_symmetric := data.ambientConnection_symmetric
  sourceConnection_symmetric := data.sourceConnection_symmetric

/-- Center-independent ambient corrected second derivative expressed with the
canonical global tangent synthesis. -/
def ProjectedSeedGlobalAmbientJetData.correctedAmbientSecondDerivative
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) : ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) :=
  projectedSeedAmbientCovariantSecondDerivative
    (tangentFrameSynthesisCLM tangentBasis basisData base)
    (data.rawSecond base) (data.ambientConnection base)
    (data.sourceConnection base)

/-- Every valid chart computes the canonical center-independent corrected
ambient coefficient. -/
theorem ProjectedSeedGlobalAmbientJetData.chart_corrected_eq_global
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData center).correctedAmbientSecondDerivative base =
      data.correctedAmbientSecondDerivative tangentBasis basisData base := by
  change projectedSeedAmbientCovariantSecondDerivative
      (projectedSeedChartTangentDerivativeCLM tangentBasis hTangentBasis
        basisData center base)
      (data.rawSecond base) (data.ambientConnection base)
      (data.sourceConnection base) =
    projectedSeedAmbientCovariantSecondDerivative
      (tangentFrameSynthesisCLM tangentBasis basisData base)
      (data.rawSecond base) (data.ambientConnection base)
      (data.sourceConnection base)
  rw [projectedSeedChartTangentDerivativeCLM_eq_synthesis
    tangentBasis hTangentBasis basisData center base hValid]

/-- Corrected ambient coefficients agree on every projected-seed overlap. -/
theorem ProjectedSeedGlobalAmbientJetData.chart_corrected_overlap
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (firstCenter secondCenter base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) firstCenter base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) secondCenter base) :
    (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData firstCenter).correctedAmbientSecondDerivative base =
      (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
        basisData secondCenter).correctedAmbientSecondDerivative base := by
  calc
    (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData firstCenter).correctedAmbientSecondDerivative base =
        data.correctedAmbientSecondDerivative tangentBasis basisData base :=
      data.chart_corrected_eq_global tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData firstCenter base hFirst
    _ = (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData secondCenter).correctedAmbientSecondDerivative base :=
      (data.chart_corrected_eq_global tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData secondCenter base hSecond).symm

/-- The physical Riesz operator computed by two chart restrictions is identical
on their overlap. -/
theorem ProjectedSeedGlobalAmbientJetData.chart_physicalOperator_overlap
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (firstCenter secondCenter base : Base)
    (hFirst : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) firstCenter base)
    (hSecond : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) secondCenter base) :
    (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData firstCenter).physicalOperator base =
      (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
        basisData secondCenter).physicalOperator base := by
  unfold ProjectedSeedSmoothAmbientJetFamilyOn.physicalOperator
  unfold ProjectedSeedSmoothAmbientJetFamilyOn.normalQuadratic
  unfold ProjectedSeedSmoothAmbientJetFamilyOn.physicalNormal
  rw [data.chart_corrected_overlap tangentBasis hTangentBasis normalBasis
    hNormalBasis basisData firstCenter secondCenter base hFirst hSecond]
  exact projectedSeedRieszOperator_normalChart_independent normalBasis
    hNormalBasis basisData hDimension firstCenter secondCenter base
    hFirst hSecond
    ((data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData secondCenter).correctedAmbientSecondDerivative base)
    (data.physicalNormalAmbient base)

/-- Local physical operator indexed by the point-centered chart. -/
def ProjectedSeedGlobalAmbientJetData.localPhysicalOperator
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ) :
    Base → Base → Tangent →L[ℝ] Tangent :=
  fun center base =>
    (data.toChartData tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData center).physicalOperator base

/-- Local physical operators are compatible on all overlaps. -/
theorem ProjectedSeedGlobalAmbientJetData.localPhysicalOperator_overlap
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    ∀ firstCenter secondCenter base,
      projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) firstCenter base →
      projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) secondCenter base →
      data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
          hNormalBasis basisData firstCenter base =
        data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
          hNormalBasis basisData secondCenter base := by
  intro firstCenter secondCenter base hFirst hSecond
  exact data.chart_physicalOperator_overlap tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData hDimension firstCenter secondCenter
    base hFirst hSecond

/-- Each local representative is smooth on its own projected-seed domain. -/
theorem ProjectedSeedGlobalAmbientJetData.localPhysicalOperator_contDiffOn
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    ContDiffOn ℝ ∞
      (data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData center)
      (projectedSeedCoefficientDomain basisData center) := by
  exact (data.toChartData tangentBasis hTangentBasis normalBasis
    hNormalBasis basisData center).physicalOperator_contDiffOn

/-- Concrete metric atlas obtained directly from globally smooth ambient jet
coefficients and the pointwise projected-seed cover. -/
def ProjectedSeedGlobalAmbientJetData.metricAtlas
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    MetricFiberAtlas Base Base Tangent Normal (Tangent →L[ℝ] Tangent) :=
  metricAtlasOfPointwiseNormalBases basisData
    (data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
      hNormalBasis basisData)
    (data.localPhysicalOperator_overlap tangentBasis hTangentBasis normalBasis
      hNormalBasis basisData hDimension)

/-- Global physical operator selected by compatible metric-atlas descent. -/
def ProjectedSeedGlobalAmbientJetData.descendedPhysicalOperator
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient) :
    Base → Tangent →L[ℝ] Tangent :=
  descendedMetricOperator
    (data.metricAtlas tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData hDimension)

/-- Every valid projected-seed chart computes the descended global operator. -/
theorem ProjectedSeedGlobalAmbientJetData.localPhysicalOperator_eq_descended
    (data : ProjectedSeedGlobalAmbientJetData
      (Base := Base) (Tangent := Tangent) (Ambient := Ambient))
    (tangentBasis : Basis ι ℝ Tangent)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ Normal)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    data.localPhysicalOperator tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData center base =
      data.descendedPhysicalOperator tangentBasis hTangentBasis normalBasis
        hNormalBasis basisData hDimension base := by
  exact localOperator_eq_descendedMetricOperator
    (data.metricAtlas tangentBasis hTangentBasis normalBasis hNormalBasis
      basisData hDimension) center base hValid

/-- Audit ledger after constructing the actual projected-seed atlas from global
ambient jet coefficients. -/
structure ProjectedSeedAmbientJetDescentStatus where
  globalAmbientJetFamilySupplied : Prop
  chartRestrictionsConstructed : Prop
  tangentDerivativeCenterIndependenceProved : Prop
  correctedAmbientCoefficientOverlapProved : Prop
  normalCoefficientOverlapInherited : Prop
  physicalRieszOverlapProved : Prop
  localChartSmoothnessProved : Prop
  metricAtlasConstructed : Prop
  globalOperatorDescended : Prop
  globalOperatorSmoothnessProved : Prop
  genuineManifoldSpinCJetFamilyConstructed : Prop

def projectedSeedAmbientJetDescentClosed
    (s : ProjectedSeedAmbientJetDescentStatus) : Prop :=
  s.globalAmbientJetFamilySupplied ∧
  s.chartRestrictionsConstructed ∧
  s.tangentDerivativeCenterIndependenceProved ∧
  s.correctedAmbientCoefficientOverlapProved ∧
  s.normalCoefficientOverlapInherited ∧
  s.physicalRieszOverlapProved ∧
  s.localChartSmoothnessProved ∧
  s.metricAtlasConstructed ∧
  s.globalOperatorDescended ∧
  s.globalOperatorSmoothnessProved ∧
  s.genuineManifoldSpinCJetFamilyConstructed

theorem missing_global_smoothness_blocks_descent_closure
    (s : ProjectedSeedAmbientJetDescentStatus)
    (hMissing : Not s.globalOperatorSmoothnessProved) :
    Not (projectedSeedAmbientJetDescentClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusProjectedSeedAmbientJetDescent
end JanusFormal
