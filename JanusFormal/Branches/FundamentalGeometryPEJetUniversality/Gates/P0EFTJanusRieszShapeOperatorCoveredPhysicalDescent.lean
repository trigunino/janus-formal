import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorPhysicalRealizationAtlas

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorCoveredPhysicalDescent

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorPhysicalRealizationAtlas

universe u v w x

variable {Base : Type u} {Ambient : Type v} {PhysicalOperator : Type w}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Pointwise normal bases, local coordinate operators, and their common physical
realization packaged into one descent datum. -/
structure CoveredPhysicalRieszData where
  basisData : PointwiseNormalBasisData Base Ambient ι κ
  physicalOperator : Base → PhysicalOperator
  localOperator : Base → Base → PhysicalOperator
  realizes :
    ∀ center base,
      projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base →
      localOperator center base = physicalOperator base

/-- The coordinate expressions of covered physical Riesz data form a physical
realization family. -/
def CoveredPhysicalRieszData.toPhysicalRealizationData
    (data : CoveredPhysicalRieszData
      (Base := Base) (Ambient := Ambient) (PhysicalOperator := PhysicalOperator)
      (ι := ι) (κ := κ)) :
    PhysicalRealizationData Base Base PhysicalOperator where
  valid := projectedSeedChartValid data.basisData.tangentFrame
    (pointwiseNormalSeedCharts data.basisData)
  physicalOperator := data.physicalOperator
  localOperator := data.localOperator
  realizes := data.realizes

/-- Pointwise normal bases provide the cover required for physical descent. -/
theorem CoveredPhysicalRieszData.cover
    (data : CoveredPhysicalRieszData
      (Base := Base) (Ambient := Ambient) (PhysicalOperator := PhysicalOperator)
      (ι := ι) (κ := κ)) :
    ∀ base, ∃ center,
      data.toPhysicalRealizationData.valid center base := by
  exact pointwiseNormalSeedCharts_cover data.basisData

/-- Validity of every chart persists locally. -/
theorem CoveredPhysicalRieszData.valid_eventually
    (data : CoveredPhysicalRieszData
      (Base := Base) (Ambient := Ambient) (PhysicalOperator := PhysicalOperator)
      (ι := ι) (κ := κ)) :
    ∀ center base,
      data.toPhysicalRealizationData.valid center base →
      ∀ᶠ nearby in 𝓝 base,
        data.toPhysicalRealizationData.valid center nearby := by
  intro center base hValid
  exact projectedSeedChartValid_eventually
    data.basisData.tangentFrame
    (pointwiseNormalSeedCharts data.basisData)
    data.basisData.tangent_contDiff center base hValid

/-- Local operators automatically agree on chart overlaps because they realize
one physical operator. -/
theorem CoveredPhysicalRieszData.overlapCompatible
    (data : CoveredPhysicalRieszData
      (Base := Base) (Ambient := Ambient) (PhysicalOperator := PhysicalOperator)
      (ι := ι) (κ := κ))
    (first second base : Base)
    (hFirst : data.toPhysicalRealizationData.valid first base)
    (hSecond : data.toPhysicalRealizationData.valid second base) :
    data.localOperator first base = data.localOperator second base := by
  exact data.toPhysicalRealizationData.overlapCompatible
    first second base hFirst hSecond

/-- The globally descended operator is exactly the physical Riesz family. -/
theorem descendedOperator_eq_physical
    {TangentModel NormalModel : Type x}
    (data : CoveredPhysicalRieszData
      (Base := Base) (Ambient := Ambient) (PhysicalOperator := PhysicalOperator)
      (ι := ι) (κ := κ)) :
    P0EFTJanusRieszShapeOperatorMetricAtlasInterface.descendedMetricOperator
      (metricAtlasOfPhysicalRealization
        (TangentModel := TangentModel) (NormalModel := NormalModel)
        data.toPhysicalRealizationData data.cover data.valid_eventually) =
      data.physicalOperator := by
  exact descendedMetricOperator_eq_physicalOperator
    (TangentModel := TangentModel) (NormalModel := NormalModel)
    data.toPhysicalRealizationData data.cover data.valid_eventually

/-- Smooth local Riesz expressions imply smoothness of the physical family. -/
theorem physicalOperator_contDiff
    {F : Type w} {TangentModel NormalModel : Type x}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (data : CoveredPhysicalRieszData
      (Base := Base) (Ambient := Ambient) (PhysicalOperator := F)
      (ι := ι) (κ := κ))
    (hLocalSmooth : ∀ center, ContDiff ℝ ∞ (data.localOperator center)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  exact physicalOperator_contDiff_of_local
    (TangentModel := TangentModel) (NormalModel := NormalModel)
    data.toPhysicalRealizationData data.cover data.valid_eventually hLocalSmooth

/-- The remaining Janus-specific obligations after abstract covered descent. -/
structure CoveredPhysicalRieszStatus where
  pointwiseNormalBasesConstructed : Prop
  localRieszExpressionsConstructed : Prop
  physicalRealizationIdentityProved : Prop
  localSmoothnessProved : Prop
  globalPhysicalRieszFamilyIdentified : Prop
  globalSmoothnessProved : Prop
  instantiatedOnStructuredJetBase : Prop

/-- Full closure of the covered physical Riesz stage. -/
def coveredPhysicalRieszClosed (s : CoveredPhysicalRieszStatus) : Prop :=
  s.pointwiseNormalBasesConstructed ∧
  s.localRieszExpressionsConstructed ∧
  s.physicalRealizationIdentityProved ∧
  s.localSmoothnessProved ∧
  s.globalPhysicalRieszFamilyIdentified ∧
  s.globalSmoothnessProved ∧
  s.instantiatedOnStructuredJetBase

/-- Abstract covered descent still does not construct the structured-jet
instance itself. -/
theorem missing_structured_jet_instance_blocks_closure
    (s : CoveredPhysicalRieszStatus)
    (hMissing : Not s.instantiatedOnStructuredJetBase) :
    Not (coveredPhysicalRieszClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorCoveredPhysicalDescent
end JanusFormal
