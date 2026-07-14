import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedOpenAtlas

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorPointwiseBasisOpenDescent

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedOpenAtlas

universe u v w x

variable {Base : Type u} {Ambient : Type v} {PhysicalOperator : Type w}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [NormedAddCommGroup PhysicalOperator]
variable [NormedSpace ℝ PhysicalOperator]

variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Open Riesz descent data specialized to the canonical cover by charts centered
at pointwise normal bases. -/
structure PointwiseBasisOpenRieszData where
  basisData : PointwiseNormalBasisData Base Ambient ι κ
  physicalOperator : Base → PhysicalOperator
  localOperator : Base → Base → PhysicalOperator
  local_realizes :
    ∀ center base,
      projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base →
      localOperator center base = physicalOperator base
  local_contDiffOn :
    ∀ center,
      ContDiffOn ℝ ∞ (localOperator center)
        {base | projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center base}

/-- The pointwise-basis data defines an open metric atlas. -/
def PointwiseBasisOpenRieszData.openMetricAtlas
    {TangentModel NormalModel : Type x}
    (data : PointwiseBasisOpenRieszData
      (Base := Base) (Ambient := Ambient)
      (PhysicalOperator := PhysicalOperator) (ι := ι) (κ := κ)) :
    P0EFTJanusRieszShapeOperatorOpenMetricAtlas.OpenMetricFiberAtlas
      Base Base TangentModel NormalModel PhysicalOperator :=
  openMetricAtlasOfProjectedSeedsPhysical
    data.basisData.tangentFrame
    (pointwiseNormalSeedCharts data.basisData)
    data.basisData.tangent_contDiff
    data.physicalOperator data.localOperator
    (pointwiseNormalSeedCharts_cover data.basisData)
    data.local_realizes data.local_contDiffOn

/-- Every complete pointwise-basis open Riesz package yields a globally smooth
physical operator. -/
theorem PointwiseBasisOpenRieszData.physicalOperator_contDiff
    {TangentModel NormalModel : Type x}
    (data : PointwiseBasisOpenRieszData
      (Base := Base) (Ambient := Ambient)
      (PhysicalOperator := PhysicalOperator) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  exact projectedSeedPhysicalOperator_contDiff
    (TangentModel := TangentModel) (NormalModel := NormalModel)
    data.basisData.tangentFrame
    (pointwiseNormalSeedCharts data.basisData)
    data.basisData.tangent_contDiff
    data.physicalOperator data.localOperator
    (pointwiseNormalSeedCharts_cover data.basisData)
    data.local_realizes data.local_contDiffOn

/-- Every local formula agrees with the descended metric-atlas operator on its
open chart domain. -/
theorem PointwiseBasisOpenRieszData.local_eq_descended
    {TangentModel NormalModel : Type x}
    (data : PointwiseBasisOpenRieszData
      (Base := Base) (Ambient := Ambient)
      (PhysicalOperator := PhysicalOperator) (ι := ι) (κ := κ))
    (center base : Base)
    (hValid : projectedSeedChartValid data.basisData.tangentFrame
      (pointwiseNormalSeedCharts data.basisData) center base) :
    data.localOperator center base =
      P0EFTJanusRieszShapeOperatorMetricAtlasInterface.descendedMetricOperator
        data.openMetricAtlas.toMetricFiberAtlas base := by
  exact
    P0EFTJanusRieszShapeOperatorOpenMetricAtlas.localOperator_eq_descended_openMetricOperator
      data.openMetricAtlas center base hValid

/-- Audit boundary after pointwise-basis open descent. -/
structure PointwiseBasisOpenDescentStatus where
  pointwiseNormalBasisCoverConstructed : Prop
  localRieszFormulaConstructed : Prop
  localPhysicalRealizationProved : Prop
  localContDiffOnProved : Prop
  openMetricAtlasConstructed : Prop
  globalPhysicalRieszSmooth : Prop
  instantiatedOnJanusJetBase : Prop

/-- Closure of pointwise-basis open descent. -/
def pointwiseBasisOpenDescentClosed
    (s : PointwiseBasisOpenDescentStatus) : Prop :=
  s.pointwiseNormalBasisCoverConstructed ∧
  s.localRieszFormulaConstructed ∧
  s.localPhysicalRealizationProved ∧
  s.localContDiffOnProved ∧
  s.openMetricAtlasConstructed ∧
  s.globalPhysicalRieszSmooth ∧
  s.instantiatedOnJanusJetBase

/-- The only remaining non-formal step is the actual Janus-jet instantiation. -/
theorem missing_janus_instance_blocks_pointwise_basis_open_descent
    (s : PointwiseBasisOpenDescentStatus)
    (hMissing : Not s.instantiatedOnJanusJetBase) :
    Not (pointwiseBasisOpenDescentClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorPointwiseBasisOpenDescent
end JanusFormal
