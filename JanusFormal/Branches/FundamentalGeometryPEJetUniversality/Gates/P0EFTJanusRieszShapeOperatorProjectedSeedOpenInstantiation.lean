import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenMovingFrame
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorPointwiseBasisOpenDescent

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedOpenInstantiation

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorOpenMovingFrame
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorPointwiseBasisOpenDescent

universe u v w x y

variable {Base : Type w} {Ambient : Type x}
variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent] [FiniteDimensional ℝ Normal]

variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Validity domain of the pointwise-basis chart centered at `center`. -/
def pointwiseBasisChartDomain
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) : Set Base :=
  {base | projectedSeedChartValid basisData.tangentFrame
    (pointwiseNormalSeedCharts basisData) center base}

/-- Chartwise open moving-frame data sufficient to construct a local Riesz
formula, prove its smoothness on the chart, and identify it with one global
physical operator. -/
structure ProjectedSeedOpenRieszInstantiationData where
  basisData : PointwiseNormalBasisData Base Ambient ι κ
  physicalOperator : Base → Tangent →L[ℝ] Tangent
  referenceTangentFrame : ∀ center,
    SmoothOrthogonalFrameFamilyOn Base Tangent
      (pointwiseBasisChartDomain basisData center)
  referenceNormalFrame : ∀ center,
    SmoothOrthogonalFrameFamilyOn Base Normal
      (pointwiseBasisChartDomain basisData center)
  transition : ∀ center,
    SmoothResidualOrthogonalFrameFamilyOn Base Tangent Normal
      (pointwiseBasisChartDomain basisData center)
  referenceForm : ∀ center,
    Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)
  physicalNormal : Base → Normal
  referenceForm_contDiffOn : ∀ center,
    ContDiffOn ℝ ∞ (referenceForm center)
      (pointwiseBasisChartDomain basisData center)
  physicalNormal_contDiffOn : ∀ center,
    ContDiffOn ℝ ∞ physicalNormal
      (pointwiseBasisChartDomain basisData center)
  reference_realizes_physical :
    ∀ center base,
      base ∈ pointwiseBasisChartDomain basisData center →
      geometricRieszShapeFamilyOn
          (referenceTangentFrame center)
          (referenceNormalFrame center)
          (referenceForm center) physicalNormal base =
        physicalOperator base

/-- Local Riesz formula in the projected-seed chart centered at `center`. -/
def ProjectedSeedOpenRieszInstantiationData.localOperator
    (data : ProjectedSeedOpenRieszInstantiationData
      (Base := Base) (Ambient := Ambient)
      (Tangent := Tangent) (Normal := Normal) (ι := ι) (κ := κ))
    (center : Base) : Base → Tangent →L[ℝ] Tangent :=
  geometricRieszShapeFamilyOn
    (reparametrizeSmoothOrthogonalFrameFamilyOn
      (data.referenceTangentFrame center) (data.transition center).tangent)
    (reparametrizeSmoothOrthogonalFrameFamilyOn
      (data.referenceNormalFrame center) (data.transition center).normal)
    (transformContinuousIIOnOpenOverlap
      (data.transition center) (data.referenceForm center))
    data.physicalNormal

/-- Each chartwise formula realizes the same physical operator. -/
theorem ProjectedSeedOpenRieszInstantiationData.localOperator_realizes
    (data : ProjectedSeedOpenRieszInstantiationData
      (Base := Base) (Ambient := Ambient)
      (Tangent := Tangent) (Normal := Normal) (ι := ι) (κ := κ))
    (center base : Base)
    (hValid : base ∈ pointwiseBasisChartDomain data.basisData center) :
    data.localOperator center base = data.physicalOperator base := by
  have hInvariant := congrFun
    (geometricRieszShapeFamilyOn_variable_coordinate_invariant
      (data.referenceTangentFrame center)
      (data.referenceNormalFrame center)
      (data.transition center)
      (data.referenceForm center) data.physicalNormal) base
  exact hInvariant.trans
    (data.reference_realizes_physical center base hValid)

/-- Each chartwise formula is smooth on its own open projected-seed domain. -/
theorem ProjectedSeedOpenRieszInstantiationData.localOperator_contDiffOn
    (data : ProjectedSeedOpenRieszInstantiationData
      (Base := Base) (Ambient := Ambient)
      (Tangent := Tangent) (Normal := Normal) (ι := ι) (κ := κ))
    (center : Base) :
    ContDiffOn ℝ ∞ (data.localOperator center)
      (pointwiseBasisChartDomain data.basisData center) := by
  exact geometricRieszShapeFamilyOn_variable_overlap_contDiffOn
    (data.referenceTangentFrame center)
    (data.referenceNormalFrame center)
    (data.transition center)
    (data.referenceForm center) data.physicalNormal
    (data.referenceForm_contDiffOn center)
    (data.physicalNormal_contDiffOn center)

/-- Package the chartwise overlap construction as pointwise-basis open descent
data. -/
def ProjectedSeedOpenRieszInstantiationData.toPointwiseBasisOpenRieszData
    (data : ProjectedSeedOpenRieszInstantiationData
      (Base := Base) (Ambient := Ambient)
      (Tangent := Tangent) (Normal := Normal) (ι := ι) (κ := κ)) :
    PointwiseBasisOpenRieszData
      (Base := Base) (Ambient := Ambient)
      (PhysicalOperator := Tangent →L[ℝ] Tangent) (ι := ι) (κ := κ) where
  basisData := data.basisData
  physicalOperator := data.physicalOperator
  localOperator := data.localOperator
  local_realizes := by
    intro center base hValid
    exact data.localOperator_realizes center base hValid
  local_contDiffOn := data.localOperator_contDiffOn

/-- The physical Riesz family is globally smooth once the chartwise open moving
frames and reference realization are supplied. -/
theorem ProjectedSeedOpenRieszInstantiationData.physicalOperator_contDiff
    {TangentModel NormalModel : Type y}
    (data : ProjectedSeedOpenRieszInstantiationData
      (Base := Base) (Ambient := Ambient)
      (Tangent := Tangent) (Normal := Normal) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  exact
    PointwiseBasisOpenRieszData.physicalOperator_contDiff
      (TangentModel := TangentModel) (NormalModel := NormalModel)
      data.toPointwiseBasisOpenRieszData

/-- Exact boundary after chartwise open Riesz instantiation. -/
structure ProjectedSeedOpenInstantiationStatus where
  pointwiseBasisCoverConnected : Prop
  openReferenceFramesConstructed : Prop
  openResidualTransitionsConstructed : Prop
  referenceSecondFundamentalFormSmooth : Prop
  physicalNormalSmooth : Prop
  referencePhysicalRealizationProved : Prop
  localRealizationDerived : Prop
  localContDiffOnDerived : Prop
  globalPhysicalRieszSmooth : Prop
  gramSchmidtFramesConnected : Prop

/-- Closure of chartwise open Riesz instantiation. -/
def projectedSeedOpenInstantiationClosed
    (s : ProjectedSeedOpenInstantiationStatus) : Prop :=
  s.pointwiseBasisCoverConnected ∧
  s.openReferenceFramesConstructed ∧
  s.openResidualTransitionsConstructed ∧
  s.referenceSecondFundamentalFormSmooth ∧
  s.physicalNormalSmooth ∧
  s.referencePhysicalRealizationProved ∧
  s.localRealizationDerived ∧
  s.localContDiffOnDerived ∧
  s.globalPhysicalRieszSmooth ∧
  s.gramSchmidtFramesConnected

/-- The remaining geometric step is the actual Gram--Schmidt frame connection. -/
theorem missing_gramSchmidt_connection_blocks_open_instantiation
    (s : ProjectedSeedOpenInstantiationStatus)
    (hMissing : Not s.gramSchmidtFramesConnected) :
    Not (projectedSeedOpenInstantiationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorProjectedSeedOpenInstantiation
end JanusFormal
