import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorOpenCanonicalTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging

universe u v w x y

variable {Base : Type w} {Model : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Model] [InnerProductSpace ℝ Model]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Model]

variable {κ : Type x} [Fintype κ]

def basisRankOneSynthesisCLM
    (coordinateBasis : Basis κ ℝ Model) (k : κ) :
    Ambient →L[ℝ] Model →L[ℝ] Ambient :=
  (ContinuousLinearMap.smulRightL ℝ Model Ambient)
    (coordinateBasis.coord k).toContinuousLinearMap

def projectedSeedSynthesisSumCLM
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base) : Model →L[ℝ] Ambient :=
  ∑ k, basisRankOneSynthesisCLM coordinateBasis k
    (projectedSeedNormalFrame tangentFrame charts chart k base)

@[simp]
theorem projectedSeedSynthesisSumCLM_basis
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base) (k : κ) :
    projectedSeedSynthesisSumCLM coordinateBasis tangentFrame charts chart base
        (coordinateBasis k) =
      projectedSeedNormalFrame tangentFrame charts chart k base := by
  classical
  unfold projectedSeedSynthesisSumCLM basisRankOneSynthesisCLM
  rw [Fintype.sum_eq_single k]
  · simp
  · intro j hj hne
    simp [hne]

theorem projectedSeedSynthesisCLM_eq_sum
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (chart : Chart) (base : Base) :
    projectedSeedSynthesisCLM coordinateBasis tangentFrame charts chart base =
      projectedSeedSynthesisSumCLM coordinateBasis tangentFrame charts chart base := by
  apply ContinuousLinearMap.ext
  intro vector
  conv_lhs => rw [← coordinateBasis.sum_equivFun vector]
  conv_rhs => rw [← coordinateBasis.sum_equivFun vector]
  simp only [map_sum, map_smul]
  simp

theorem projectedSeedSynthesisCLM_contDiffOn
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (chart : Chart) :
    ContDiffOn ℝ ∞
      (projectedSeedSynthesisCLM coordinateBasis tangentFrame charts chart)
      {base | projectedSeedChartValid tangentFrame charts chart base} := by
  have hSum : ContDiffOn ℝ ∞
      (projectedSeedSynthesisSumCLM coordinateBasis tangentFrame charts chart)
      {base | projectedSeedChartValid tangentFrame charts chart base} := by
    classical
    unfold projectedSeedSynthesisSumCLM
    apply ContDiffOn.sum
    intro k hk
    exact (basisRankOneSynthesisCLM coordinateBasis k).contDiff.comp_contDiffOn
      (projectedSeedNormalFrame_contDiffOn
        tangentFrame charts hTangent chart k)
  apply hSum.congr
  intro base hValid
  exact projectedSeedSynthesisCLM_eq_sum
    coordinateBasis tangentFrame charts chart base

def projectedSeedSmoothIsometricFrameFamilyOnOfSmooth
    {Chart : Type y} {ι : Type*}
    [Fintype ι] [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (fallback : Model →ₗᵢ[ℝ] Ambient)
    (tangentFrame : ι → Base → Ambient)
    (charts : ProjectedSeedChartFamily Chart Base Ambient κ)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (chart : Chart) :
    SmoothIsometricFrameFamilyOn Base Model Ambient
      {base | projectedSeedChartValid tangentFrame charts chart base} :=
  projectedSeedSmoothIsometricFrameFamilyOn coordinateBasis
    hCoordinateOrthonormal fallback tangentFrame charts chart
    (projectedSeedSynthesisCLM_contDiffOn
      coordinateBasis tangentFrame charts hTangent chart)

def pointwiseNormalBasisFallback
    {ι : Type*}
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) : Model →ₗᵢ[ℝ] Ambient := by
  let synthesis : Model →ₗ[ℝ] Ambient :=
    coordinateBasis.constr ℝ (basisData.normalBasisAt center)
  have hBasisImage :
      synthesis ∘ coordinateBasis = basisData.normalBasisAt center := by
    funext k
    exact coordinateBasis.constr_basis ℝ _ k
  have hImage : Orthonormal ℝ (synthesis ∘ coordinateBasis) := by
    rw [hBasisImage]
    exact basisData.normal_orthonormal center
  exact synthesis.isometryOfOrthonormal hCoordinateOrthonormal hImage

def pointwiseBasisSmoothNormalFrameFamilyOn
    {ι : Type*} [Fintype ι]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    SmoothIsometricFrameFamilyOn Base Model Ambient
      {base | projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base} :=
  projectedSeedSmoothIsometricFrameFamilyOnOfSmooth coordinateBasis
    hCoordinateOrthonormal
    (pointwiseNormalBasisFallback coordinateBasis hCoordinateOrthonormal
      basisData center)
    basisData.tangentFrame (pointwiseNormalSeedCharts basisData)
    basisData.tangent_contDiff center

theorem pointwiseBasisSmoothNormalFrameFamilyOn_range
    {ι : Type*} [Fintype ι]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    normalFrameRange
        ((pointwiseBasisSmoothNormalFrameFamilyOn coordinateBasis
          hCoordinateOrthonormal basisData center).frame base) =
      Submodule.span ℝ
        (Set.range (fun k => projectedSeedNormalFrame
          basisData.tangentFrame (pointwiseNormalSeedCharts basisData)
          center k base)) := by
  exact projectedSeedSmoothIsometricFrameFamilyOn_range coordinateBasis
    hCoordinateOrthonormal
    (pointwiseNormalBasisFallback coordinateBasis hCoordinateOrthonormal
      basisData center)
    basisData.tangentFrame (pointwiseNormalSeedCharts basisData) center
    (projectedSeedSynthesisCLM_contDiffOn coordinateBasis
      basisData.tangentFrame (pointwiseNormalSeedCharts basisData)
      basisData.tangent_contDiff center)
    base hValid

structure ProjectedSeedSynthesisSmoothnessStatus where
  rankOneExpansionConstructed : Prop
  rankOneExpansionEqualsBasisConstruction : Prop
  synthesisContDiffOnProved : Prop
  gramSchmidtIsometricFramePackaged : Prop
  pointwiseBasisFallbackConstructed : Prop
  pointwiseBasisFramePackaged : Prop
  frameRangeIdentified : Prop
  connectedToPhysicalNormalRange : Prop

def projectedSeedSynthesisSmoothnessClosed
    (s : ProjectedSeedSynthesisSmoothnessStatus) : Prop :=
  s.rankOneExpansionConstructed ∧
  s.rankOneExpansionEqualsBasisConstruction ∧
  s.synthesisContDiffOnProved ∧
  s.gramSchmidtIsometricFramePackaged ∧
  s.pointwiseBasisFallbackConstructed ∧
  s.pointwiseBasisFramePackaged ∧
  s.frameRangeIdentified ∧
  s.connectedToPhysicalNormalRange

theorem missing_physical_range_identification_blocks_closure
    (s : ProjectedSeedSynthesisSmoothnessStatus)
    (hMissing : Not s.connectedToPhysicalNormalRange) :
    Not (projectedSeedSynthesisSmoothnessClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
end JanusFormal
