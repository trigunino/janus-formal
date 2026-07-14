import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness

set_option autoImplicit false

noncomputable section

open Set
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

/-- Rank-one synthesis operator associated with one coordinate functional. -/
def basisRankOneSynthesisCLM
    (coordinateBasis : Basis κ ℝ Model) (k : κ) :
    Ambient →L[ℝ] Model →L[ℝ] Ambient :=
  (ContinuousLinearMap.smulRightL ℝ Model Ambient)
    (coordinateBasis.coord k).toContinuousLinearMap

/-- Finite rank-one expansion of a basis synthesis operator. -/
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
  change
    (∑ j, coordinateBasis.coord j (coordinateBasis k) •
      projectedSeedNormalFrame tangentFrame charts chart j base) =
      projectedSeedNormalFrame tangentFrame charts chart k base
  simp

/-- The `Basis.constr` synthesis map is exactly its finite rank-one expansion. -/
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

/-- Smoothness of every Gram--Schmidt vector implies smoothness of the finite
basis synthesis operator on the projected-seed chart domain. -/
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
  exact (projectedSeedSynthesisCLM_eq_sum
    coordinateBasis tangentFrame charts chart base).symm

/-- Projected-seed Gram--Schmidt frames package automatically as smooth
open-domain isometric frame families. -/
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

/-- A pointwise normal orthonormal family supplies the fallback isometric
embedding for its centered chart. -/
def pointwiseNormalBasisFallback
    {ι : Type*}
    (coordinateBasis : Basis κ ℝ Model)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) : Model →ₗᵢ[ℝ] Ambient := by
  let synthesis : Model →ₗ[ℝ] Ambient :=
    coordinateBasis.constr ℝ (basisData.normalBasisAt center)
  have hImage : Orthonormal ℝ (synthesis ∘ coordinateBasis) := by
    simpa [synthesis, Function.comp_def] using
      basisData.normal_orthonormal center
  exact synthesis.isometryOfOrthonormal hCoordinateOrthonormal hImage

/-- Complete smooth normal-frame packaging on the pointwise-basis chart centered
at `center`. -/
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

/-- The packaged pointwise-basis frame has the expected Gram--Schmidt ambient
range on every valid point of its chart. -/
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

/-- Exact closure status after finite-sum synthesis smoothness. -/
structure ProjectedSeedSynthesisSmoothnessStatus where
  rankOneExpansionConstructed : Prop
  rankOneExpansionEqualsBasisConstruction : Prop
  synthesisContDiffOnProved : Prop
  gramSchmidtIsometricFramePackaged : Prop
  pointwiseBasisFallbackConstructed : Prop
  pointwiseBasisFramePackaged : Prop
  frameRangeIdentified : Prop
  connectedToPhysicalNormalRange : Prop

/-- Closure of projected-seed synthesis smoothness. -/
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

/-- The remaining geometric statement is equality with the actual physical
normal range, not smoothness or isometric frame packaging. -/
theorem missing_physical_range_identification_blocks_closure
    (s : ProjectedSeedSynthesisSmoothnessStatus)
    (hMissing : Not s.connectedToPhysicalNormalRange) :
    Not (projectedSeedSynthesisSmoothnessClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
end JanusFormal
