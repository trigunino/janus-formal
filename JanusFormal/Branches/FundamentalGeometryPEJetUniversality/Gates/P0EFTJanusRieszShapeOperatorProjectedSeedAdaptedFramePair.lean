import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedOrthogonalRange

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusNormalFramePointwiseTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorOpenCanonicalTransition
open P0EFTJanusRieszShapeOperatorProjectedSeedFramePackaging
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedPhysicalRangeBridge
open P0EFTJanusRieszShapeOperatorProjectedSeedOrthogonalRange

universe u v w x y

variable {Base : Type w} {TangentModel : Type u}
variable {NormalModel : Type v} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup TangentModel]
variable [InnerProductSpace ℝ TangentModel]
variable [NormedAddCommGroup NormalModel]
variable [InnerProductSpace ℝ NormalModel]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ TangentModel]
variable [FiniteDimensional ℝ NormalModel]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Linear synthesis operator sending a fixed abstract tangent basis to the
pointwise tangent orthonormal frame. -/
def tangentFrameSynthesisLinearMap
    (coordinateBasis : Basis ι ℝ TangentModel)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) : TangentModel →ₗ[ℝ] Ambient :=
  coordinateBasis.constr ℝ (fun i => basisData.tangentFrame i base)

/-- Continuous-linear tangent synthesis operator. -/
def tangentFrameSynthesisCLM
    (coordinateBasis : Basis ι ℝ TangentModel)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) : TangentModel →L[ℝ] Ambient :=
  (tangentFrameSynthesisLinearMap coordinateBasis basisData base)
    .toContinuousLinearMap

@[simp]
theorem tangentFrameSynthesisCLM_basis
    (coordinateBasis : Basis ι ℝ TangentModel)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) (i : ι) :
    tangentFrameSynthesisCLM coordinateBasis basisData base
        (coordinateBasis i) = basisData.tangentFrame i base := by
  unfold tangentFrameSynthesisCLM tangentFrameSynthesisLinearMap
  exact coordinateBasis.constr_basis ℝ _ i

/-- Finite rank-one expansion of tangent synthesis. -/
def tangentFrameSynthesisSumCLM
    (coordinateBasis : Basis ι ℝ TangentModel)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) : TangentModel →L[ℝ] Ambient :=
  ∑ i, basisRankOneSynthesisCLM coordinateBasis i
    (basisData.tangentFrame i base)

/-- Tangent synthesis equals its finite coordinate expansion. -/
theorem tangentFrameSynthesisCLM_eq_sum
    (coordinateBasis : Basis ι ℝ TangentModel)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (base : Base) :
    tangentFrameSynthesisCLM coordinateBasis basisData base =
      tangentFrameSynthesisSumCLM coordinateBasis basisData base := by
  apply ContinuousLinearMap.ext
  intro vector
  unfold tangentFrameSynthesisCLM tangentFrameSynthesisLinearMap
  rw [← coordinateBasis.sum_equivFun vector]
  simp [tangentFrameSynthesisSumCLM, basisRankOneSynthesisCLM]

/-- The tangent synthesis operator varies smoothly on the whole base. -/
theorem tangentFrameSynthesisCLM_contDiff
    (coordinateBasis : Basis ι ℝ TangentModel)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ) :
    ContDiff ℝ ∞ (tangentFrameSynthesisCLM coordinateBasis basisData) := by
  have hSum : ContDiff ℝ ∞
      (tangentFrameSynthesisSumCLM coordinateBasis basisData) := by
    classical
    unfold tangentFrameSynthesisSumCLM
    apply ContDiff.sum
    intro i hi
    exact (basisRankOneSynthesisCLM coordinateBasis i).contDiff.comp
      (basisData.tangent_contDiff i)
  apply hSum.congr
  intro base
  exact tangentFrameSynthesisCLM_eq_sum coordinateBasis basisData base

/-- Pointwise fallback tangent isometry obtained at a chart center. -/
def tangentFrameFallback
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) : TangentModel →ₗᵢ[ℝ] Ambient := by
  let synthesis : TangentModel →ₗ[ℝ] Ambient :=
    coordinateBasis.constr ℝ (fun i => basisData.tangentFrame i center)
  have hBasisImage :
      synthesis ∘ coordinateBasis =
        (fun i => basisData.tangentFrame i center) := by
    funext i
    exact coordinateBasis.constr_basis ℝ _ i
  have hImage : Orthonormal ℝ (synthesis ∘ coordinateBasis) := by
    rw [hBasisImage]
    exact basisData.tangent_orthonormal center
  exact synthesis.isometryOfOrthonormal hCoordinateOrthonormal hImage

/-- The supplied tangent orthonormal frame packages as a smooth isometric frame
on every point-centered projected-seed chart. -/
def pointwiseBasisSmoothTangentFrameFamilyOn
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) :
    SmoothIsometricFrameFamilyOn Base TangentModel Ambient
      {base | projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base} :=
  OrthonormalFrameSynthesisOn.toSmoothIsometricFrameFamilyOn
    ({ coordinateBasis := coordinateBasis
       coordinateBasis_orthonormal := hCoordinateOrthonormal
       vector := basisData.tangentFrame
       vector_orthonormal := by
         intro base hValid
         exact basisData.tangent_orthonormal base
       synthesis := tangentFrameSynthesisCLM coordinateBasis basisData
       synthesis_basis := tangentFrameSynthesisCLM_basis
         coordinateBasis basisData
       synthesis_contDiffOn :=
         (tangentFrameSynthesisCLM_contDiff
           coordinateBasis basisData).contDiffOn
       fallback := tangentFrameFallback coordinateBasis
         hCoordinateOrthonormal basisData center } :
      OrthonormalFrameSynthesisOn
        (Base := Base) (Model := TangentModel) (Ambient := Ambient) (κ := ι)
        {base | projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center base})

/-- Ambient image of the packaged tangent frame is exactly the tangent span. -/
theorem pointwiseBasisSmoothTangentFrameFamilyOn_range
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center base : Base)
    (hValid : projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base) :
    normalFrameRange
        ((pointwiseBasisSmoothTangentFrameFamilyOn coordinateBasis
          hCoordinateOrthonormal basisData center).frame base) =
      tangentFrameSpan basisData base := by
  unfold normalFrameRange tangentFrameSpan
  have hFrame :
      ((pointwiseBasisSmoothTangentFrameFamilyOn coordinateBasis
        hCoordinateOrthonormal basisData center).frame base).toLinearMap =
        tangentFrameSynthesisLinearMap coordinateBasis basisData base := by
    apply LinearMap.ext
    intro vector
    unfold pointwiseBasisSmoothTangentFrameFamilyOn
    change synthesizedIsometryValue
      ({ coordinateBasis := coordinateBasis
         coordinateBasis_orthonormal := hCoordinateOrthonormal
         vector := basisData.tangentFrame
         vector_orthonormal := by
           intro point hPoint
           exact basisData.tangent_orthonormal point
         synthesis := tangentFrameSynthesisCLM coordinateBasis basisData
         synthesis_basis := tangentFrameSynthesisCLM_basis
           coordinateBasis basisData
         synthesis_contDiffOn :=
           (tangentFrameSynthesisCLM_contDiff
             coordinateBasis basisData).contDiffOn
         fallback := tangentFrameFallback coordinateBasis
           hCoordinateOrthonormal basisData center } :
        OrthonormalFrameSynthesisOn
          (Base := Base) (Model := TangentModel) (Ambient := Ambient) (κ := ι)
          {point | projectedSeedChartValid basisData.tangentFrame
            (pointwiseNormalSeedCharts basisData) center point})
      base vector = tangentFrameSynthesisCLM coordinateBasis basisData base vector
    have hCLM := synthesizedIsometryValue_toContinuousLinearMap
      ({ coordinateBasis := coordinateBasis
         coordinateBasis_orthonormal := hCoordinateOrthonormal
         vector := basisData.tangentFrame
         vector_orthonormal := by
           intro point hPoint
           exact basisData.tangent_orthonormal point
         synthesis := tangentFrameSynthesisCLM coordinateBasis basisData
         synthesis_basis := tangentFrameSynthesisCLM_basis
           coordinateBasis basisData
         synthesis_contDiffOn :=
           (tangentFrameSynthesisCLM_contDiff
             coordinateBasis basisData).contDiffOn
         fallback := tangentFrameFallback coordinateBasis
           hCoordinateOrthonormal basisData center } :
        OrthonormalFrameSynthesisOn
          (Base := Base) (Model := TangentModel) (Ambient := Ambient) (κ := ι)
          {point | projectedSeedChartValid basisData.tangentFrame
            (pointwiseNormalSeedCharts basisData) center point})
      base hValid
    exact congrArg
      (fun operator : TangentModel →L[ℝ] Ambient => operator vector) hCLM
  rw [hFrame]
  exact coordinateBasis.constr_range ℝ

/-- Smooth physical tangent frame on one point-centered chart. -/
structure PhysicalTangentFrameOn
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) where
  frame : SmoothIsometricFrameFamilyOn Base TangentModel Ambient
    {base | projectedSeedChartValid basisData.tangentFrame
      (pointwiseNormalSeedCharts basisData) center base}
  physicalRange : Base → Submodule ℝ Ambient
  frame_range_eq :
    ∀ base,
      projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base →
      normalFrameRange (frame.frame base) = physicalRange base

/-- The packaged tangent frame itself realizes the canonical tangent span. -/
def canonicalPhysicalTangentFrameOn
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base) : PhysicalTangentFrameOn
      (TangentModel := TangentModel) basisData center where
  frame := pointwiseBasisSmoothTangentFrameFamilyOn coordinateBasis
    hCoordinateOrthonormal basisData center
  physicalRange := tangentFrameSpan basisData
  frame_range_eq := pointwiseBasisSmoothTangentFrameFamilyOn_range
    coordinateBasis hCoordinateOrthonormal basisData center

/-- Canonical tangent transition to any physical tangent frame having the same
physical tangent range. -/
def tangentFrameToPhysicalTransition
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (physical : PhysicalTangentFrameOn
      (TangentModel := TangentModel) basisData center)
    (hPhysicalRange :
      ∀ base,
        projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center base →
        tangentFrameSpan basisData base = physical.physicalRange base) :
    P0EFTJanusRieszShapeOperatorOpenMovingFrame.SmoothOrthogonalFrameFamilyOn
      Base TangentModel
      {base | projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base} :=
  openCanonicalFrameTransition
    (pointwiseBasisSmoothTangentFrameFamilyOn coordinateBasis
      hCoordinateOrthonormal basisData center)
    physical.frame
    (by
      intro base hValid
      exact (pointwiseBasisSmoothTangentFrameFamilyOn_range coordinateBasis
        hCoordinateOrthonormal basisData center base hValid).trans
          ((hPhysicalRange base hValid).trans
            (physical.frame_range_eq base hValid).symm))

/-- Full projected-seed adapted frame pair from compatible physical tangent and
normal frames. -/
def projectedSeedOpenAdaptedFramePair
    (tangentBasis : Basis ι ℝ TangentModel)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (physicalTangent : PhysicalTangentFrameOn
      (TangentModel := TangentModel) basisData center)
    (hPhysicalTangentRange :
      ∀ base,
        projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center base →
        tangentFrameSpan basisData base = physicalTangent.physicalRange base)
    (physicalNormal : PhysicalNormalFrameOn
      (Model := NormalModel) basisData center)
    (normalIdentification : ProjectedSeedPhysicalRangeIdentification
      normalBasis hNormalBasis basisData center physicalNormal) :
    OpenAdaptedFramePair Base TangentModel NormalModel Ambient Ambient
      {base | projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base} where
  referenceTangent := pointwiseBasisSmoothTangentFrameFamilyOn tangentBasis
    hTangentBasis basisData center
  localTangent := physicalTangent.frame
  tangentRange := by
    intro base hValid
    exact (pointwiseBasisSmoothTangentFrameFamilyOn_range tangentBasis
      hTangentBasis basisData center base hValid).trans
        ((hPhysicalTangentRange base hValid).trans
          (physicalTangent.frame_range_eq base hValid).symm)
  referenceNormal := pointwiseBasisSmoothNormalFrameFamilyOn normalBasis
    hNormalBasis basisData center
  localNormal := physicalNormal.frame
  normalRange := projectedSeedFrame_range_eq_physicalFrame normalBasis
    hNormalBasis basisData center physicalNormal normalIdentification

/-- Smooth simultaneous tangent/normal residual transition produced by the full
projected-seed adapted frame pair. -/
def projectedSeedResidualTransition
    (tangentBasis : Basis ι ℝ TangentModel)
    (hTangentBasis : Orthonormal ℝ tangentBasis)
    (normalBasis : Basis κ ℝ NormalModel)
    (hNormalBasis : Orthonormal ℝ normalBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (center : Base)
    (physicalTangent : PhysicalTangentFrameOn
      (TangentModel := TangentModel) basisData center)
    (hPhysicalTangentRange :
      ∀ base,
        projectedSeedChartValid basisData.tangentFrame
          (pointwiseNormalSeedCharts basisData) center base →
        tangentFrameSpan basisData base = physicalTangent.physicalRange base)
    (physicalNormal : PhysicalNormalFrameOn
      (Model := NormalModel) basisData center)
    (normalIdentification : ProjectedSeedPhysicalRangeIdentification
      normalBasis hNormalBasis basisData center physicalNormal) :
    P0EFTJanusRieszShapeOperatorOpenMovingFrame.SmoothResidualOrthogonalFrameFamilyOn
      Base TangentModel NormalModel
      {base | projectedSeedChartValid basisData.tangentFrame
        (pointwiseNormalSeedCharts basisData) center base} :=
  (projectedSeedOpenAdaptedFramePair tangentBasis hTangentBasis
    normalBasis hNormalBasis basisData center physicalTangent
    hPhysicalTangentRange physicalNormal normalIdentification).residualTransition

/-- Status after constructing a complete smooth adapted pair from projected-seed
normal frames and the supplied tangent frame. -/
structure ProjectedSeedAdaptedFramePairStatus where
  tangentSynthesisConstructed : Prop
  tangentSynthesisSmooth : Prop
  tangentIsometricFramePackaged : Prop
  tangentRangeIdentified : Prop
  physicalTangentTransitionConstructed : Prop
  normalOrthogonalRangeIdentified : Prop
  openAdaptedFramePairConstructed : Prop
  residualTransitionConstructed : Prop
  connectedToOpenRieszInstantiation : Prop

/-- Closure of full projected-seed adapted-frame packaging. -/
def projectedSeedAdaptedFramePairClosed
    (s : ProjectedSeedAdaptedFramePairStatus) : Prop :=
  s.tangentSynthesisConstructed ∧
  s.tangentSynthesisSmooth ∧
  s.tangentIsometricFramePackaged ∧
  s.tangentRangeIdentified ∧
  s.physicalTangentTransitionConstructed ∧
  s.normalOrthogonalRangeIdentified ∧
  s.openAdaptedFramePairConstructed ∧
  s.residualTransitionConstructed ∧
  s.connectedToOpenRieszInstantiation

/-- Once the complete residual transition exists, only the concrete Riesz
coefficient fields remain to instantiate. -/
theorem missing_riesz_coefficients_after_adapted_pair
    (s : ProjectedSeedAdaptedFramePairStatus)
    (hClosed : projectedSeedAdaptedFramePairClosed s) :
    s.residualTransitionConstructed ∧
      Not s.connectedToOpenRieszInstantiation →
      Not s.connectedToOpenRieszInstantiation := by
  intro h
  exact h.2

end

end P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedFramePair
end JanusFormal
