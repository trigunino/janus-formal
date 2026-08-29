import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D

/-!
# Zero-order frame transition for throat covariant two-tensors

The genuine tangent-frame transition induces the usual covariant rank-two
action on model tensors.  This gate proves its identity, cocycle, smoothness
and exact action on the coordinates of every smooth symmetric throat tensor.
No differentiated or higher-jet overlap law is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  ContinuousLinearMap.toNormedSpace

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Induced rank-two representation -/

/-- Covariant rank-two action induced by the tangent transition and its
contragredient covector action. -/
def throatCovariantTwoTensorTrivializationTransitionAt
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod) :
    TensorModel ≃L[Real] TensorModel :=
  (throatGaugeTangentTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current).arrowCongr
    (throatGaugeCovectorTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current)

@[simp]
theorem throatCovariantTwoTensorTrivializationTransitionAt_apply
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (tensor : TensorModel) (first second : ThroatCoverCoordinates) :
    throatCovariantTwoTensorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current tensor first second =
      tensor
        ((throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current).symm first)
        ((throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current).symm second) := by
  rfl

/-- The induced tensor transition is the identity on one frame's base set. -/
theorem throatCovariantTwoTensorTrivializationTransitionAt_self
    (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet) :
    throatCovariantTwoTensorTrivializationTransitionAt period hPeriod
        anchor anchor current =
      ContinuousLinearEquiv.refl Real TensorModel := by
  have hTangent :=
    throatGaugeTangentTrivializationTransitionAt_self period hPeriod
      anchor current hCurrent
  apply ContinuousLinearEquiv.ext
  funext tensor
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp only [throatCovariantTwoTensorTrivializationTransitionAt_apply,
    ContinuousLinearEquiv.refl_apply]
  rw [hTangent]
  simp

/-- Covariant rank-two frame transitions compose on every triple overlap. -/
theorem throatCovariantTwoTensorTrivializationTransitionAt_cocycle
    (firstAnchor middleAnchor lastAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) middleAnchor).baseSet ∩
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) lastAnchor).baseSet)) :
    (throatCovariantTwoTensorTrivializationTransitionAt period hPeriod
        firstAnchor middleAnchor current).trans
      (throatCovariantTwoTensorTrivializationTransitionAt period hPeriod
        middleAnchor lastAnchor current) =
      throatCovariantTwoTensorTrivializationTransitionAt period hPeriod
        firstAnchor lastAnchor current := by
  have hTangent :=
    throatGaugeTangentTrivializationTransitionAt_cocycle period hPeriod
      firstAnchor middleAnchor lastAnchor current hCurrent
  apply ContinuousLinearEquiv.ext
  funext tensor
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp only [ContinuousLinearEquiv.trans_apply,
    throatCovariantTwoTensorTrivializationTransitionAt_apply]
  rw [← hTangent]
  rfl

/-- The rank-two transition varies `C∞` on the common frame domain. -/
theorem throatCovariantTwoTensorTrivializationTransitionAt_contMDiffOn
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, TensorModel →L[Real] TensorModel) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (throatCovariantTwoTensorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            TensorModel →L[Real] TensorModel))
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) := by
  have hTangentInverse :=
    throatGaugeTangentTrivializationTransitionAt_symm_contMDiffOn
      period hPeriod firstAnchor secondAnchor
  have hCovector :=
    throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
      period hPeriod firstAnchor secondAnchor
  simpa only [throatCovariantTwoTensorTrivializationTransitionAt] using
    hTangentInverse.cle_arrowCongr hCovector

/-! ## Exact action on smooth tensor coordinates -/

@[simp]
theorem throatTensorCoordinates_apply_of_mem
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet)
    (first second : ThroatCoverCoordinates) :
    throatTensorCoordinates period hPeriod tensor anchor current first second =
      tensor.tensor current
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).symm current first)
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).symm current second) := by
  unfold throatTensorCoordinates
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp

/-- Coordinates in two tangent frames are related exactly by the induced
covariant rank-two transition. -/
theorem throatTensorCoordinates_eq_tensor_transition
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) :
    throatTensorCoordinates period hPeriod tensor secondAnchor current =
      throatCovariantTwoTensorTrivializationTransitionAt period hPeriod
        firstAnchor secondAnchor current
        (throatTensorCoordinates period hPeriod tensor firstAnchor current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [throatCovariantTwoTensorTrivializationTransitionAt_apply,
    throatTensorCoordinates_apply_of_mem period hPeriod tensor secondAnchor
      current hCurrent.2,
    throatTensorCoordinates_apply_of_mem period hPeriod tensor firstAnchor
      current hCurrent.1]
  have hVector (vector : ThroatCoverCoordinates) :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).symm current
          ((throatGaugeTangentTrivializationTransitionAt period hPeriod
            firstAnchor secondAnchor current).symm vector) =
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).symm current
          vector := by
    rw [throatGaugeTangentTrivializationTransitionAt_symm period hPeriod
      firstAnchor secondAnchor current hCurrent]
    unfold throatGaugeTangentTrivializationTransitionAt
    rw [← Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := Real) _ _ ⟨hCurrent.2, hCurrent.1⟩]
    exact
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstAnchor).symm_apply_apply_mk
          hCurrent.1 _
  rw [hVector first, hVector second]

end
end P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D
end JanusFormal
