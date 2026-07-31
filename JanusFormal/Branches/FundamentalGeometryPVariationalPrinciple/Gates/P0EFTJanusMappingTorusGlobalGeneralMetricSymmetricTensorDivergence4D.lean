import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

/-!
# Global divergence of a general symmetric tensor

The chartwise covector `∇^μ h_{μν}` is transported through the genuine
holonomic frame and glued with the canonical total atlas.  Smoothness is
proved locally through the inverse of one fixed chart.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Vector4

private abbrev Index4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Index4

private abbrev ModelCovector := CoverCoordinates →L[Real] Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def transportCovector
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (covector : TangentSpace coverModelWithCorners first →L[Real] Real) :
    TangentSpace coverModelWithCorners second →L[Real] Real := by
  subst second
  exact covector

private theorem transportCovector_eq_of_heq
    {first second : EffectiveQuotient period hPeriod}
    (samePoint : first = second)
    (firstCovector : TangentSpace coverModelWithCorners first →L[Real] Real)
    (secondCovector : TangentSpace coverModelWithCorners second →L[Real] Real)
    (hCovector : HEq firstCovector secondCovector) :
    transportCovector period hPeriod samePoint firstCovector =
      secondCovector := by
  subst second
  exact eq_of_heq hCovector

/-- Pointwise divergence selected from the canonical total holonomic atlas. -/
def globalGeneralMetricSymmetricTensorDivergenceAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentSpace coverModelWithCorners point →L[Real] Real :=
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  transportCovector period hPeriod witness.coordinate_eq
    (localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
      tensor witness.patch witness.coordinate)

/-- The selected pointwise covector equals every local representative. -/
theorem globalGeneralMetricSymmetricTensorDivergenceAt_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric tensor
        (patch.coordinateMap coordinate) =
      localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
        tensor patch coordinate := by
  unfold globalGeneralMetricSymmetricTensorDivergenceAt
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod
      (patch.coordinateMap coordinate)
  apply transportCovector_eq_of_heq
  exact
    localSymmetricTensorDivergenceIntrinsicCovector_transition period hPeriod
      metric tensor witness.patch patch witness.coordinate coordinate
        witness.coordinate_eq

private def localInverseDerivativeCoordinates
    (localInverse : EffectiveQuotient period hPeriod → Vector4)
    (anchor current : EffectiveQuotient period hPeriod) :
    CoverCoordinates →L[Real] Vector4 :=
  inTangentCoordinates coverModelWithCorners
    (modelWithCornersSelf Real Vector4)
      (fun point : EffectiveQuotient period hPeriod => point) localInverse
      (mfderiv coverModelWithCorners (modelWithCornersSelf Real Vector4)
        localInverse) anchor current

private theorem localInverseDerivativeCoordinates_apply
    (localInverse : EffectiveQuotient period hPeriod → Vector4)
    (anchor current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates
        (TangentSpace coverModelWithCorners) anchor).baseSet)
    (vector : CoverCoordinates) :
    localInverseDerivativeCoordinates period hPeriod localInverse anchor current
        vector =
      (trivializationAt Vector4
        (TangentSpace (modelWithCornersSelf Real Vector4))
          (localInverse anchor)).linearMapAt Real (localInverse current)
        (mfderiv coverModelWithCorners (modelWithCornersSelf Real Vector4)
          localInverse current
          ((trivializationAt CoverCoordinates
            (TangentSpace coverModelWithCorners) anchor).symm current
              vector)) := by
  have hTarget : localInverse current ∈
      (trivializationAt Vector4
        (TangentSpace (modelWithCornersSelf Real Vector4))
          (localInverse anchor)).baseSet := by
    simp
  rw [show
      localInverseDerivativeCoordinates period hPeriod localInverse anchor
          current =
        ContinuousLinearMap.inCoordinates CoverCoordinates
          (TangentSpace coverModelWithCorners) Vector4
          (TangentSpace (modelWithCornersSelf Real Vector4))
          anchor current (localInverse anchor) (localInverse current)
          (mfderiv coverModelWithCorners
            (modelWithCornersSelf Real Vector4) localInverse current) by
      rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hTarget]
  rw [Trivialization.linearMapAt_apply, if_pos hTarget]
  rfl

private def globalGeneralMetricSymmetricTensorDivergenceCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) : ModelCovector :=
  ContinuousLinearMap.inCoordinates CoverCoordinates
    (TangentSpace coverModelWithCorners) Real
    (fun _ : EffectiveQuotient period hPeriod => Real)
    anchor current anchor current
    (globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric tensor
      current)

private theorem globalGeneralMetricSymmetricTensorDivergenceCoordinates_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates
        (TangentSpace coverModelWithCorners) anchor).baseSet)
    (vector : CoverCoordinates) :
    globalGeneralMetricSymmetricTensorDivergenceCoordinates period hPeriod
        metric tensor anchor current vector =
      globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric
        tensor current
        ((trivializationAt CoverCoordinates
          (TangentSpace coverModelWithCorners) anchor).symm current
            vector) := by
  unfold globalGeneralMetricSymmetricTensorDivergenceCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent (by simp)]
  simp

private theorem localInverse_mfderiv_eq_frameCoordinates
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (anchorCoordinate : Vector4)
    (current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (patch.coordinateMap_isLocalDiffeomorph
        anchorCoordinate).localInverse.source)
    (tangent : TangentSpace coverModelWithCorners current) :
    mfderiv coverModelWithCorners (modelWithCornersSelf Real Vector4)
        (patch.coordinateMap_isLocalDiffeomorph anchorCoordinate).localInverse
        current tangent =
      ((Pi.basisFun Real Index4).equiv
        (patch.frame
          ((patch.coordinateMap_isLocalDiffeomorph anchorCoordinate)
            |>.localInverse current))
        (Equiv.refl Index4)).symm tangent := by
  let hLocal := patch.coordinateMap_isLocalDiffeomorph anchorCoordinate
  let coordinate := hLocal.localInverse current
  let frame :=
    (Pi.basisFun Real Index4).equiv (patch.frame coordinate)
      (Equiv.refl Index4)
  have hEventually :
      patch.coordinateMap ∘ hLocal.localInverse =ᶠ[𝓝 current] id :=
    Filter.eventuallyEq_of_mem
      (hLocal.localInverse.open_source.mem_nhds hCurrent)
      hLocal.localInverse_eqOn_right
  have hDerivative :
      mfderiv coverModelWithCorners coverModelWithCorners
          (patch.coordinateMap ∘ hLocal.localInverse) current =
        mfderiv coverModelWithCorners coverModelWithCorners
          (id : EffectiveQuotient period hPeriod →
            EffectiveQuotient period hPeriod) current :=
    hEventually.mfderiv_eq
  have hInverseAt :
      MDifferentiableAt coverModelWithCorners
        (modelWithCornersSelf Real Vector4) hLocal.localInverse current :=
    (hLocal.localInverse.isLocalDiffeomorphAt coverModelWithCorners
      (modelWithCornersSelf Real Vector4) ∞ hCurrent)
      |>.mdifferentiableAt (by simp)
  have hMapAt :
      MDifferentiableAt (modelWithCornersSelf Real Vector4)
        coverModelWithCorners patch.coordinateMap coordinate :=
    patch.coordinateMap_contMDiff.mdifferentiable (by simp) coordinate
  have hChain :
      mfderiv coverModelWithCorners coverModelWithCorners
          (patch.coordinateMap ∘ hLocal.localInverse) current =
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate).comp
          (mfderiv coverModelWithCorners
            (modelWithCornersSelf Real Vector4) hLocal.localInverse
              current) :=
    mfderiv_comp current hMapAt hInverseAt
  have hRight :
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate
          (mfderiv coverModelWithCorners
            (modelWithCornersSelf Real Vector4) hLocal.localInverse current
              tangent) =
        tangent := by
    have hChainAt :
        mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
            patch.coordinateMap coordinate
            (mfderiv coverModelWithCorners
              (modelWithCornersSelf Real Vector4) hLocal.localInverse current
                tangent) =
          mfderiv coverModelWithCorners coverModelWithCorners
            (patch.coordinateMap ∘ hLocal.localInverse) current tangent :=
      congrArg (fun derivative => derivative tangent) hChain.symm
    have hDerivativeAt :
        mfderiv coverModelWithCorners coverModelWithCorners
            (patch.coordinateMap ∘ hLocal.localInverse) current tangent =
          mfderiv coverModelWithCorners coverModelWithCorners
            (id : EffectiveQuotient period hPeriod →
              EffectiveQuotient period hPeriod) current tangent :=
      congrArg (fun derivative => derivative tangent) hDerivative
    have hIdentityAt :
        mfderiv coverModelWithCorners coverModelWithCorners
            (id : EffectiveQuotient period hPeriod →
              EffectiveQuotient period hPeriod) current tangent =
          tangent := by
      rw [mfderiv_id]
      rfl
    exact hChainAt.trans (hDerivativeAt.trans hIdentityAt)
  apply frame.injective
  rw [frame.apply_symm_apply]
  rw [← coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch]
  exact hRight

private theorem localInverseDerivativeCoordinates_eq_frameCoordinates
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (anchorCoordinate : Vector4)
    (current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (patch.coordinateMap_isLocalDiffeomorph
        anchorCoordinate).localInverse.source)
    (hTrivialization : current ∈
      (trivializationAt CoverCoordinates
        (TangentSpace coverModelWithCorners)
          (patch.coordinateMap anchorCoordinate)).baseSet)
    (vector : CoverCoordinates) :
    localInverseDerivativeCoordinates period hPeriod
        (patch.coordinateMap_isLocalDiffeomorph
          anchorCoordinate).localInverse
        (patch.coordinateMap anchorCoordinate) current vector =
      ((Pi.basisFun Real Index4).equiv
        (patch.frame
          ((patch.coordinateMap_isLocalDiffeomorph anchorCoordinate)
            |>.localInverse current))
        (Equiv.refl Index4)).symm
          ((trivializationAt CoverCoordinates
            (TangentSpace coverModelWithCorners)
              (patch.coordinateMap anchorCoordinate)).symm current vector) := by
  rw [localInverseDerivativeCoordinates_apply period hPeriod _ _ _
    hTrivialization]
  have hTarget :
      (patch.coordinateMap_isLocalDiffeomorph anchorCoordinate).localInverse
          current ∈
        (trivializationAt Vector4
          (TangentSpace (modelWithCornersSelf Real Vector4))
            ((patch.coordinateMap_isLocalDiffeomorph anchorCoordinate)
              |>.localInverse (patch.coordinateMap anchorCoordinate))).baseSet := by
    simp
  rw [Trivialization.linearMapAt_apply, if_pos hTarget]
  simp only [trivializationAt_model_space_apply]
  exact
    localInverse_mfderiv_eq_frameCoordinates period hPeriod patch
      anchorCoordinate current hCurrent
        ((trivializationAt CoverCoordinates
          (TangentSpace coverModelWithCorners)
            (patch.coordinateMap anchorCoordinate)).symm current vector)

/-- The effective background underlying the global divergence field. -/
abbrev generalMetricDivergenceBackground : EffectiveD8Background where
  period := period
  period_ne_zero := hPeriod

/-- The covariant divergence `∇^μ h_{μν}` as a genuine smooth global
one-form. -/
def globalGeneralMetricSymmetricTensorDivergence
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    EffectiveD8SmoothCovectorField
      (generalMetricDivergenceBackground period hPeriod) where
  toFun :=
    globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric tensor
  contMDiff_toFun := by
    intro point
    let witness :=
      canonicalPhysicalScalarEulerChartWitness period hPeriod point
    rw [← witness.coordinate_eq]
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    let hLocal :=
      witness.patch.coordinateMap_isLocalDiffeomorph witness.coordinate
    let anchor := witness.patch.coordinateMap witness.coordinate
    change ContMDiffAt coverModelWithCorners
      𝓘(Real, ModelCovector) ∞
      (globalGeneralMetricSymmetricTensorDivergenceCoordinates period hPeriod
        metric tensor anchor) anchor
    have hModel :
        ContMDiffAt coverModelWithCorners
          𝓘(Real, Vector4 →L[Real] Real) ∞
          (fun current =>
            localSymmetricTensorDivergenceModelCovector period hPeriod metric
              tensor witness.patch (hLocal.localInverse current)) anchor :=
      (localSymmetricTensorDivergenceModelCovector_contDiff period hPeriod
        metric tensor witness.patch).contMDiff.contMDiffAt.comp anchor
          hLocal.localInverse_contMDiffAt
    have hDerivative :=
      hLocal.localInverse_contMDiffAt.mfderiv_const
        (x₀ := anchor) (m := ∞) (by simp)
    change ContMDiffAt coverModelWithCorners
      𝓘(Real, CoverCoordinates →L[Real] Vector4) ∞
      (localInverseDerivativeCoordinates period hPeriod hLocal.localInverse
        anchor) anchor at hDerivative
    have hFormula := hModel.clm_comp hDerivative
    apply hFormula.congr_of_eventuallyEq
    have hSource : ∀ᶠ current in 𝓝 anchor,
        current ∈ hLocal.localInverse.source :=
      hLocal.localInverse.open_source.mem_nhds hLocal.localInverse_mem_source
    have hTrivialization : ∀ᶠ current in 𝓝 anchor,
        current ∈
          (trivializationAt CoverCoordinates
            (TangentSpace coverModelWithCorners) anchor).baseSet :=
      (trivializationAt CoverCoordinates
        (TangentSpace coverModelWithCorners) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt CoverCoordinates
            (TangentSpace coverModelWithCorners) anchor)
    filter_upwards [hSource, hTrivialization] with current hCurrent hTriv
    apply ContinuousLinearMap.ext
    intro vector
    change
      globalGeneralMetricSymmetricTensorDivergenceCoordinates period hPeriod
          metric tensor anchor current vector =
        localSymmetricTensorDivergenceModelCovector period hPeriod metric
          tensor witness.patch (hLocal.localInverse current)
          (localInverseDerivativeCoordinates period hPeriod
            hLocal.localInverse anchor current vector)
    rw [globalGeneralMetricSymmetricTensorDivergenceCoordinates_apply
      period hPeriod metric tensor anchor current hTriv vector]
    rw [localInverseDerivativeCoordinates_eq_frameCoordinates period hPeriod
      witness.patch witness.coordinate current hCurrent hTriv vector]
    have hRight :
        witness.patch.coordinateMap (hLocal.localInverse current) = current :=
      hLocal.localInverse_eqOn_right hCurrent
    have hLeft :
        hLocal.localInverse
            (witness.patch.coordinateMap (hLocal.localInverse current)) =
          hLocal.localInverse current :=
      hLocal.localInverse_left_inv
        (hLocal.localInverse.map_source hCurrent)
    rw [← hRight]
    rw [globalGeneralMetricSymmetricTensorDivergenceAt_eq_local]
    rw [hLeft]
    unfold localSymmetricTensorDivergenceIntrinsicCovector
    rfl

@[simp]
theorem globalGeneralMetricSymmetricTensorDivergence_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor
        point =
      globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric
        tensor point :=
  rfl

end

end P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
end JanusFormal
