import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D

/-!
# Regular metric carried by the completed Lorentz chart

The smooth inverse of the completed identity root transports the regular
frame of the base metric to the genuine affine metric.  Exact root
congruence preserves its Gram matrix, so the base smooth volume field is the
required varied volume.  Smooth inversion of the varied musical map supplies
the genuine sharp field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle ContinuousLinearMap Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricAffineLorentzRootBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateAGeometry4D.TangentFiber
    period hPeriod point

private abbrev CotangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev ModelTangent := CoverCoordinates
private abbrev ModelCotangent := ModelTangent →L[Real] Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance tangentFiberFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentFiber period hPeriod point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

private def regularGeneralMetricC2LorentzChartMetricCoordinates
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (TangentFiber period hPeriod) ModelCotangent
    (CotangentFiber period hPeriod) anchor current anchor current
    ((regularGeneralMetricC2LorentzChartMetric
      period hPeriod metric tensor hVariation).tensor.tensor current)

private theorem regularGeneralMetricC2LorentzChartMetricCoordinates_contMDiffAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real
        (ModelTangent →L[Real] ModelCotangent)) ∞
      (regularGeneralMetricC2LorentzChartMetricCoordinates
        period hPeriod metric tensor hVariation anchor) anchor := by
  have hMetric :=
    (regularGeneralMetricC2LorentzChartMetric
      period hPeriod metric tensor hVariation).tensor.tensor.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hMetric
  exact hMetric.2

private theorem regularGeneralMetricC2LorentzChartMetricCoordinates_isInvertible
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (anchor : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricC2LorentzChartMetricCoordinates
      period hPeriod metric tensor hVariation anchor anchor).IsInvertible := by
  have hTangent : anchor ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent
      (TangentFiber period hPeriod) anchor
  have hCotangent : anchor ∈
      (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelCotangent
      (CotangentFiber period hPeriod) anchor
  unfold regularGeneralMetricC2LorentzChartMetricCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ← (regularGeneralMetricC2LorentzChartMetric
      period hPeriod metric tensor hVariation).musical_eq_tensor anchor]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

/-- The genuine inverse musical map of the varied metric is a smooth bundle
homomorphism. -/
def regularGeneralMetricC2LorentzChartSharp
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    SmoothSharpField period hPeriod where
  toFun := fun point => inverseMetricSharp period hPeriod
    (regularGeneralMetricC2LorentzChartMetric
      period hPeriod metric tensor hVariation) point
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have hMetric :=
      regularGeneralMetricC2LorentzChartMetricCoordinates_contMDiffAt
        period hPeriod metric tensor hVariation anchor
    have hInverse :=
      (regularGeneralMetricC2LorentzChartMetricCoordinates_isInvertible
        period hPeriod metric tensor hVariation anchor
        |>.contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt hMetric
    apply hInverse.congr_of_eventuallyEq
    have hTangent : ∀ᶠ current in nhds anchor, current ∈
        (trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (TangentFiber period hPeriod) anchor)
    have hCotangent : ∀ᶠ current in nhds anchor, current ∈
        (trivializationAt ModelCotangent
          (CotangentFiber period hPeriod) anchor).baseSet :=
      (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelCotangent
            (CotangentFiber period hPeriod) anchor)
    filter_upwards [hTangent, hCotangent] with current hTangent' hCotangent'
    unfold regularGeneralMetricC2LorentzChartMetricCoordinates
    simp only [Function.comp_apply]
    change
      ContinuousLinearMap.inCoordinates ModelCotangent
          (CotangentFiber period hPeriod) ModelTangent
          (TangentFiber period hPeriod) anchor current anchor current
          (inverseMetricSharp period hPeriod
            (regularGeneralMetricC2LorentzChartMetric
              period hPeriod metric tensor hVariation) current) =
        (ContinuousLinearMap.inCoordinates ModelTangent
          (TangentFiber period hPeriod) ModelCotangent
          (CotangentFiber period hPeriod) anchor current anchor current
          ((regularGeneralMetricC2LorentzChartMetric
            period hPeriod metric tensor hVariation).tensor.tensor current)).inverse
    symm
    rw [ContinuousLinearMap.inCoordinates_eq hTangent' hCotangent',
      ← (regularGeneralMetricC2LorentzChartMetric
        period hPeriod metric tensor hVariation).musical_eq_tensor current]
    rw [ContinuousLinearMap.inCoordinates_eq hCotangent' hTangent']
    change
      (((trivializationAt ModelCotangent
            (CotangentFiber period hPeriod) anchor).continuousLinearEquivAt
          Real current hCotangent').toContinuousLinearMap.comp
        (((regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation).musical current)
            |>.toContinuousLinearMap.comp
          ((trivializationAt ModelTangent
              (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
            Real current hTangent').symm.toContinuousLinearMap)).inverse = _
    rw [ContinuousLinearMap.inverse_equiv_comp,
      ContinuousLinearMap.inverse_comp_equiv]
    change _ =
      ((trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hTangent').toContinuousLinearMap.comp
        ((inverseMetricSharp period hPeriod
          (regularGeneralMetricC2LorentzChartMetric
            period hPeriod metric tensor hVariation) current).comp
          ((trivializationAt ModelCotangent
              (CotangentFiber period hPeriod) anchor).continuousLinearEquivAt
            Real current hCotangent').symm.toContinuousLinearMap)
    simp only [inverseMetricSharp, ContinuousLinearMap.inverse_equiv,
      ContinuousLinearEquiv.symm_symm]
    exact ContinuousLinearMap.comp_assoc _ _ _

@[simp]
theorem regularGeneralMetricC2LorentzChartSharp_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2LorentzChartSharp
        period hPeriod metric tensor hVariation point =
      inverseMetricSharp period hPeriod
        (regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation) point :=
  rfl

private def regularGeneralMetricC2LorentzChartRootData
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    RegularGeneralMetricAffineRootData period hPeriod metric tensor :=
  regularGeneralMetricC2SelfAdjointIdentityAffineRootData
    period hPeriod metric tensor
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
        period hPeriod metric hVariation)

private def regularGeneralMetricC2LorentzChartRootEquivAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      TangentFiber period hPeriod point :=
  regularGeneralMetricAffineRootEquivAt period hPeriod metric tensor
    (regularGeneralMetricC2LorentzChartRootData
      period hPeriod metric tensor hVariation)
    (regularGeneralMetricC2LorentzChartDomain_mem_nondegenerate
      period hPeriod metric hVariation) point

@[simp]
private theorem regularGeneralMetricC2LorentzChartRootEquivAt_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    regularGeneralMetricC2LorentzChartRootEquivAt
        period hPeriod metric tensor hVariation point vector =
      regularGeneralMetricC2IdentityRootAt
        period hPeriod metric tensor point vector := by
  exact regularGeneralMetricAffineRootEquivAt_apply
    period hPeriod metric tensor
      (regularGeneralMetricC2LorentzChartRootData
        period hPeriod metric tensor hVariation)
      (regularGeneralMetricC2LorentzChartDomain_mem_nondegenerate
        period hPeriod metric hVariation) point vector

@[simp]
private theorem regularGeneralMetricC2LorentzChartRootEquivAt_apply_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    regularGeneralMetricC2LorentzChartRootEquivAt
        period hPeriod metric tensor hVariation point
          (regularGeneralMetricC2IdentityRootInverseAt
            period hPeriod metric tensor point vector) = vector := by
  rw [regularGeneralMetricC2LorentzChartRootEquivAt_apply]
  have hInverse := DFunLike.congr_fun
    (regularGeneralMetricC2IdentityRootAt_comp_inverse
      period hPeriod metric tensor hVariation point) vector
  simpa [ContinuousLinearMap.comp_apply] using hInverse

@[simp]
private theorem regularGeneralMetricC2LorentzChartRootEquivAt_symm_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    (regularGeneralMetricC2LorentzChartRootEquivAt
        period hPeriod metric tensor hVariation point).symm vector =
      regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point vector := by
  apply (regularGeneralMetricC2LorentzChartRootEquivAt
    period hPeriod metric tensor hVariation point).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    regularGeneralMetricC2LorentzChartRootEquivAt_apply_inverse]

/-- Public form of the exact congruence used to construct the varied Lorentz
metric. -/
theorem regularGeneralMetricC2LorentzChartMetric_congruence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    (regularGeneralMetricC2LorentzChartMetric
        period hPeriod metric tensor hVariation).tensor.tensor point
          first second =
      metric.metric.tensor.tensor point
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point first)
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point second) := by
  calc
    _ = (metric.metric.tensor + tensor).tensor point first second := by
      rw [regularGeneralMetricC2LorentzChartMetric_tensor]
    _ = metric.metric.tensor.tensor point
        (regularGeneralMetricC2LorentzChartRootEquivAt
          period hPeriod metric tensor hVariation point first)
        (regularGeneralMetricC2LorentzChartRootEquivAt
          period hPeriod metric tensor hVariation point second) :=
      regularGeneralMetricAffineRootData_congruence
        period hPeriod metric tensor
        (regularGeneralMetricC2LorentzChartRootData
          period hPeriod metric tensor hVariation)
        (regularGeneralMetricC2LorentzChartDomain_mem_nondegenerate
          period hPeriod metric hVariation) point first second
    _ = _ := by
      rw [regularGeneralMetricC2LorentzChartRootEquivAt_apply,
        regularGeneralMetricC2LorentzChartRootEquivAt_apply]

/-- Smooth frame transported from the base metric by the inverse root. -/
def regularGeneralMetricC2LorentzChartFrame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (index : Fin 4) : SmoothTangentField period hPeriod :=
  regularGeneralMetricC2IdentityRootInverseSmoothAction
    period hPeriod metric tensor hVariation (metric.frame index)

@[simp]
theorem regularGeneralMetricC2LorentzChartFrame_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (index : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC2LorentzChartFrame
        period hPeriod metric tensor hVariation index point =
      regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point (metric.frame index point) :=
  regularGeneralMetricC2IdentityRootInverseSmoothAction_apply
    period hPeriod metric tensor hVariation (metric.frame index) point

/-- Pointwise equivalence attached to the transported smooth frame. -/
def regularGeneralMetricC2LorentzChartFrameEquiv
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    (Fin 4 → Real) ≃L[Real] TangentFiber period hPeriod point :=
  (metric.frameEquiv point).trans
    (regularGeneralMetricC2LorentzChartRootEquivAt
      period hPeriod metric tensor hVariation point).symm

@[simp]
theorem regularGeneralMetricC2LorentzChartFrameEquiv_symm_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    (regularGeneralMetricC2LorentzChartFrameEquiv
        period hPeriod metric tensor hVariation point).symm vector =
      (metric.frameEquiv point).symm
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point vector) := by
  simp [regularGeneralMetricC2LorentzChartFrameEquiv,
    regularGeneralMetricC2LorentzChartRootEquivAt_apply]

private theorem regularGeneralMetricC2LorentzChartVolume_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    metric.volume point =
      metricVolumeDensity period hPeriod
        (regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation) point
        (fun index => regularGeneralMetricC2LorentzChartFrame
          period hPeriod metric tensor hVariation index point) := by
  have hGram :
      metricGramMatrix period hPeriod
          (regularGeneralMetricC2LorentzChartMetric
            period hPeriod metric tensor hVariation) point
          (fun index => regularGeneralMetricC2LorentzChartFrame
            period hPeriod metric tensor hVariation index point) =
        metricGramMatrix period hPeriod metric.metric point
          (fun index => metric.frame index point) := by
    ext first second
    change
      (regularGeneralMetricC2LorentzChartMetric
        period hPeriod metric tensor hVariation).tensor.tensor point
          (regularGeneralMetricC2LorentzChartFrame
            period hPeriod metric tensor hVariation first point)
          (regularGeneralMetricC2LorentzChartFrame
            period hPeriod metric tensor hVariation second point) =
        metric.metric.tensor.tensor point
          (metric.frame first point) (metric.frame second point)
    rw [regularGeneralMetricC2LorentzChartMetric_tensor,
      regularGeneralMetricC2LorentzChartFrame_apply,
      regularGeneralMetricC2LorentzChartFrame_apply,
      regularGeneralMetricAffineRootData_congruence period hPeriod metric tensor
        (regularGeneralMetricC2LorentzChartRootData
          period hPeriod metric tensor hVariation)
        (regularGeneralMetricC2LorentzChartDomain_mem_nondegenerate
          period hPeriod metric hVariation) point]
    change
      metric.metric.tensor.tensor point
          (regularGeneralMetricC2LorentzChartRootEquivAt
            period hPeriod metric tensor hVariation point
              (regularGeneralMetricC2IdentityRootInverseAt
                period hPeriod metric tensor point (metric.frame first point)))
          (regularGeneralMetricC2LorentzChartRootEquivAt
            period hPeriod metric tensor hVariation point
              (regularGeneralMetricC2IdentityRootInverseAt
                period hPeriod metric tensor point (metric.frame second point))) =
        metric.metric.tensor.tensor point
          (metric.frame first point) (metric.frame second point)
    rw [
      regularGeneralMetricC2LorentzChartRootEquivAt_apply_inverse,
      regularGeneralMetricC2LorentzChartRootEquivAt_apply_inverse]
  rw [metric.volume_eq]
  unfold metricVolumeDensity
  rw [hGram]

/-- The genuine affine chart metric with all regular sharp, frame and volume
data reconstructed rather than assumed. -/
def regularGeneralMetricC2LorentzChartRegularMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    RegularGeneralLorentzMetric period hPeriod where
  metric := regularGeneralMetricC2LorentzChartMetric
    period hPeriod metric tensor hVariation
  sharp := regularGeneralMetricC2LorentzChartSharp
    period hPeriod metric tensor hVariation
  sharp_eq := fun _ => rfl
  frame := regularGeneralMetricC2LorentzChartFrame
    period hPeriod metric tensor hVariation
  frameEquiv := regularGeneralMetricC2LorentzChartFrameEquiv
    period hPeriod metric tensor hVariation
  frame_eq := by
    intro point index
    rw [regularGeneralMetricC2LorentzChartFrame_apply, metric.frame_eq]
    change regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point
          (metric.frameEquiv point _) =
      (regularGeneralMetricC2LorentzChartRootEquivAt
        period hPeriod metric tensor hVariation point).symm
          (metric.frameEquiv point _)
    rw [regularGeneralMetricC2LorentzChartRootEquivAt_symm_apply]
  volume := metric.volume
  volume_eq := regularGeneralMetricC2LorentzChartVolume_eq
    period hPeriod metric tensor hVariation

@[simp]
theorem regularGeneralMetricC2LorentzChartRegularMetric_metric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    (regularGeneralMetricC2LorentzChartRegularMetric
      period hPeriod metric tensor hVariation).metric =
        regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation :=
  rfl

@[simp]
theorem regularGeneralMetricC2LorentzChartRegularMetric_frame_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (index : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricC2LorentzChartRegularMetric
        period hPeriod metric tensor hVariation).frame index point =
      regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric tensor point (metric.frame index point) :=
  regularGeneralMetricC2LorentzChartFrame_apply
    period hPeriod metric tensor hVariation index point

@[simp]
theorem regularGeneralMetricC2LorentzChartRegularMetric_frameEquiv_symm_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    ((regularGeneralMetricC2LorentzChartRegularMetric
        period hPeriod metric tensor hVariation).frameEquiv point).symm vector =
      (metric.frameEquiv point).symm
        (regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor point vector) :=
  regularGeneralMetricC2LorentzChartFrameEquiv_symm_apply
    period hPeriod metric tensor hVariation point vector

/-- Gate marker: every point of the completed regular C² Lorentz chart is a
genuine regular general Lorentz metric. -/
theorem regular_general_metric_c2_lorentz_chart_regular_metric_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    ∃ varied : RegularGeneralLorentzMetric period hPeriod,
      varied.metric = regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation ∧
        varied.metric.tensor = metric.metric.tensor + tensor := by
  exact ⟨regularGeneralMetricC2LorentzChartRegularMetric
      period hPeriod metric tensor hVariation, rfl,
    regularGeneralMetricC2LorentzChartMetric_tensor
      period hPeriod metric tensor hVariation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
end JanusFormal
