import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixEvaluation4D

/-!
# Transport of arbitrary C² metric variations through the Lorentz chart

The matrix of any symmetric tensor in the transported varied frame is the
exact inverse-root sandwich of its matrix in the fixed base frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 5000000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- The inverse of the selected self-adjoint root is self-adjoint. -/
theorem regularGeneralMetricC2IdentityRootInverse_isSelfAdjoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    metric.metric.musical point
        (regularGeneralMetricC2IdentityRootInverseAt
          period hPeriod metric variation point first) second =
      metric.metric.musical point first
        (regularGeneralMetricC2IdentityRootInverseAt
          period hPeriod metric variation point second) := by
  have hFirst := DFunLike.congr_fun
    (regularGeneralMetricC2IdentityRootAt_comp_inverse
      period hPeriod metric variation hVariation point) first
  have hSecond := DFunLike.congr_fun
    (regularGeneralMetricC2IdentityRootAt_comp_inverse
      period hPeriod metric variation hVariation point) second
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hFirst hSecond
  have hAdjoint := regularGeneralMetricC2IdentityRoot_isSelfAdjoint
    period hPeriod metric variation
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
        period hPeriod metric hVariation) point
      (regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric variation point first)
      (regularGeneralMetricC2IdentityRootInverseAt
        period hPeriod metric variation point second)
  rw [hFirst, hSecond] at hAdjoint
  exact hAdjoint.symm

/-- The fixed-frame matrix of the intrinsic inverse root is its evaluated
matrix inverse. -/
theorem regularGeneralMetricC2IdentityRootInverseAt_matrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        (regularGeneralMetricC2IdentityRootInverseAt
          period hPeriod metric variation point) =
      regularGeneralMetricC2IdentityRootInverseMatrixAt
        period hPeriod metric variation point := by
  ext row column
  rw [finiteFrameEndomorphismMatrixAt_apply,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate]
  simp [regularGeneralMetricC2IdentityRootInverseAt_apply,
    regularGeneralLorentzMetricSmoothD8Frame_vectorAt,
    RegularGeneralLorentzMetric.frame_eq_basisFun,
    Pi.basisFun_apply]

/-- Changing from the transported frame back to the base frame conjugates an
endomorphism by the root and inverse root. -/
theorem regularGeneralMetricC2LorentzChartVariationMatrix_frameTransport
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric
            period hPeriod metric variation hVariation) tensor) point =
      finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        ((regularGeneralMetricC2IdentityRootAt
            period hPeriod metric variation point).comp
          ((raisedGeneralMetricTensorAt period hPeriod
              (regularGeneralMetricC2LorentzChartRegularMetric
                period hPeriod metric variation hVariation).metric tensor point).comp
            (regularGeneralMetricC2IdentityRootInverseAt
              period hPeriod metric variation point))) := by
  rw [regularGeneralMetricC2VariationMatrix_valueAt]
  ext row column
  rw [finiteFrameEndomorphismMatrixAt_apply,
    finiteFrameEndomorphismMatrixAt_apply,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate,
    regularGeneralMetricFiniteFrameCoefficientAt_eq_coordinate,
    regularGeneralLorentzMetricSmoothD8Frame_vectorAt,
    regularGeneralLorentzMetricSmoothD8Frame_vectorAt,
    regularGeneralMetricC2LorentzChartRegularMetric_frame_apply,
    regularGeneralMetricC2LorentzChartRegularMetric_frameEquiv_symm_apply]
  rfl

/-- Intrinsically, raising a tensor with the varied metric and transporting
back to the base frame is the inverse-root sandwich. -/
theorem regularGeneralMetricC2LorentzChartRaisedTensor_transport
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    (regularGeneralMetricC2IdentityRootAt
        period hPeriod metric variation point).comp
      ((raisedGeneralMetricTensorAt period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric
            period hPeriod metric variation hVariation).metric tensor point).comp
        (regularGeneralMetricC2IdentityRootInverseAt
          period hPeriod metric variation point)) =
      (regularGeneralMetricC2IdentityRootInverseAt
          period hPeriod metric variation point).comp
        ((raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point).comp
          (regularGeneralMetricC2IdentityRootInverseAt
            period hPeriod metric variation point)) := by
  let root := regularGeneralMetricC2IdentityRootAt
    period hPeriod metric variation point
  let inverseRoot := regularGeneralMetricC2IdentityRootInverseAt
    period hPeriod metric variation point
  let variedMetric := regularGeneralMetricC2LorentzChartRegularMetric
    period hPeriod metric variation hVariation
  let variedRaised := raisedGeneralMetricTensorAt
    period hPeriod variedMetric.metric tensor point
  let baseRaised := raisedGeneralMetricTensorAt
    period hPeriod metric.metric tensor point
  have hRootInverse (vector : TangentFiber period hPeriod point) :
      root (inverseRoot vector) = vector := by
    have hIdentity := DFunLike.congr_fun
      (regularGeneralMetricC2IdentityRootAt_comp_inverse
        period hPeriod metric variation hVariation point) vector
    simpa only [root, inverseRoot, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using hIdentity
  have hInverseSelfAdjoint (first second : TangentFiber period hPeriod point) :
      metric.metric.musical point (inverseRoot first) second =
        metric.metric.musical point first (inverseRoot second) :=
    regularGeneralMetricC2IdentityRootInverse_isSelfAdjoint
      period hPeriod metric variation hVariation point first second
  apply ContinuousLinearMap.ext
  intro vector
  apply (metric.metric.musical point).injective
  apply ContinuousLinearMap.ext
  intro test
  simp only [ContinuousLinearMap.comp_apply]
  change metric.metric.musical point
      (root (variedRaised (inverseRoot vector))) test =
    metric.metric.musical point
      (inverseRoot (baseRaised (inverseRoot vector))) test
  calc
    _ = metric.metric.tensor.tensor point
        (root (variedRaised (inverseRoot vector))) test := by
      exact DFunLike.congr_fun
        (DFunLike.congr_fun (metric.metric.musical_eq_tensor point)
          (root (variedRaised (inverseRoot vector)))) test
    _ = variedMetric.metric.tensor.tensor point
        (variedRaised (inverseRoot vector)) (inverseRoot test) := by
      change metric.metric.tensor.tensor point
          (root (variedRaised (inverseRoot vector))) test =
        (regularGeneralMetricC2LorentzChartMetric
            period hPeriod metric variation hVariation).tensor.tensor point
          (variedRaised (inverseRoot vector)) (inverseRoot test)
      rw [regularGeneralMetricC2LorentzChartMetric_congruence,
        hRootInverse]
    _ = variedMetric.metric.musical point
        (variedRaised (inverseRoot vector)) (inverseRoot test) := by
      exact (DFunLike.congr_fun
        (DFunLike.congr_fun (variedMetric.metric.musical_eq_tensor point)
          (variedRaised (inverseRoot vector))) (inverseRoot test)).symm
    _ = tensor.tensor point (inverseRoot vector) (inverseRoot test) := by
      simp [variedRaised, raisedGeneralMetricTensorAt]
    _ = metric.metric.musical point
        (baseRaised (inverseRoot vector)) (inverseRoot test) := by
      simp [baseRaised, raisedGeneralMetricTensorAt]
    _ = metric.metric.musical point
        (inverseRoot (baseRaised (inverseRoot vector))) test :=
      (hInverseSelfAdjoint (baseRaised (inverseRoot vector)) test).symm

/-- Exact pointwise transport formula for arbitrary C² metric variations. -/
theorem regularGeneralMetricC2LorentzChartVariationMatrix_valueAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric
            period hPeriod metric variation hVariation) tensor) point =
      regularGeneralMetricC2IdentityRootInverseMatrixAt
          period hPeriod metric variation point *
        (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2VariationMatrix
              period hPeriod metric tensor) point *
          regularGeneralMetricC2IdentityRootInverseMatrixAt
            period hPeriod metric variation point) := by
  calc
    _ = finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        ((regularGeneralMetricC2IdentityRootAt
            period hPeriod metric variation point).comp
          ((raisedGeneralMetricTensorAt period hPeriod
              (regularGeneralMetricC2LorentzChartRegularMetric
                period hPeriod metric variation hVariation).metric tensor point).comp
            (regularGeneralMetricC2IdentityRootInverseAt
              period hPeriod metric variation point))) :=
      regularGeneralMetricC2LorentzChartVariationMatrix_frameTransport
        period hPeriod metric variation tensor hVariation point
    _ = finiteFrameEndomorphismMatrixAt period hPeriod
        (RegularFrame period hPeriod metric) metric.metric point
        ((regularGeneralMetricC2IdentityRootInverseAt
            period hPeriod metric variation point).comp
          ((raisedGeneralMetricTensorAt period hPeriod metric.metric tensor point).comp
            (regularGeneralMetricC2IdentityRootInverseAt
              period hPeriod metric variation point))) := by
      rw [regularGeneralMetricC2LorentzChartRaisedTensor_transport
        period hPeriod metric variation tensor hVariation point]
    _ = _ := by
      rw [finiteFrameEndomorphismMatrixAt_comp,
        finiteFrameEndomorphismMatrixAt_comp,
        regularGeneralMetricC2IdentityRootInverseAt_matrix,
        ← regularGeneralMetricC2VariationMatrix_valueAt]
      rfl

/-- Gate marker: every tensor variation obeys the exact inverse-root
transport law in the genuine varied Lorentz frame. -/
theorem regular_general_metric_c2_lorentz_chart_variation_transport_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric
            period hPeriod metric variation hVariation) tensor) point =
      regularGeneralMetricC2IdentityRootInverseMatrixAt
          period hPeriod metric variation point *
        (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2VariationMatrix
              period hPeriod metric tensor) point *
          regularGeneralMetricC2IdentityRootInverseMatrixAt
            period hPeriod metric variation point) :=
  regularGeneralMetricC2LorentzChartVariationMatrix_valueAt
    period hPeriod metric variation tensor hVariation point

end

end P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D
end JanusFormal
