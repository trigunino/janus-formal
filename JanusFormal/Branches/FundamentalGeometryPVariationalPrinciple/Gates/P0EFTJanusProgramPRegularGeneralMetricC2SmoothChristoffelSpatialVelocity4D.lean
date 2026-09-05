import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulSpatialVelocity4D

/-! # Smooth spatial Christoffel velocity in the genuine C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialVelocity4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseSpatialVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulSpatialVelocity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev Index4 := Fin 4

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
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

@[simp] private theorem smoothToContinuous_apply
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothToCanonicalPhysicalContinuousScalar period hPeriod field point =
      field point :=
  rfl

/-- Stored background spatial Christoffel derivative as a smooth field. -/
def regularFrameSmoothChristoffelDerivativeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Index4) :
    SmoothScalarField period hPeriod :=
  ∑ lower : Index4,
    (smoothScalarFieldMul period hPeriod
        (regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
          derivative upper lower)
        (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric
          first second lower) +
      smoothScalarFieldMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric upper lower)
        (regularFrameSmoothKoszulLowerDerivativeCoefficient period hPeriod metric
          derivative first second lower))

/-- Four-factor product-rule velocity of the stored spatial Christoffel
derivative. -/
def regularFrameSmoothChristoffelSpatialVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper first second : Index4) :
    SmoothScalarField period hPeriod :=
  ∑ lower : Index4,
    ((smoothScalarFieldMul period hPeriod
        (regularFrameSmoothInverseSpatialVariationCoefficient period hPeriod
          metric tensor derivative upper lower)
        (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric
          first second lower) +
      smoothScalarFieldMul period hPeriod
        (regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
          derivative upper lower)
        (regularFrameSmoothKoszulLowerVariationCoefficient period hPeriod metric
          tensor first second lower)) +
      (smoothScalarFieldMul period hPeriod
        (regularFrameSmoothInverseVariationCoefficient period hPeriod metric
          tensor upper lower)
        (regularFrameSmoothKoszulLowerDerivativeCoefficient period hPeriod metric
          derivative first second lower) +
      smoothScalarFieldMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric upper lower)
        (regularFrameSmoothKoszulLowerSpatialVariationCoefficient period hPeriod
          metric tensor derivative first second lower)))

/-- The stored background spatial Christoffel derivative is smooth. -/
theorem regularGeneralMetricC0ChristoffelDerivative_zero_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Index4) :
    regularGeneralMetricC0ChristoffelDerivative period hPeriod metric 0
        derivative upper first second =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothChristoffelDerivativeCoefficient period hPeriod metric
          derivative upper first second) := by
  apply ContinuousMap.ext
  intro point
  simp only [regularGeneralMetricC0ChristoffelDerivative,
    regularFrameSmoothChristoffelDerivativeCoefficient,
    regularGeneralMetricC0InverseMetricDerivative_zero_smooth,
    regularGeneralMetricC0KoszulLower_zero_smooth,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC0KoszulLowerDerivative_zero_smooth,
    smoothToContinuous_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, ContinuousMap.add_apply,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply,
    smoothScalarFieldAdd_apply]

/-- The parameter derivative of the stored spatial Christoffel jet is the
explicit smooth four-term product-rule field. -/
theorem regularGeneralMetricC0ChristoffelDerivative_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper first second : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0ChristoffelDerivative
          period hPeriod metric variation derivative upper first second) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothChristoffelSpatialVariationCoefficient
          period hPeriod metric tensor derivative upper first second) := by
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  have hMetricFirstDerivative (row column : Index4) :=
    ((regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod metric
      derivative row column).differentiable (by simp) 0).hasFDerivAt
  have hInverseDerivativeFactor (lower row column : Index4) :=
    ((regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
      period hPeriod metric upper row).mul
      (hMetricFirstDerivative row column)).mul
      (regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
        period hPeriod metric column lower)
  have hInverseDerivative (lower : Index4) :
      HasFDerivAt
        (fun variation => regularGeneralMetricC0InverseMetricDerivative
          period hPeriod metric variation derivative upper lower)
        (fderiv Real
          (fun variation => regularGeneralMetricC0InverseMetricDerivative
            period hPeriod metric variation derivative upper lower) 0) 0 := by
    have hRaw :=
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun row _ =>
        HasFDerivAt.fun_sum (u := Finset.univ) (fun column _ =>
          hInverseDerivativeFactor lower row column))).neg
    change HasFDerivAt
      (fun variation => regularGeneralMetricC0InverseMetricDerivative
        period hPeriod metric variation derivative upper lower) _ 0 at hRaw
    simpa only [hRaw.fderiv] using hRaw
  have hKoszul (lower : Index4) :=
    ((regularGeneralMetricC0KoszulLower_contDiff period hPeriod metric
      first second lower).differentiable (by simp) 0).hasFDerivAt
  have hKoszulDerivative (lower : Index4) :=
    ((regularGeneralMetricC0KoszulLowerDerivative_contDiff period hPeriod metric
      derivative first second lower).differentiable (by simp) 0).hasFDerivAt
  have hTerm (lower : Index4) :=
    ((hInverseDerivative lower).mul (hKoszul lower)).add
      ((regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
        period hPeriod metric upper lower).mul (hKoszulDerivative lower))
  have hSum := HasFDerivAt.fun_sum (u := Finset.univ) fun lower _ =>
    hTerm lower
  change HasFDerivAt
    (fun variation => regularGeneralMetricC0ChristoffelDerivative period hPeriod
      metric variation derivative upper first second) _ 0 at hSum
  have hApply := congrArg (fun current => current direction) hSum.fderiv
  apply ContinuousMap.ext
  intro point
  have hPoint := congrArg (fun field : C0Scalar period hPeriod => field point)
    hApply
  simp only [direction,
    regularGeneralMetricC0InverseMetricDerivative_fderiv_smooth,
    regularGeneralMetricC0KoszulLower_fderiv_smooth,
    regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero,
    regularGeneralMetricC0InverseMetricCoefficient_fderiv_smooth,
    regularGeneralMetricC0KoszulLowerDerivative_fderiv_smooth,
    regularGeneralMetricC0InverseMetricDerivative_zero_smooth,
    regularGeneralMetricC0KoszulLower_zero_smooth,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC0KoszulLowerDerivative_zero_smooth,
    regularFrameSmoothChristoffelSpatialVariationCoefficient,
    smoothToContinuous_apply, sum_apply, add_apply, smul_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply,
    smoothScalarFieldAdd_apply, smul_eq_mul] at hPoint ⊢
  rw [hPoint]
  apply Finset.sum_congr rfl
  intro lower _
  ring

/-- Gate marker for the smooth stored spatial Christoffel velocity. -/
theorem regular_general_metric_c2_smooth_christoffel_spatial_velocity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper first second : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0ChristoffelDerivative
          period hPeriod metric variation derivative upper first second) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothChristoffelSpatialVariationCoefficient
          period hPeriod metric tensor derivative upper first second) :=
  regularGeneralMetricC0ChristoffelDerivative_fderiv_smooth
    period hPeriod metric tensor derivative upper first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelSpatialVelocity4D
end JanusFormal
