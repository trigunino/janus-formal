import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D

/-! # Smooth spatial inverse-metric velocity in the genuine C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseSpatialVelocity4D

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

private def smoothTripleMul
    (first second third : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod :=
  smoothScalarFieldMul period hPeriod
    (smoothScalarFieldMul period hPeriod first second) third

/-- Stored background spatial inverse derivative as a smooth field. -/
def regularFrameSmoothInverseDerivativeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper lower : Index4) : SmoothScalarField period hPeriod :=
  (-1 : Real) •
    ∑ first : Index4, ∑ second : Index4,
      smoothTripleMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric upper first)
        (regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod
          metric derivative first second)
        (regularFrameMetricInverseMatrix period hPeriod metric second lower)

/-- Parameter velocity of the stored spatial inverse derivative. -/
def regularFrameSmoothInverseSpatialVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper lower : Index4) : SmoothScalarField period hPeriod :=
  (-1 : Real) •
    ∑ first : Index4, ∑ second : Index4,
      (smoothTripleMul period hPeriod
          (regularFrameSmoothInverseVariationCoefficient period hPeriod metric
            tensor upper first)
          (regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod
            metric derivative first second)
          (regularFrameMetricInverseMatrix period hPeriod metric second lower) +
        smoothTripleMul period hPeriod
          (regularFrameMetricInverseMatrix period hPeriod metric upper first)
          (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod
            metric tensor derivative first second)
          (regularFrameMetricInverseMatrix period hPeriod metric second lower) +
        smoothTripleMul period hPeriod
          (regularFrameMetricInverseMatrix period hPeriod metric upper first)
          (regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod
            metric derivative first second)
          (regularFrameSmoothInverseVariationCoefficient period hPeriod metric
            tensor second lower))

theorem regularGeneralMetricC0InverseMetricDerivative_zero_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative upper lower : Index4) :
    regularGeneralMetricC0InverseMetricDerivative period hPeriod metric 0
        derivative upper lower =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothInverseDerivativeCoefficient period hPeriod metric
          derivative upper lower) := by
  apply ContinuousMap.ext
  intro point
  change -( ∑ first : Index4, ∑ second : Index4,
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
          upper first point *
        regularGeneralMetricC0MetricFirstDerivative period hPeriod metric 0
          derivative first second point *
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric 0
          second lower point) = _
  simp only [regularFrameSmoothInverseDerivativeCoefficient,
    smoothTripleMul, regularFrameSmoothMetricFirstDerivativeCoefficient,
    frameDerivativeComponentField,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC0MetricFirstDerivative_zero_apply,
    smoothToContinuous_apply, smoothScalarFieldSmul_toFun,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
  ring

/-- The exact parameter derivative of the stored spatial inverse jet is the
explicit smooth three-factor product-rule field. -/
theorem regularGeneralMetricC0InverseMetricDerivative_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper lower : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0InverseMetricDerivative
          period hPeriod metric variation derivative upper lower) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothInverseSpatialVariationCoefficient
          period hPeriod metric tensor derivative upper lower) := by
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  have hFirstDerivative (row column : Index4) :=
    ((regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod
      metric derivative row column).differentiable (by simp) 0).hasFDerivAt
  have hFactor (first second : Index4) :=
    ((regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
      period hPeriod metric upper first).mul
      (hFirstDerivative first second)).mul
      (regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
        period hPeriod metric second lower)
  have hDoubleSum := HasFDerivAt.fun_sum (u := Finset.univ) fun first _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) fun second _ =>
      hFactor first second
  have hDerivative := hDoubleSum.neg
  change HasFDerivAt
    (fun variation => regularGeneralMetricC0InverseMetricDerivative
      period hPeriod metric variation derivative upper lower) _ 0 at hDerivative
  have hApply := congrArg (fun current => current direction) hDerivative.fderiv
  apply ContinuousMap.ext
  intro point
  have hPoint := congrArg (fun field : C0Scalar period hPeriod => field point)
    hApply
  simp only [direction,
    regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero,
    regularGeneralMetricC0InverseMetricCoefficient_fderiv_smooth,
    regularGeneralMetricC0MetricFirstDerivative_fderiv_smooth,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC0MetricFirstDerivative_zero_apply,
    regularFrameSmoothMetricFirstDerivativeCoefficient,
    frameDerivativeComponentField,
    regularFrameSmoothInverseSpatialVariationCoefficient, smoothTripleMul,
    smoothToContinuous_apply,
    Pi.mul_apply, Pi.neg_apply, Pi.zero_apply, Pi.add_apply,
    sum_apply, add_apply, smul_apply, neg_apply, zero_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply, ContinuousMap.neg_apply,
    smoothScalarFieldSmul_toFun, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, smoothScalarFieldAdd_apply,
    zero_mul, mul_zero, zero_add, add_zero, smul_eq_mul] at hPoint ⊢
  rw [hPoint]
  rw [neg_eq_neg_one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- Gate marker for the smooth stored spatial inverse-metric velocity. -/
theorem regular_general_metric_c2_smooth_inverse_spatial_velocity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative upper lower : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0InverseMetricDerivative
          period hPeriod metric variation derivative upper lower) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothInverseSpatialVariationCoefficient
          period hPeriod metric tensor derivative upper lower) :=
  regularGeneralMetricC0InverseMetricDerivative_fderiv_smooth
    period hPeriod metric tensor derivative upper lower

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseSpatialVelocity4D
end JanusFormal
