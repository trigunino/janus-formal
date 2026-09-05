import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseSpatialVelocity4D

/-! # Smooth spatial lowered-Koszul velocity in the genuine C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulSpatialVelocity4D

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
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
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

/-- Smooth regular-frame derivative of a structure coefficient. -/
def regularFrameSmoothStructureCoefficientDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second upper : Index4) :
    SmoothScalarField period hPeriod :=
  frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (regularFrameStructureCoefficient period hPeriod metric first second upper)
    derivative

private def regularFrameSmoothMetricSecondDerivativeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner row column : Index4) : SmoothScalarField period hPeriod :=
  frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameMetricMatrix period hPeriod metric row column) inner) outer

private def regularFrameSmoothStructureMetricDerivativeTerm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn :
      Index4) : SmoothScalarField period hPeriod :=
  smoothScalarFieldMul period hPeriod
      (regularFrameSmoothStructureCoefficientDerivative period hPeriod metric
        derivative bracketFirst bracketSecond contracted)
      (regularFrameMetricMatrix period hPeriod metric metricRow metricColumn) +
    smoothScalarFieldMul period hPeriod
      (regularFrameStructureCoefficient period hPeriod metric bracketFirst
        bracketSecond contracted)
      (regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod metric
        derivative metricRow metricColumn)

private def regularFrameSmoothStructureMetricDerivativeVariationTerm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn :
      Index4) : SmoothScalarField period hPeriod :=
  smoothScalarFieldMul period hPeriod
      (regularFrameSmoothStructureCoefficientDerivative period hPeriod metric
        derivative bracketFirst bracketSecond contracted)
      (regularFrameSmoothCovariantVariationCoefficient period hPeriod metric
        tensor metricRow metricColumn) +
    smoothScalarFieldMul period hPeriod
      (regularFrameStructureCoefficient period hPeriod metric bracketFirst
        bracketSecond contracted)
      (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
        tensor derivative metricRow metricColumn)

/-- Stored spatial derivative of the background lowered Koszul coefficient as
a smooth field. -/
def regularFrameSmoothKoszulLowerDerivativeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second lower : Index4) :
    SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (regularFrameSmoothMetricSecondDerivativeCoefficient period hPeriod metric
          derivative first second lower +
      regularFrameSmoothMetricSecondDerivativeCoefficient period hPeriod metric
          derivative second lower first -
      regularFrameSmoothMetricSecondDerivativeCoefficient period hPeriod metric
          derivative lower first second -
      ∑ contracted : Index4,
        regularFrameSmoothStructureMetricDerivativeTerm period hPeriod metric
          derivative second lower contracted first contracted +
      ∑ contracted : Index4,
        regularFrameSmoothStructureMetricDerivativeTerm period hPeriod metric
          derivative lower first contracted second contracted +
      ∑ contracted : Index4,
        regularFrameSmoothStructureMetricDerivativeTerm period hPeriod metric
          derivative first second contracted lower contracted)

/-- Parameter velocity of the stored spatial lowered-Koszul derivative. -/
def regularFrameSmoothKoszulLowerSpatialVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative first second lower : Index4) :
    SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric
          tensor derivative first second lower +
      regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric
          tensor derivative second lower first -
      regularFrameSmoothCovariantVariationSecondDerivative period hPeriod metric
          tensor derivative lower first second -
      ∑ contracted : Index4,
        regularFrameSmoothStructureMetricDerivativeVariationTerm period hPeriod
          metric tensor derivative second lower contracted first contracted +
      ∑ contracted : Index4,
        regularFrameSmoothStructureMetricDerivativeVariationTerm period hPeriod
          metric tensor derivative lower first contracted second contracted +
      ∑ contracted : Index4,
        regularFrameSmoothStructureMetricDerivativeVariationTerm period hPeriod
          metric tensor derivative first second contracted lower contracted)

/-- The stored background spatial Koszul derivative is smooth. -/
theorem regularGeneralMetricC0KoszulLowerDerivative_zero_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative first second lower : Index4) :
    regularGeneralMetricC0KoszulLowerDerivative period hPeriod metric 0
        derivative first second lower =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothKoszulLowerDerivativeCoefficient period hPeriod metric
          derivative first second lower) := by
  apply ContinuousMap.ext
  intro point
  change (1 / 2 : Real) * _ = (1 / 2 : Real) * _
  simp only [regularFrameSmoothStructureMetricDerivativeTerm,
    regularFrameSmoothStructureCoefficientDerivative,
    regularFrameStructureMetricDerivativeTerm,
    regularFrameStructureCoefficientDerivativeContinuous_apply,
    regularGeneralMetricC0MetricSecondDerivative_zero_apply,
    regularGeneralMetricC0MetricCoefficient_zero_apply,
    regularGeneralMetricC0MetricFirstDerivative_zero_apply,
    regularFrameSmoothMetricSecondDerivativeCoefficient,
    regularFrameSmoothMetricFirstDerivativeCoefficient,
    frameDerivativeComponentField,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply,
    smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
  rfl

/-- The parameter derivative of the stored spatial Koszul jet is the explicit
smooth second-jet expression. -/
theorem regularGeneralMetricC0KoszulLowerDerivative_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative first second lower : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0KoszulLowerDerivative
          period hPeriod metric variation derivative first second lower) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothKoszulLowerSpatialVariationCoefficient
          period hPeriod metric tensor derivative first second lower) := by
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  have hSecondDerivative (outer inner row column : Index4) :=
    ((regularGeneralMetricC0MetricSecondDerivative_contDiff period hPeriod
      metric outer inner row column).differentiable (by simp) 0).hasFDerivAt
  have hCoefficient (row column : Index4) :=
    ((regularGeneralMetricC0MetricCoefficient_contDiff period hPeriod metric
      row column).differentiable (by simp) 0).hasFDerivAt
  have hFirstDerivative (inner row column : Index4) :=
    ((regularGeneralMetricC0MetricFirstDerivative_contDiff period hPeriod metric
      inner row column).differentiable (by simp) 0).hasFDerivAt
  have hStructureMetric
      (bracketFirst bracketSecond contracted metricRow metricColumn : Index4) :=
    ((hasFDerivAt_const
      (x := (0 : RegularGeneralMetricC2Core period hPeriod metric))
      (c := regularFrameStructureCoefficientDerivativeContinuous period hPeriod
        metric derivative bracketFirst bracketSecond contracted)).mul
      (hCoefficient metricRow metricColumn)).add
      ((hasFDerivAt_const
        (x := (0 : RegularGeneralMetricC2Core period hPeriod metric))
        (c := regularFrameStructureCoefficientContinuous period hPeriod metric
          bracketFirst bracketSecond contracted)).mul
        (hFirstDerivative derivative metricRow metricColumn))
  have hMetricPart :=
    ((hSecondDerivative derivative first second lower).add
      (hSecondDerivative derivative second lower first)).sub
      (hSecondDerivative derivative lower first second)
  have hFirstSum :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun contracted _ =>
      hStructureMetric second lower contracted first contracted
  have hSecondSum :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun contracted _ =>
      hStructureMetric lower first contracted second contracted
  have hThirdSum :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun contracted _ =>
      hStructureMetric first second contracted lower contracted
  have hRaw := ((hMetricPart.sub hFirstSum).add hSecondSum).add hThirdSum
  have hKoszul := hRaw.const_smul (1 / 2 : Real)
  change HasFDerivAt
    (fun variation => regularGeneralMetricC0KoszulLowerDerivative period hPeriod
      metric variation derivative first second lower) _ 0 at hKoszul
  have hApply := congrArg (fun current => current direction) hKoszul.fderiv
  apply ContinuousMap.ext
  intro point
  have hPoint := congrArg (fun field : C0Scalar period hPeriod => field point)
    hApply
  simpa only [direction,
    regularGeneralMetricC0MetricSecondDerivative_fderiv_smooth,
    regularGeneralMetricC0MetricCoefficient_fderiv_smooth,
    regularGeneralMetricC0MetricFirstDerivative_fderiv_smooth,
    regularGeneralMetricC0MetricSecondDerivative_zero_apply,
    regularGeneralMetricC0MetricCoefficient_zero_apply,
    regularGeneralMetricC0MetricFirstDerivative_zero_apply,
    regularFrameStructureCoefficientDerivativeContinuous_apply,
    regularFrameStructureCoefficientContinuous_apply,
    regularFrameSmoothKoszulLowerSpatialVariationCoefficient,
    regularFrameSmoothStructureMetricDerivativeVariationTerm,
    regularFrameSmoothStructureCoefficientDerivative,
    regularFrameSmoothCovariantVariationSecondDerivative,
    regularFrameSmoothCovariantVariationFirstDerivative,
    frameDerivativeComponentField, smoothToContinuous_apply,
    Pi.mul_apply, Pi.zero_apply, Pi.add_apply, Pi.sub_apply,
    sum_apply, add_apply, sub_apply, smul_apply, zero_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, smoothScalarFieldSmul_toFun,
    smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply,
    zero_mul, mul_zero, zero_add, add_zero, smul_eq_mul] using hPoint

/-- Gate marker for the smooth stored spatial lowered-Koszul velocity. -/
theorem regular_general_metric_c2_smooth_koszul_spatial_velocity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative first second lower : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0KoszulLowerDerivative
          period hPeriod metric variation derivative first second lower) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothKoszulLowerSpatialVariationCoefficient
          period hPeriod metric tensor derivative first second lower) :=
  regularGeneralMetricC0KoszulLowerDerivative_fderiv_smooth
    period hPeriod metric tensor derivative first second lower

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulSpatialVelocity4D
end JanusFormal
