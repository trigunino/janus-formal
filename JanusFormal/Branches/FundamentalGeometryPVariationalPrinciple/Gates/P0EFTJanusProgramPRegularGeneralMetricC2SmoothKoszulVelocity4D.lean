import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseVelocity4D

/-! # Smooth lowered-Koszul velocity in the genuine C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulVelocity4D

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
open P0EFTJanusMappingTorusH1GraphTrace4D
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
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseVelocity4D

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

/-- Smooth first regular-frame derivative of the background metric. -/
def regularFrameSmoothMetricFirstDerivativeCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative row column : Index4) : SmoothScalarField period hPeriod :=
  frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (regularFrameMetricMatrix period hPeriod metric row column) derivative

/-- Background lowered Koszul coefficient as a global smooth field. -/
def regularFrameSmoothKoszulLowerCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second lower : Index4) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod metric
          first second lower +
      regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod metric
          second lower first -
      regularFrameSmoothMetricFirstDerivativeCoefficient period hPeriod metric
          lower first second -
      ∑ contracted : Index4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric
            second lower contracted)
          (regularFrameMetricMatrix period hPeriod metric first contracted) +
      ∑ contracted : Index4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric
            lower first contracted)
          (regularFrameMetricMatrix period hPeriod metric second contracted) +
      ∑ contracted : Index4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric
            first second contracted)
          (regularFrameMetricMatrix period hPeriod metric lower contracted))

/-- Linearized lowered Koszul coefficient as a global smooth field. -/
def regularFrameSmoothKoszulLowerVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second lower : Index4) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
          tensor first second lower +
      regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
          tensor second lower first -
      regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric
          tensor lower first second -
      ∑ contracted : Index4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric
            second lower contracted)
          (regularFrameSmoothCovariantVariationCoefficient period hPeriod
            metric tensor first contracted) +
      ∑ contracted : Index4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric
            lower first contracted)
          (regularFrameSmoothCovariantVariationCoefficient period hPeriod
            metric tensor second contracted) +
      ∑ contracted : Index4,
        smoothScalarFieldMul period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric
            first second contracted)
          (regularFrameSmoothCovariantVariationCoefficient period hPeriod
            metric tensor lower contracted))

/-- The background completed Koszul coefficient is the inclusion of the
explicit smooth field. -/
theorem regularGeneralMetricC0KoszulLower_zero_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second lower : Index4) :
    regularGeneralMetricC0KoszulLower period hPeriod metric 0
        first second lower =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric
          first second lower) := by
  apply ContinuousMap.ext
  intro point
  change (1 / 2 : Real) * _ = (1 / 2 : Real) * _
  simp only [regularGeneralMetricC0KoszulLower,
    regularFrameSmoothKoszulLowerCoefficient,
    regularFrameSmoothMetricFirstDerivativeCoefficient,
    regularGeneralMetricC0MetricFirstDerivative_zero_apply,
    regularGeneralMetricC0MetricCoefficient_zero_apply,
    regularFrameStructureCoefficientContinuous_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    smoothScalarFieldSmul_toFun, smoothScalarFieldAdd_apply,
    smoothScalarFieldSub_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]
  rfl

/-- The lowered Koszul parameter derivative is the explicit smooth
linearized coefficient. -/
theorem regularGeneralMetricC0KoszulLower_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second lower : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0KoszulLower
          period hPeriod metric variation first second lower) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothKoszulLowerVariationCoefficient
          period hPeriod metric tensor first second lower) := by
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  have hFirst (derivative row column : Index4) :=
    ((regularGeneralMetricC0MetricFirstDerivative_contDiff
      period hPeriod metric derivative row column).differentiable
        (by simp) 0).hasFDerivAt
  have hCoefficient (row column : Index4) :=
    ((regularGeneralMetricC0MetricCoefficient_contDiff
      period hPeriod metric row column).differentiable
        (by simp) 0).hasFDerivAt
  have hStructureMetric
      (bracketFirst bracketSecond contracted row column : Index4) :=
    (hasFDerivAt_const
      (x := (0 : RegularGeneralMetricC2Core period hPeriod metric))
      (c := regularFrameStructureCoefficientContinuous period hPeriod metric
        bracketFirst bracketSecond contracted)).mul
      (hCoefficient row column)
  have hMetricPart :=
    ((hFirst first second lower).add (hFirst second lower first)).sub
      (hFirst lower first second)
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
    (fun variation => regularGeneralMetricC0KoszulLower period hPeriod metric
      variation first second lower) _ 0 at hKoszul
  have hApply := congrArg (fun derivative => derivative direction)
    hKoszul.fderiv
  apply ContinuousMap.ext
  intro point
  have hPoint := congrArg (fun field : C0Scalar period hPeriod => field point)
    hApply
  simpa only [direction,
    regularGeneralMetricC0MetricFirstDerivative_fderiv_smooth,
    regularGeneralMetricC0MetricCoefficient_fderiv_smooth,
    regularFrameSmoothKoszulLowerVariationCoefficient,
    regularFrameStructureCoefficientContinuous_apply,
    Pi.mul_apply, Pi.zero_apply, Pi.add_apply, Pi.sub_apply,
    sum_apply, add_apply, sub_apply, smul_apply, zero_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, smoothScalarFieldSmul_toFun,
    smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply,
    smoothToContinuous_apply,
    zero_mul, mul_zero, zero_add, add_zero, smul_eq_mul] using hPoint

/-- Gate marker for the smooth lowered-Koszul parameter velocity. -/
theorem regular_general_metric_c2_smooth_koszul_velocity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (first second lower : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0KoszulLower
          period hPeriod metric variation first second lower) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothKoszulLowerVariationCoefficient
          period hPeriod metric tensor first second lower) :=
  regularGeneralMetricC0KoszulLower_fderiv_smooth
    period hPeriod metric tensor first second lower

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulVelocity4D
end JanusFormal
