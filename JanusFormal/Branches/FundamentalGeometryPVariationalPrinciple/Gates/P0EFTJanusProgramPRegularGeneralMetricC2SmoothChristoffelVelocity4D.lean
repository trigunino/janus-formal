import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulVelocity4D

/-! # Smooth Christoffel velocity in the genuine C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D

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
open P0EFTJanusProgramPRegularGeneralMetricC2RicciConnectionVelocity4D
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

/-- Background raised Christoffel coefficient as a global smooth field. -/
def regularFrameSmoothChristoffelCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Index4) : SmoothScalarField period hPeriod :=
  ∑ lower : Index4,
    smoothScalarFieldMul period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod metric upper lower)
      (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric
        first second lower)

/-- Product-rule Christoffel velocity as a global smooth field. -/
def regularFrameSmoothChristoffelVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (upper first second : Index4) : SmoothScalarField period hPeriod :=
  ∑ lower : Index4,
    (smoothScalarFieldMul period hPeriod
        (regularFrameSmoothInverseVariationCoefficient period hPeriod metric
          tensor upper lower)
        (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric
          first second lower) +
      smoothScalarFieldMul period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric upper lower)
        (regularFrameSmoothKoszulLowerVariationCoefficient period hPeriod
          metric tensor first second lower))

/-- The background completed Christoffel coefficient is the inclusion of
its explicit smooth field. -/
theorem regularGeneralMetricC0Christoffel_zero_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Index4) :
    regularGeneralMetricC0Christoffel period hPeriod metric 0
        upper first second =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothChristoffelCoefficient period hPeriod metric
          upper first second) := by
  apply ContinuousMap.ext
  intro point
  simp only [regularGeneralMetricC0Christoffel,
    regularFrameSmoothChristoffelCoefficient,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC0KoszulLower_zero_smooth,
    smoothToContinuous_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]

/-- The exact completed Christoffel parameter derivative is the explicit
smooth product-rule field. -/
theorem regularGeneralMetricC0ChristoffelFDerivativeAtZero_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (upper first second : Index4) :
    regularGeneralMetricC0ChristoffelFDerivativeAtZero period hPeriod metric
        upper first second
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothChristoffelVariationCoefficient
          period hPeriod metric tensor upper first second) := by
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  have hKoszul (lower : Index4) :=
    ((regularGeneralMetricC0KoszulLower_contDiff period hPeriod metric
      first second lower).differentiable (by simp) 0).hasFDerivAt
  have hProduct (lower : Index4) :=
    (regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
      period hPeriod metric upper lower).mul (hKoszul lower)
  have hSum := HasFDerivAt.fun_sum (u := Finset.univ) fun lower _ =>
    hProduct lower
  change HasFDerivAt
    (fun variation => regularGeneralMetricC0Christoffel period hPeriod metric
      variation upper first second) _ 0 at hSum
  have hApply := congrArg (fun derivative => derivative direction) hSum.fderiv
  apply ContinuousMap.ext
  intro point
  have hPoint := congrArg (fun field : C0Scalar period hPeriod => field point)
    hApply
  simp only [direction,
    regularGeneralMetricC0ChristoffelFDerivativeAtZero,
    regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero,
    regularGeneralMetricC0InverseMetricCoefficient_fderiv_smooth,
    regularGeneralMetricC0KoszulLower_fderiv_smooth,
    regularGeneralMetricC0InverseMetricCoefficient_zero_apply,
    regularGeneralMetricC0KoszulLower_zero_smooth,
    regularFrameSmoothChristoffelVariationCoefficient,
    smoothToContinuous_apply,
    Pi.mul_apply, Pi.zero_apply, Pi.add_apply, Pi.sub_apply,
    sum_apply, add_apply, sub_apply, smul_apply, zero_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, smoothScalarFieldAdd_apply,
    zero_mul, mul_zero, zero_add, add_zero, smul_eq_mul] at hPoint ⊢
  rw [hPoint]
  apply Finset.sum_congr rfl
  intro lower _
  ring

/-- Gate marker for the global smooth Christoffel parameter velocity. -/
theorem regular_general_metric_c2_smooth_christoffel_velocity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (upper first second : Index4) :
    regularGeneralMetricC0ChristoffelFDerivativeAtZero period hPeriod metric
        upper first second
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothChristoffelVariationCoefficient
          period hPeriod metric tensor upper first second) :=
  regularGeneralMetricC0ChristoffelFDerivativeAtZero_smooth
    period hPeriod metric tensor upper first second

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
end JanusFormal
