import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D

/-! # Smooth inverse-metric velocity in the genuine C² chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseVelocity4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix
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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseVelocityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-- The smooth coefficient of `δg⁻¹ = -g⁻¹ (δg) g⁻¹`. -/
def regularFrameSmoothInverseVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index4) : SmoothScalarField period hPeriod :=
  (-1 : Real) •
    ∑ second : Index4,
      smoothScalarFieldMul period hPeriod
        (∑ first : Index4,
          smoothScalarFieldMul period hPeriod
            (regularFrameMetricInverseMatrix period hPeriod metric row first)
            (regularFrameSmoothCovariantVariationCoefficient
              period hPeriod metric tensor first second))
        (regularFrameMetricInverseMatrix period hPeriod metric second column)

theorem regularFrameSmoothInverseVariationCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameSmoothInverseVariationCoefficient period hPeriod metric tensor
        row column point =
      -∑ second : Index4,
        (∑ first : Index4,
          regularFrameMetricInverseMatrix period hPeriod metric row first point *
            tensor.tensor point (metric.frame first point)
              (metric.frame second point)) *
          regularFrameMetricInverseMatrix period hPeriod metric second column
            point := by
  simp only [regularFrameSmoothInverseVariationCoefficient,
    smoothScalarFieldSmul_toFun, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply,
    regularFrameSmoothCovariantVariationCoefficient_apply]
  ring

/-- The completed inverse coefficient has the explicit smooth velocity on
every genuine smooth tensor direction. -/
theorem regularGeneralMetricC0InverseMetricCoefficient_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0InverseMetricCoefficient
          period hPeriod metric variation row column) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothInverseVariationCoefficient
          period hPeriod metric tensor row column) := by
  apply ContinuousMap.ext
  intro point
  change regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
      point row column = _
  rw [regularGeneralMetricC0InverseMetricVelocityAt_smooth]
  change _ = regularFrameSmoothInverseVariationCoefficient
    period hPeriod metric tensor row column point
  rw [regularFrameSmoothInverseVariationCoefficient_apply]
  simp only [Matrix.neg_apply, Matrix.mul_apply,
    regularFrameMetricInverseMatrix, regularFrameMetricInverseMatrixMap,
    regularFrameCovariantVariationMatrixAt]

/-- Gate marker for the genuine smooth inverse-metric parameter velocity. -/
theorem regular_general_metric_c2_smooth_inverse_velocity_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0InverseMetricCoefficient
          period hPeriod metric variation row column) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothInverseVariationCoefficient
          period hPeriod metric tensor row column) :=
  regularGeneralMetricC0InverseMetricCoefficient_fderiv_smooth
    period hPeriod metric tensor row column

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseVelocity4D
end JanusFormal
