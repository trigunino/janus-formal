import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricSecondDerivative4D

/-! # Smooth metric-parameter velocities of the genuine C² metric jet -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothActualMetricSecondDerivative4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

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

private theorem fderiv_apply_eq_of_smul_line
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (map : E → F) (direction : E) (value : F)
    (hDifferentiable : DifferentiableAt Real map 0)
    (hLine : ∀ scalar : Real,
      map (scalar • direction) = map 0 + scalar • value) :
    fderiv Real map 0 direction = value := by
  have hAffine : HasDerivAt (fun scalar : Real => scalar • direction)
      direction 0 := by
    simpa using (hasDerivAt_id (0 : Real)).smul_const direction
  have hAtLineZero :
      HasFDerivAt map (fderiv Real map 0)
        ((fun scalar : Real => scalar • direction) 0) := by
    simpa using hDifferentiable.hasFDerivAt
  have hComposed :=
    (hAtLineZero.comp 0 hAffine.hasFDerivAt).hasDerivAt
  have hExpected :
      HasDerivAt (fun scalar : Real => map 0 + scalar • value) value 0 := by
    exact (((hasDerivAt_id (0 : Real)).smul_const value).const_add (map 0))
      |>.congr_deriv (one_smul Real value)
  have hActual :
      HasDerivAt (fun scalar : Real => map (scalar • direction)) value 0 := by
    rw [show (fun scalar : Real => map (scalar • direction)) =
        fun scalar => map 0 + scalar • value by
      funext scalar
      exact hLine scalar]
    exact hExpected
  have hUnique := hComposed.unique hActual
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one] using hUnique

/-- Smooth regular-frame coefficient of the covariant metric variation. -/
def regularFrameSmoothCovariantVariationCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index4) : SmoothScalarField period hPeriod :=
  candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
      period hPeriod metric tensor row column -
    regularFrameMetricMatrix period hPeriod metric row column

@[simp]
theorem regularFrameSmoothCovariantVariationCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameSmoothCovariantVariationCoefficient
        period hPeriod metric tensor row column point =
      tensor.tensor point (metric.frame row point)
        (metric.frame column point) := by
  unfold regularFrameSmoothCovariantVariationCoefficient
  change candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric tensor row column point -
      regularFrameMetricMatrix period hPeriod metric row column point = _
  rw [← candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix]
  rw [candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth]
  rw [regularFrameMetricMatrix_apply]
  ring

/-- The actual smooth metric coefficient is affine in a smooth tensor
parameter. -/
theorem candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (scalar : Real) (row column : Index4) :
    candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod metric (scalar • tensor) row column =
      regularFrameMetricMatrix period hPeriod metric row column +
        scalar • regularFrameSmoothCovariantVariationCoefficient
          period hPeriod metric tensor row column := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [← candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix]
  rw [candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth]
  change
    metric.metric.tensor.tensor point (metric.frame row point)
          (metric.frame column point) +
        ((scalar • tensor).tensor point) (metric.frame row point)
          (metric.frame column point) =
      regularFrameMetricMatrix period hPeriod metric row column point +
        scalar * regularFrameSmoothCovariantVariationCoefficient
          period hPeriod metric tensor row column point
  rw [regularFrameMetricMatrix_apply,
    regularFrameSmoothCovariantVariationCoefficient_apply]
  rfl

/-- First regular-frame derivative of the smooth covariant variation. -/
def regularFrameSmoothCovariantVariationFirstDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative row column : Index4) : SmoothScalarField period hPeriod :=
  frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (regularFrameSmoothCovariantVariationCoefficient
      period hPeriod metric tensor row column) derivative

/-- Ordered second regular-frame derivative of the smooth covariant
variation. -/
def regularFrameSmoothCovariantVariationSecondDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Index4) : SmoothScalarField period hPeriod :=
  frameDerivativeComponentField period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    (frameDerivativeComponentField period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      (regularFrameSmoothCovariantVariationCoefficient
        period hPeriod metric tensor row column) inner) outer

private theorem regularGeneralMetricC2SmoothDirection_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (scalar : Real) :
    scalar • regularGeneralMetricC2SmoothDirection
        period hPeriod metric tensor =
      regularGeneralMetricC2SmoothDirection
        period hPeriod metric (scalar • tensor) := by
  unfold regularGeneralMetricC2SmoothDirection
  rw [map_smul]

/-- The metric coefficient's parameter derivative is the smooth covariant
variation coefficient. -/
theorem regularGeneralMetricC0MetricCoefficient_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0MetricCoefficient
          period hPeriod metric variation row column) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothCovariantVariationCoefficient
          period hPeriod metric tensor row column) := by
  let map := fun variation => regularGeneralMetricC0MetricCoefficient
    period hPeriod metric variation row column
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  let value : C0Scalar period hPeriod :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (regularFrameSmoothCovariantVariationCoefficient
        period hPeriod metric tensor row column)
  apply fderiv_apply_eq_of_smul_line map direction value
  · exact (regularGeneralMetricC0MetricCoefficient_contDiff
      period hPeriod metric row column).differentiable (by simp) 0
  · intro scalar
    apply ContinuousMap.ext
    intro point
    rw [regularGeneralMetricC2SmoothDirection_smul]
    dsimp only [map]
    unfold regularGeneralMetricC2SmoothDirection
    rw [candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth]
    simp only [map, direction, value,
      regularGeneralMetricC0MetricCoefficient_zero_apply,
      regularFrameSmoothCovariantVariationCoefficient_apply,
      ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContMDiffSection.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    change
      metric.metric.tensor.tensor point (metric.frame row point)
            (metric.frame column point) +
          ((scalar • tensor).tensor point) (metric.frame row point)
            (metric.frame column point) =
        regularFrameMetricMatrix period hPeriod metric row column point +
          scalar * regularFrameSmoothCovariantVariationCoefficient
            period hPeriod metric tensor row column point
    rw [regularFrameMetricMatrix_apply,
      regularFrameSmoothCovariantVariationCoefficient_apply]
    rfl

/-- The first spacetime metric jet has the corresponding smooth parameter
derivative. -/
theorem regularGeneralMetricC0MetricFirstDerivative_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (derivative row column : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0MetricFirstDerivative
          period hPeriod metric variation derivative row column) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothCovariantVariationFirstDerivative
          period hPeriod metric tensor derivative row column) := by
  let map := fun variation => regularGeneralMetricC0MetricFirstDerivative
    period hPeriod metric variation derivative row column
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  let value : C0Scalar period hPeriod :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (regularFrameSmoothCovariantVariationFirstDerivative
        period hPeriod metric tensor derivative row column)
  apply fderiv_apply_eq_of_smul_line map direction value
  · exact (regularGeneralMetricC0MetricFirstDerivative_contDiff
      period hPeriod metric derivative row column).differentiable (by simp) 0
  · intro scalar
    apply ContinuousMap.ext
    intro point
    rw [regularGeneralMetricC2SmoothDirection_smul]
    dsimp only [map]
    unfold regularGeneralMetricC2SmoothDirection
    rw [candidateANormalBoundaryRegularGeneralMetricC0MetricFirstDerivative_smooth]
    rw [candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_smul]
    rw [frameDerivative_add, frameDerivative_smul]
    simp only [map, direction, value,
      regularGeneralMetricC0MetricFirstDerivative_zero_apply,
      regularFrameSmoothCovariantVariationFirstDerivative,
      frameDerivativeComponentField, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    rfl

/-- The ordered second spacetime metric jet also has the exact smooth
parameter derivative. -/
theorem regularGeneralMetricC0MetricSecondDerivative_fderiv_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0MetricSecondDerivative
          period hPeriod metric variation outer inner row column) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothCovariantVariationSecondDerivative
          period hPeriod metric tensor outer inner row column) := by
  let map := fun variation => regularGeneralMetricC0MetricSecondDerivative
    period hPeriod metric variation outer inner row column
  let direction := regularGeneralMetricC2SmoothDirection
    period hPeriod metric tensor
  let value : C0Scalar period hPeriod :=
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (regularFrameSmoothCovariantVariationSecondDerivative
        period hPeriod metric tensor outer inner row column)
  apply fderiv_apply_eq_of_smul_line map direction value
  · exact (regularGeneralMetricC0MetricSecondDerivative_contDiff
      period hPeriod metric outer inner row column).differentiable (by simp) 0
  · intro scalar
    apply ContinuousMap.ext
    intro point
    rw [regularGeneralMetricC2SmoothDirection_smul]
    dsimp only [map]
    unfold regularGeneralMetricC2SmoothDirection
    rw [regularGeneralMetricC0MetricSecondDerivative_smooth_apply]
    change
      frameSecondDerivative period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
            period hPeriod metric (scalar • tensor) row column)
          point outer inner = _
    rw [candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix_smul]
    rw [frameSecondDerivative_add, frameSecondDerivative_smul]
    simp only [map, direction, value,
      regularGeneralMetricC0MetricSecondDerivative_zero_apply,
      regularFrameSmoothCovariantVariationSecondDerivative,
      frameSecondDerivative, frameDerivativeComponentField,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rfl

/-- Gate marker for the smooth parameter velocities of all metric jets needed
by the linearized connection. -/
theorem regular_general_metric_c2_smooth_metric_parameter_jet_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (outer inner row column : Index4) :
    fderiv Real
        (fun variation => regularGeneralMetricC0MetricSecondDerivative
          period hPeriod metric variation outer inner row column) 0
        (regularGeneralMetricC2SmoothDirection
          period hPeriod metric tensor) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameSmoothCovariantVariationSecondDerivative
          period hPeriod metric tensor outer inner row column) :=
  regularGeneralMetricC0MetricSecondDerivative_fderiv_smooth
    period hPeriod metric tensor outer inner row column

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
end JanusFormal
