import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D

/-! # Pointwise product rule for the C² scalar-curvature derivative -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C0Scalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

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

/-- Exact derivative of one inverse-metric coefficient. -/
def regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  fderiv Real
    (fun variation =>
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
        variation row column) 0

theorem regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    HasFDerivAt
      (fun variation =>
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
          variation row column)
      (regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero
        period hPeriod metric row column) 0 := by
  exact (((regularGeneralMetricC0InverseMetricCoefficient_contDiffOn
    period hPeriod metric row column).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric)))
    |>.differentiableAt (by simp)).hasFDerivAt

/-- Exact derivative of one regular-frame Ricci coefficient. -/
def regularGeneralMetricC0RicciDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C0Scalar period hPeriod :=
  fderiv Real
    (fun variation => regularGeneralMetricC0Ricci period hPeriod metric
      variation first second) 0

theorem regularGeneralMetricC0Ricci_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4) :
    HasFDerivAt
      (fun variation => regularGeneralMetricC0Ricci period hPeriod metric
        variation first second)
      (regularGeneralMetricC0RicciDerivativeAtZero
        period hPeriod metric first second) 0 := by
  exact (((regularGeneralMetricC0Ricci_contDiffOn
    period hPeriod metric first second).contDiffAt
      ((regularGeneralMetricC2Domain_isOpen period hPeriod metric).mem_nhds
        (zero_mem_regularGeneralMetricC2Domain period hPeriod metric)))
    |>.differentiableAt (by simp)).hasFDerivAt

/-- Pointwise inverse matrix of the completed C² family. -/
def regularGeneralMetricC0InverseMetricMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  fun row column =>
    regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
      variation row column point

/-- Pointwise Ricci matrix of the completed C² family. -/
def regularGeneralMetricC0RicciMatrixAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  fun first second => regularGeneralMetricC0Ricci period hPeriod metric
    variation first second point

/-- Pointwise inverse-metric velocity in one C² direction. -/
def regularGeneralMetricC0InverseMetricVelocityAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  fun row column =>
    regularGeneralMetricC0InverseMetricCoefficientDerivativeAtZero
      period hPeriod metric row column direction point

/-- Pointwise Ricci velocity in one C² direction. -/
def regularGeneralMetricC0RicciVelocityAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) : Matrix4 :=
  fun first second =>
    regularGeneralMetricC0RicciDerivativeAtZero
      period hPeriod metric first second direction point

private theorem tensorPairing_comm (first second : Matrix4) :
    tensorPairing first second = tensorPairing second first := by
  unfold tensorPairing
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  ring

/-- The scalar-curvature derivative is exactly the sum of the inverse-metric
and Ricci velocities, pointwise. -/
theorem regularGeneralMetricC0ScalarCurvatureDerivativeAtZero_pointwise
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0ScalarCurvatureDerivativeAtZero
        period hPeriod metric direction point =
      inverseMetricScalarVelocity
          (regularGeneralMetricC0RicciMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0InverseMetricVelocityAt
            period hPeriod metric direction point) +
        palatiniScalarVelocity
          (regularGeneralMetricC0InverseMetricMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0RicciVelocityAt
            period hPeriod metric direction point) := by
  have hTerm (first second : Fin 4) :=
    (regularGeneralMetricC0InverseMetricCoefficient_hasFDerivAt_zero
      period hPeriod metric first second).mul
    (regularGeneralMetricC0Ricci_hasFDerivAt_zero
      period hPeriod metric first second)
  have hDoubleSum :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun first _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) fun second _ =>
        hTerm first second
  have hApply := congrArg (fun derivative => derivative direction)
    hDoubleSum.fderiv
  have hPoint := congrArg (fun field : C0Scalar period hPeriod => field point)
    hApply
  have hFunction :
      (fun variation => ∑ first : Fin 4, ∑ second : Fin 4,
        regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
            variation first second *
          regularGeneralMetricC0Ricci period hPeriod metric variation
            first second) =
        regularGeneralMetricC0ScalarCurvature period hPeriod metric := by
    rfl
  simp only [Pi.mul_apply] at hPoint
  rw [hFunction] at hPoint
  have hRaw :
      regularGeneralMetricC0ScalarCurvatureDerivativeAtZero
          period hPeriod metric direction point =
        palatiniScalarVelocity
            (regularGeneralMetricC0InverseMetricMatrixAt
              period hPeriod metric 0 point)
            (regularGeneralMetricC0RicciVelocityAt
              period hPeriod metric direction point) +
          tensorPairing
            (regularGeneralMetricC0RicciMatrixAt
              period hPeriod metric 0 point)
            (regularGeneralMetricC0InverseMetricVelocityAt
              period hPeriod metric direction point) := by
    simpa only [regularGeneralMetricC0ScalarCurvatureDerivativeAtZero,
      regularGeneralMetricC0InverseMetricMatrixAt,
      regularGeneralMetricC0RicciMatrixAt,
      regularGeneralMetricC0InverseMetricVelocityAt,
      regularGeneralMetricC0RicciVelocityAt,
      palatiniScalarVelocity, tensorPairing, Pi.mul_apply, sum_apply,
      add_apply, smul_apply, smul_eq_mul, ContinuousMap.sum_apply,
      ContinuousMap.mul_apply, ContinuousMap.add_apply,
      Finset.sum_add_distrib] using hPoint
  calc
    _ = palatiniScalarVelocity
          (regularGeneralMetricC0InverseMetricMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0RicciVelocityAt
            period hPeriod metric direction point) +
        tensorPairing
          (regularGeneralMetricC0RicciMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0InverseMetricVelocityAt
            period hPeriod metric direction point) := hRaw
    _ = palatiniScalarVelocity
          (regularGeneralMetricC0InverseMetricMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0RicciVelocityAt
            period hPeriod metric direction point) +
        inverseMetricScalarVelocity
          (regularGeneralMetricC0RicciMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0InverseMetricVelocityAt
            period hPeriod metric direction point) := by
      rw [inverseMetricScalarVelocity,
        tensorPairing_comm]
    _ = _ := add_comm _ _

/-- Gate marker for the exact pointwise Palatini split before converting the
Ricci velocity to a connection divergence. -/
theorem regular_general_metric_c2_scalar_curvature_derivative_pointwise_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularGeneralMetricC0ScalarCurvatureDerivativeAtZero
        period hPeriod metric direction point =
      inverseMetricScalarVelocity
          (regularGeneralMetricC0RicciMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0InverseMetricVelocityAt
            period hPeriod metric direction point) +
        palatiniScalarVelocity
          (regularGeneralMetricC0InverseMetricMatrixAt
            period hPeriod metric 0 point)
          (regularGeneralMetricC0RicciVelocityAt
            period hPeriod metric direction point) :=
  regularGeneralMetricC0ScalarCurvatureDerivativeAtZero_pointwise
    period hPeriod metric direction point

end
end P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
end JanusFormal
