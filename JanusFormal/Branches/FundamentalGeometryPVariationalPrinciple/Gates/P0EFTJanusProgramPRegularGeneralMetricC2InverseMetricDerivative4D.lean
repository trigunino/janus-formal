import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

/-! # Exact derivative of the regular general inverse metric -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
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
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

/-- Derivative of the inverse relative matrix at the affine origin. -/
def generalMetricRelativeC2InverseMatrixDerivativeAtZero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricRelativeC2Core period hPeriod frame baseMetric →L[Real]
      C2FiniteMatrix period hPeriod frame.count :=
  (c2FiniteMatrixInverseDerivative period hPeriod frame.count
      (c2FiniteMatrixIdentity period hPeriod frame.count)).comp
    (generalMetricRelativeC2ExtendedMatrixDerivative
      period hPeriod frame baseMetric)

theorem generalMetricRelativeC2InverseMatrix_hasFDerivAt_zero
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
      (generalMetricRelativeC2InverseMatrix period hPeriod frame baseMetric)
      (generalMetricRelativeC2InverseMatrixDerivativeAtZero
        period hPeriod frame baseMetric) 0 := by
  have hInner := generalMetricRelativeC2ExtendedMatrix_hasFDerivAt_zero
    period hPeriod frame baseMetric
  have hOuter : HasFDerivAt
      (c2FiniteMatrixInverse period hPeriod frame.count)
      (c2FiniteMatrixInverseDerivative period hPeriod frame.count
        (c2FiniteMatrixIdentity period hPeriod frame.count))
      (generalMetricRelativeC2ExtendedMatrix
        period hPeriod frame baseMetric 0) := by
    simpa [generalMetricRelativeC2ExtendedMatrix] using
      c2FiniteMatrixInverse_hasFDerivAt period hPeriod frame.count
        (c2FiniteMatrixIdentity period hPeriod frame.count)
        (c2FiniteMatrixIdentity_mem_unitSet period hPeriod frame.count)
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

@[simp]
theorem generalMetricRelativeC2InverseMatrixDerivativeAtZero_apply
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (direction : GeneralMetricRelativeC2Core
      period hPeriod frame baseMetric) :
    generalMetricRelativeC2InverseMatrixDerivativeAtZero
        period hPeriod frame baseMetric direction = -direction.1 := by
  have hIdentityInverse :
      c2FiniteMatrixInverse period hPeriod frame.count
          (c2FiniteMatrixIdentity period hPeriod frame.count) =
        c2FiniteMatrixIdentity period hPeriod frame.count := by
    have hInverse := c2FiniteMatrixProduct_inverse_right
      period hPeriod frame.count
      (c2FiniteMatrixIdentity period hPeriod frame.count)
      (c2FiniteMatrixIdentity_mem_unitSet period hPeriod frame.count)
    rw [c2FiniteMatrixProduct_identity_left] at hInverse
    exact hInverse
  rw [generalMetricRelativeC2InverseMatrixDerivativeAtZero,
    ContinuousLinearMap.comp_apply,
    c2FiniteMatrixInverseDerivative_apply,
    generalMetricRelativeC2ExtendedMatrixDerivative,
    hIdentityInverse]
  rw [c2FiniteMatrixProduct_identity_left,
    c2FiniteMatrixProduct_identity_right]
  rfl

/-- Derivative of the physical inverse-metric coefficient matrix. -/
def regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C2FiniteMatrix period hPeriod 4 :=
  ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4).flip
        (regularFrameMetricInverseC2Matrix period hPeriod metric)).comp
    (generalMetricRelativeC2InverseMatrixDerivativeAtZero period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric)

theorem regularGeneralMetricC2InverseMetricMatrix_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric)
      (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
        period hPeriod metric) 0 := by
  have hInner := generalMetricRelativeC2InverseMatrix_hasFDerivAt_zero
    period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric
  have hOuter : HasFDerivAt
      (fun matrix => c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4 matrix
          (regularFrameMetricInverseC2Matrix period hPeriod metric))
      ((c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4).flip
          (regularFrameMetricInverseC2Matrix period hPeriod metric))
      (generalMetricRelativeC2InverseMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric 0) :=
    ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4).flip
        (regularFrameMetricInverseC2Matrix period hPeriod metric)).hasFDerivAt
  exact (hOuter.comp 0 hInner).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

@[simp]
theorem regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
        period hPeriod metric direction =
      -c2FiniteMatrixProduct
        (period := period) (hPeriod := hPeriod) 4 direction.1
          (regularFrameMetricInverseC2Matrix period hPeriod metric) := by
  rw [regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero,
    ContinuousLinearMap.comp_apply]
  have hDirection :=
    generalMetricRelativeC2InverseMatrixDerivativeAtZero_apply
      period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric direction
  calc
    _ = ((c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4).flip
            (regularFrameMetricInverseC2Matrix period hPeriod metric))
          (-direction.1) := congrArg _ hDirection
    _ = _ := ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4).flip
        (regularFrameMetricInverseC2Matrix period hPeriod metric)).map_neg
          direction.1

/-- Gate marker for `δg⁻¹ = -g⁻¹(δg)g⁻¹` in regular-frame C² form. -/
theorem regular_general_metric_c2_inverse_metric_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    HasFDerivAt
        (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric)
        (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
          period hPeriod metric) 0 ∧
      ∀ direction,
        regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
            period hPeriod metric direction =
          -c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) 4 direction.1
              (regularFrameMetricInverseC2Matrix period hPeriod metric) :=
  ⟨regularGeneralMetricC2InverseMetricMatrix_hasFDerivAt_zero
      period hPeriod metric,
    regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero_apply
      period hPeriod metric⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D
end JanusFormal
