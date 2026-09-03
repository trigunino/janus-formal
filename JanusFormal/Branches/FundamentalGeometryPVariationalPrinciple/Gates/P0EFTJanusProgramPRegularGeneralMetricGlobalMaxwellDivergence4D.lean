import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMetricInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D

/-!
# Global Maxwell curvature and divergence for a regular metric

The smooth regular-frame Cartan coefficients are reconstructed as a genuine
covariant two-tensor with the metric-induced dual frame.  The now-generic
global tensor-divergence construction then produces `∇^μ F_μν` as a smooth
intrinsic covector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev SmoothCovector :=
  SmoothCotangentField period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise multiplication of a smooth scalar and smooth covector. -/
def smoothScalarSMulCovector
    (scalar : SmoothScalarField period hPeriod)
    (covector : SmoothCovector period hPeriod) :
    SmoothCovector period hPeriod where
  toFun := fun point => scalar point • covector point
  contMDiff_toFun :=
    scalar.contMDiff_toFun.smul_section covector.contMDiff

@[simp]
theorem smoothScalarSMulCovector_apply
    (scalar : SmoothScalarField period hPeriod)
    (covector : SmoothCovector period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    smoothScalarSMulCovector period hPeriod scalar covector point vector =
      scalar point * covector point vector :=
  rfl

/-- Metric dual of one vector of the stored regular frame. -/
def regularFrameMetricCovector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4) : SmoothCovector period hPeriod :=
  generalMetricFrameCovector period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric.tensor index

@[simp]
theorem regularFrameMetricCovector_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    regularFrameMetricCovector period hPeriod metric index point vector =
      metric.metric.tensor.tensor point (metric.frame index point) vector :=
  rfl

/-- The genuine smooth coframe reconstructed from the inverse Gram matrix. -/
def regularFrameDualCovector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4) : SmoothCovector period hPeriod :=
  ∑ column : Fin 4,
    smoothScalarSMulCovector period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod metric index column)
      (regularFrameMetricCovector period hPeriod metric column)

theorem regularFrameDualCovector_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4)
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    regularFrameDualCovector period hPeriod metric index point vector =
      ∑ column : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod metric index column
            point *
          metric.metric.tensor.tensor point (metric.frame column point)
            vector := by
  let evaluation : SmoothCovector period hPeriod →+ Real :=
    { toFun := fun current => current point vector
      map_zero' := rfl
      map_add' := by intros; rfl }
  change evaluation (∑ column : Fin 4,
    smoothScalarSMulCovector period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod metric index column)
      (regularFrameMetricCovector period hPeriod metric column)) = _
  rw [map_sum]
  rfl

/-- The reconstructed coframe is dual to the stored regular frame. -/
@[simp]
theorem regularFrameDualCovector_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index frameIndex : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameDualCovector period hPeriod metric index point
        (metric.frame frameIndex point) =
      if index = frameIndex then 1 else 0 := by
  have hMatrix := congrArg
    (fun matrix => matrix index frameIndex)
    (regularFrameMetricInverse_mul_matrix period hPeriod metric)
  have hPoint := congrArg
    (fun field : SmoothScalarField period hPeriod => field point) hMatrix
  rw [regularFrameDualCovector_apply]
  change (∑ column : Fin 4,
      regularFrameMetricInverseMatrix period hPeriod metric index column point *
        metric.metric.tensor.tensor point (metric.frame column point)
          (metric.frame frameIndex point)) =
    (if index = frameIndex then 1 else 0) at hPoint
  exact hPoint

/-- Intrinsic Maxwell curvature reconstructed from its smooth Cartan frame
coefficients. -/
def regularGlobalGaugeCurvatureTensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) : SmoothCovariantTwoTensor period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulCovariantTensor period hPeriod
      (regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second)
      (smoothBulkCovectorOuterProduct period hPeriod
        (regularFrameDualCovector period hPeriod metric first)
        (regularFrameDualCovector period hPeriod metric second))

theorem regularGlobalGaugeCurvatureTensor_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (left right : TangentSpace coverModelWithCorners point) :
    regularGlobalGaugeCurvatureTensor period hPeriod metric potential component
        point left right =
      ∑ first : Fin 4, ∑ second : Fin 4,
        regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component first second point *
          (regularFrameDualCovector period hPeriod metric first point left *
            regularFrameDualCovector period hPeriod metric second point
              right) := by
  let evaluation : SmoothCovariantTwoTensor period hPeriod →+ Real :=
    { toFun := fun current => current point left right
      map_zero' := rfl
      map_add' := by intros; rfl }
  change evaluation (∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulCovariantTensor period hPeriod
      (regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second)
      (smoothBulkCovectorOuterProduct period hPeriod
        (regularFrameDualCovector period hPeriod metric first)
        (regularFrameDualCovector period hPeriod metric second))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  rfl

/-- The global tensor has exactly the original Cartan coefficients. -/
@[simp]
theorem regularGlobalGaugeCurvatureTensor_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod)
    (first second : Fin 4) :
    regularGlobalGaugeCurvatureTensor period hPeriod metric potential component
        point (metric.frame first point) (metric.frame second point) =
      regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second point := by
  rw [regularGlobalGaugeCurvatureTensor_apply]
  simp

/-- On every holonomic chart, the global tensor readings on the regular frame
are exactly the genuine exterior derivative `dA`. -/
theorem regularGlobalGaugeCurvatureTensor_eq_localGaugeCurvature
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D.Vector4)
    (first second : Fin 4) :
    regularGlobalGaugeCurvatureTensor period hPeriod metric potential component
        (patch.coordinateMap coordinate)
        (metric.frame first (patch.coordinateMap coordinate))
        (metric.frame second (patch.coordinateMap coordinate)) =
      localGaugeCurvature period hPeriod potential component patch coordinate
        ![pulledRegularFrameVector period hPeriod metric patch first coordinate,
          pulledRegularFrameVector period hPeriod metric patch second
            coordinate] := by
  rw [regularGlobalGaugeCurvatureTensor_frame]
  exact regularFrameGaugeCurvatureCoefficient_eq_localGaugeCurvature
    period hPeriod metric potential component patch coordinate first second

/-- The Maxwell equation left-hand side as a genuine smooth global covector. -/
def regularGlobalMaxwellDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :=
  globalGeneralMetricSymmetricTensorDivergence period hPeriod metric.metric
    (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
      component)

/-- Every chart computes the same global Maxwell divergence covector. -/
theorem regularGlobalMaxwellDivergence_eq_local
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D.Vector4) :
    regularGlobalMaxwellDivergence period hPeriod metric potential component
        (patch.coordinateMap coordinate) =
      localSymmetricTensorDivergenceIntrinsicCovector period hPeriod
        metric.metric
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component) patch coordinate := by
  exact globalGeneralMetricSymmetricTensorDivergenceAt_eq_local period hPeriod
    metric.metric
    (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
      component) patch coordinate

/-- Summary gate: authentic global Maxwell curvature and its smooth covariant
divergence are both available. -/
theorem regular_general_metric_global_maxwell_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    (∀ component patch coordinate first second,
      regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component (patch.coordinateMap coordinate)
          (metric.frame first (patch.coordinateMap coordinate))
          (metric.frame second (patch.coordinateMap coordinate)) =
        localGaugeCurvature period hPeriod potential component patch coordinate
          ![pulledRegularFrameVector period hPeriod metric patch first
              coordinate,
            pulledRegularFrameVector period hPeriod metric patch second
              coordinate]) ∧
      (∀ component patch coordinate,
        regularGlobalMaxwellDivergence period hPeriod metric potential component
            (patch.coordinateMap coordinate) =
          localSymmetricTensorDivergenceIntrinsicCovector period hPeriod
            metric.metric
            (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
              component) patch coordinate) := by
  exact ⟨regularGlobalGaugeCurvatureTensor_eq_localGaugeCurvature
      period hPeriod metric potential,
    regularGlobalMaxwellDivergence_eq_local period hPeriod metric potential⟩

end

end P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
end JanusFormal
