import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

/-! # Global smooth Maxwell stress tensor in the regular frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The quadratic term `Σ_c F_{aρ} g^{ρσ} F_{bσ}` as a smooth scalar field. -/
def regularFrameMaxwellQuadraticCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : Fin 4) : SmoothScalarField period hPeriod :=
  ∑ component : Fin 2, ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
    smoothScalarFieldMul period hPeriod
      (smoothScalarFieldMul period hPeriod
        (regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component first lowerFirst)
        (regularFrameMetricInverseMatrix period hPeriod metric lowerFirst
          lowerSecond))
      (regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component second lowerSecond)

theorem regularFrameMaxwellQuadraticCoefficient_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameMaxwellQuadraticCoefficient period hPeriod metric potential
        first second point =
      ∑ component : Fin 2, ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component first lowerFirst point *
          regularFrameMetricInverseMatrix period hPeriod metric lowerFirst
              lowerSecond point *
          regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component second lowerSecond point := by
  let evaluation : SmoothScalarField period hPeriod →+ Real :=
    { toFun := fun field => field point
      map_zero' := rfl
      map_add' := by intros; rfl }
  change evaluation (∑ component : Fin 2,
    ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
      smoothScalarFieldMul period hPeriod
        (smoothScalarFieldMul period hPeriod
          (regularFrameGaugeCurvatureCoefficient period hPeriod metric
            potential component first lowerFirst)
          (regularFrameMetricInverseMatrix period hPeriod metric lowerFirst
            lowerSecond))
        (regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
          component second lowerSecond)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro component _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro lowerFirst _
  rw [map_sum]
  rfl

private theorem regularFrameMetricInverseMatrix_apply_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameMetricInverseMatrix period hPeriod metric first second point =
      regularFrameMetricInverseMatrix period hPeriod metric second first point := by
  change (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹
      first second =
    (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ second first
  have hMetric :
      (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
        regularFrameMetricMatrixMap period hPeriod metric point := by
    ext row column
    exact metric.metric.tensor.symmetric point _ _
  have hInverse := Matrix.transpose_nonsing_inv
    (A := regularFrameMetricMatrixMap period hPeriod metric point)
  rw [hMetric] at hInverse
  exact congrFun (congrFun hInverse second) first

theorem regularFrameMaxwellQuadraticCoefficient_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameMaxwellQuadraticCoefficient period hPeriod metric potential
        first second point =
      regularFrameMaxwellQuadraticCoefficient period hPeriod metric potential
        second first point := by
  rw [regularFrameMaxwellQuadraticCoefficient_apply,
    regularFrameMaxwellQuadraticCoefficient_apply]
  apply Finset.sum_congr rfl
  intro component _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lowerFirst _
  apply Finset.sum_congr rfl
  intro lowerSecond _
  rw [regularFrameMetricInverseMatrix_apply_symmetric]
  ring

/-- Derived covariant Maxwell stress coefficient
`T_ab = Σ_c F_{aρ} g^{ρσ} F_{bσ} - g_ab F²/4`. -/
def regularFrameMaxwellStressCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : Fin 4) : SmoothScalarField period hPeriod :=
  regularFrameMaxwellQuadraticCoefficient period hPeriod metric potential
      first second -
    (1 / 4 : Real) • smoothScalarFieldMul period hPeriod
      (regularFrameMetricMatrix period hPeriod metric first second)
      (regularFrameSmoothMaxwellPairing period hPeriod metric potential
        potential)

theorem regularFrameMaxwellStressCoefficient_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (first second : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameMaxwellStressCoefficient period hPeriod metric potential
        first second point =
      regularFrameMaxwellStressCoefficient period hPeriod metric potential
        second first point := by
  simp only [regularFrameMaxwellStressCoefficient,
    smoothScalarFieldSub_apply, smoothScalarFieldSmul_toFun,
    smoothScalarFieldMul_apply]
  rw [regularFrameMaxwellQuadraticCoefficient_symmetric period hPeriod metric
    potential first second point]
  rw [regularFrameMetricMatrix_apply, regularFrameMetricMatrix_apply,
    metric.metric.tensor.symmetric point (metric.frame first point)
      (metric.frame second point)]

/-- The Maxwell stress reconstructed as a genuine global smooth symmetric
covariant tensor. -/
def regularGeneralMetricMaxwellStressTensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (regularFrameMaxwellStressCoefficient period hPeriod metric potential
        first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (regularFrameDualCovector period hPeriod metric first)
        (regularFrameDualCovector period hPeriod metric second))

theorem regularGeneralMetricMaxwellStressTensor_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (left right : TangentSpace coverModelWithCorners point) :
    (regularGeneralMetricMaxwellStressTensor period hPeriod metric
        potential).tensor point left right =
      ∑ first : Fin 4, ∑ second : Fin 4,
        regularFrameMaxwellStressCoefficient period hPeriod metric potential
            first second point *
          ((1 / 2 : Real) *
              (regularFrameDualCovector period hPeriod metric first point left *
                regularFrameDualCovector period hPeriod metric second point
                  right) +
            (1 / 2 : Real) *
              (regularFrameDualCovector period hPeriod metric second point left *
                regularFrameDualCovector period hPeriod metric first point
                  right)) := by
  let evaluation :
      SmoothSymmetricCovariantTwoTensor period hPeriod →+ Real :=
    { toFun := fun current => current.tensor point left right
      map_zero' := rfl
      map_add' := by intros; rfl }
  change evaluation (∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (regularFrameMaxwellStressCoefficient period hPeriod metric potential
        first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (regularFrameDualCovector period hPeriod metric first)
        (regularFrameDualCovector period hPeriod metric second))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  rfl

/-- The global tensor has exactly the derived regular-frame stress
coefficients. -/
@[simp]
theorem regularGeneralMetricMaxwellStressTensor_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) (first second : Fin 4) :
    (regularGeneralMetricMaxwellStressTensor period hPeriod metric potential).tensor
        point (metric.frame first point) (metric.frame second point) =
      regularFrameMaxwellStressCoefficient period hPeriod metric potential
        first second point := by
  rw [regularGeneralMetricMaxwellStressTensor_apply]
  simp_rw [mul_add, Finset.sum_add_distrib]
  simp [regularFrameMaxwellStressCoefficient_symmetric period hPeriod metric
    potential]
  ring

/-- Gate marker: the metric variation of Maxwell now has a concrete smooth
stress-tensor candidate derived from `F = dA` and the inverse metric. -/
theorem regular_general_metric_global_smooth_maxwell_stress_tensor_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (point : EffectiveQuotient period hPeriod) (first second : Fin 4),
      (regularGeneralMetricMaxwellStressTensor period hPeriod metric
          potential).tensor point (metric.frame first point)
            (metric.frame second point) =
        regularFrameMaxwellStressCoefficient period hPeriod metric potential
          first second point :=
  regularGeneralMetricMaxwellStressTensor_frame period hPeriod metric potential

end
end P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
end JanusFormal
