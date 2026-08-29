import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D

/-!
# Metric and inverse metric in the genuine regular frame

The four vectors stored by `RegularGeneralLorentzMetric` are a true basis at
every point.  Reading the genuine metric in that basis gives a smooth matrix
with nowhere-zero determinant; its pointwise nonsingular inverse is therefore
another smooth matrix.  Both matrices lift exactly to the canonical scalar
`C²` algebra and satisfy the two-sided inverse identities there.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMetricInverse4D

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

open scoped Manifold ContDiff BigOperators Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCovariantAction4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module Real Matrix4 :=
  matrix4NormedSpace.toModule

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The genuine covariant metric matrix in its stored regular frame. -/
def regularFrameMetricMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothFiniteMatrix period hPeriod 4 :=
  fun row column =>
    { toFun := fun point =>
        metric.metric.tensor.tensor point
          (metric.frame row point) (metric.frame column point)
      contMDiff_toFun := by
        have hApplied :=
          metric.metric.tensor.tensor.contMDiff.clm_bundle_apply
            (metric.frame row).contMDiff |>.clm_bundle_apply
              (metric.frame column).contMDiff
        intro point
        have hAppliedAt := hApplied point
        rw [Bundle.contMDiffAt_section] at hAppliedAt
        simpa using hAppliedAt }

@[simp]
theorem regularFrameMetricMatrix_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (row column : Fin 4) :
    regularFrameMetricMatrix period hPeriod metric row column point =
      metric.metric.tensor.tensor point
        (metric.frame row point) (metric.frame column point) :=
  rfl

/-- The same smooth matrix as a matrix-valued map. -/
def regularFrameMetricMatrixMap
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    EffectiveQuotient period hPeriod → Matrix4 :=
  fun point row column =>
    regularFrameMetricMatrix period hPeriod metric row column point

theorem regularFrameMetricMatrixMap_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Matrix4) ∞
      (regularFrameMetricMatrixMap period hPeriod metric) := by
  classical
  have hExpansion :
      regularFrameMetricMatrixMap period hPeriod metric =
        fun point => ∑ row : Fin 4, ∑ column : Fin 4,
          regularFrameMetricMatrix period hPeriod metric row column point •
            Matrix.single row column 1 := by
    funext point
    ext row column
    simp only [regularFrameMetricMatrixMap]
    rw [Matrix.sum_apply]
    symm
    calc
      (∑ current : Fin 4,
          (∑ currentColumn : Fin 4,
            regularFrameMetricMatrix period hPeriod metric
                current currentColumn point •
              Matrix.single current currentColumn 1) row column) =
          (∑ currentColumn : Fin 4,
            regularFrameMetricMatrix period hPeriod metric
                row currentColumn point •
              Matrix.single row currentColumn 1) row column := by
        apply Finset.sum_eq_single row
        · intro other _ hOther
          rw [Matrix.sum_apply]
          apply Finset.sum_eq_zero
          intro current _
          simp [hOther]
        · simp
      _ = regularFrameMetricMatrix period hPeriod metric row column point := by
        rw [Matrix.sum_apply]
        calc
          (∑ current : Fin 4,
              (regularFrameMetricMatrix period hPeriod metric row current point •
                Matrix.single row current 1) row column) =
              (regularFrameMetricMatrix period hPeriod metric row column point •
                Matrix.single row column 1) row column := by
            apply Finset.sum_eq_single column
            · intro other _ hOther
              simp [hOther]
            · simp
          _ = regularFrameMetricMatrix period hPeriod metric row column point := by
            simp
  rw [hExpansion]
  apply contMDiff_finsetSum
  intro row _
  apply contMDiff_finsetSum
  intro column _
  exact (regularFrameMetricMatrix period hPeriod metric row column)
    |>.contMDiff_toFun.smul contMDiff_const

private def regularFrameMetricBilinForm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    LinearMap.BilinForm Real
      (TangentSpace coverModelWithCorners point) :=
  (metric.metric.tensor.tensor point).toBilinForm

private theorem regularFrameMetricBilinForm_nondegenerate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (regularFrameMetricBilinForm period hPeriod metric point).Nondegenerate := by
  constructor
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric.metric
    apply ContinuousLinearMap.ext
    intro second
    simpa [regularFrameMetricBilinForm] using hVector second
  · intro vector hVector
    apply metric_nondegenerate_at period hPeriod metric.metric
    apply ContinuousLinearMap.ext
    intro second
    rw [metric.metric.tensor.symmetric]
    simpa [regularFrameMetricBilinForm] using hVector second

theorem regularFrameMetricMatrix_det_ne_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (regularFrameMetricMatrixMap period hPeriod metric point).det ≠ 0 := by
  have hDet :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (regularMetricBasisAt period hPeriod metric point)).mp
      (regularFrameMetricBilinForm_nondegenerate period hPeriod metric point)
  have hMatrix :
      regularFrameMetricMatrixMap period hPeriod metric point =
        LinearMap.BilinForm.toMatrix
          (regularMetricBasisAt period hPeriod metric point)
          (regularFrameMetricBilinForm period hPeriod metric point) := by
    ext row column
    simp [regularFrameMetricMatrixMap, regularFrameMetricMatrix,
      regularMetricBasisAt, regularFrameMetricBilinForm,
      RegularGeneralLorentzMetric.frame_eq_basisFun]
  rw [hMatrix]
  exact hDet

theorem regularFrameMetricMatrix_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    IsUnit (regularFrameMetricMatrixMap period hPeriod metric point) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr
    (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point)

/-- The genuine pointwise inverse metric matrix in the same regular frame. -/
def regularFrameMetricInverseMatrixMap
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    EffectiveQuotient period hPeriod → Matrix4 :=
  fun point =>
    (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹

theorem regularFrameMetricInverseMatrixMap_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Matrix4) ∞
      (regularFrameMetricInverseMatrixMap period hPeriod metric) := by
  intro point
  have hUnit := regularFrameMetricMatrix_isUnit
    period hPeriod metric point
  have hFormula :
      regularFrameMetricInverseMatrixMap period hPeriod metric =
        fun current => Ring.inverse
          (regularFrameMetricMatrixMap period hPeriod metric current) := by
    funext current
    exact Matrix.nonsing_inv_eq_ringInverse
      (A := regularFrameMetricMatrixMap period hPeriod metric current)
  rw [hFormula]
  have hInverse : ContDiffAt Real ∞
      (Ring.inverse : Matrix4 → Matrix4) (hUnit.unit : Matrix4) :=
    contDiffAt_ringInverse Real hUnit.unit
  rw [hUnit.unit_spec] at hInverse
  exact hInverse.contMDiffAt.comp point
    (regularFrameMetricMatrixMap_contMDiff
      period hPeriod metric).contMDiffAt

private def matrixEntryCLM (row column : Fin 4) :
    Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Entrywise bundled smooth inverse metric matrix. -/
def regularFrameMetricInverseMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothFiniteMatrix period hPeriod 4 :=
  fun row column =>
    { toFun := fun point =>
        regularFrameMetricInverseMatrixMap period hPeriod metric point
          row column
      contMDiff_toFun :=
        (matrixEntryCLM row column).contMDiff.comp
          (regularFrameMetricInverseMatrixMap_contMDiff
            period hPeriod metric) }

theorem regularFrameMetricMatrix_mul_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    smoothFiniteMatrixProduct period hPeriod 4
        (regularFrameMetricMatrix period hPeriod metric)
        (regularFrameMetricInverseMatrix period hPeriod metric) =
      smoothFiniteMatrixIdentity period hPeriod 4 := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hProduct := Matrix.mul_nonsing_inv
    (regularFrameMetricMatrixMap period hPeriod metric point)
    (isUnit_iff_ne_zero.mpr
      (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hEntry := congrFun (congrFun hProduct row) column
  simpa [smoothFiniteMatrixProduct, smoothFiniteMatrixIdentity,
    regularFrameMetricMatrixMap, regularFrameMetricInverseMatrixMap,
    regularFrameMetricInverseMatrix,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, Matrix.mul_apply, Matrix.one_apply,
    constantSmoothField] using hEntry

theorem regularFrameMetricInverse_mul_matrix
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    smoothFiniteMatrixProduct period hPeriod 4
        (regularFrameMetricInverseMatrix period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric) =
      smoothFiniteMatrixIdentity period hPeriod 4 := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hProduct := Matrix.nonsing_inv_mul
    (regularFrameMetricMatrixMap period hPeriod metric point)
    (isUnit_iff_ne_zero.mpr
      (regularFrameMetricMatrix_det_ne_zero period hPeriod metric point))
  have hEntry := congrFun (congrFun hProduct row) column
  simpa [smoothFiniteMatrixProduct, smoothFiniteMatrixIdentity,
    regularFrameMetricMatrixMap, regularFrameMetricInverseMatrixMap,
    regularFrameMetricInverseMatrix,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, Matrix.mul_apply, Matrix.one_apply,
    constantSmoothField] using hEntry

/-- Exact `C²` lifts of the metric and inverse metric matrices. -/
def regularFrameMetricC2Matrix
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    C2FiniteMatrix period hPeriod 4 :=
  smoothFiniteMatrixToC2 period hPeriod 4
    (regularFrameMetricMatrix period hPeriod metric)

def regularFrameMetricInverseC2Matrix
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    C2FiniteMatrix period hPeriod 4 :=
  smoothFiniteMatrixToC2 period hPeriod 4
    (regularFrameMetricInverseMatrix period hPeriod metric)

theorem regularFrameMetricC2Matrix_mul_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (regularFrameMetricC2Matrix period hPeriod metric)
        (regularFrameMetricInverseC2Matrix period hPeriod metric) =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  rw [regularFrameMetricC2Matrix, regularFrameMetricInverseC2Matrix,
    c2FiniteMatrixProduct_smooth,
    regularFrameMetricMatrix_mul_inverse]
  rfl

theorem regularFrameMetricInverseC2Matrix_mul_matrix
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (regularFrameMetricInverseC2Matrix period hPeriod metric)
        (regularFrameMetricC2Matrix period hPeriod metric) =
      c2FiniteMatrixIdentity period hPeriod 4 := by
  rw [regularFrameMetricC2Matrix, regularFrameMetricInverseC2Matrix,
    c2FiniteMatrixProduct_smooth,
    regularFrameMetricInverse_mul_matrix]
  rfl

/-- Summary gate for the genuine regular-frame metric inverse. -/
theorem regular_frame_metric_inverse_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (∀ point,
      (regularFrameMetricMatrixMap period hPeriod metric point).det ≠ 0) ∧
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          (regularFrameMetricC2Matrix period hPeriod metric)
          (regularFrameMetricInverseC2Matrix period hPeriod metric) =
        c2FiniteMatrixIdentity period hPeriod 4 ∧
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          (regularFrameMetricInverseC2Matrix period hPeriod metric)
          (regularFrameMetricC2Matrix period hPeriod metric) =
        c2FiniteMatrixIdentity period hPeriod 4 := by
  exact ⟨regularFrameMetricMatrix_det_ne_zero period hPeriod metric,
    regularFrameMetricC2Matrix_mul_inverse period hPeriod metric,
    regularFrameMetricInverseC2Matrix_mul_matrix period hPeriod metric⟩

end

end P0EFTJanusProgramPRegularFrameMetricInverse4D
end JanusFormal
