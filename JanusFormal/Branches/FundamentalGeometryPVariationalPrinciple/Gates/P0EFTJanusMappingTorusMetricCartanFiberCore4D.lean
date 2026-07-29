import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Fiberwise metric Cartan residual

This reusable core proves that
`X (h Y Z) - h [X,Y] Z - h Y [X,Z]` is tensorial in `Y` and `Z`,
then packages it as a covariant two-tensor in the selected tangent fiber.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMetricCartanFiberCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

variable
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

private abbrev TangentSection
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :=
  ∀ point : M, TangentSpace I point

private abbrev CovariantTwoTensorSection
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :=
  ∀ point : M,
    TangentSpace I point →L[ℝ] TangentSpace I point →L[ℝ] ℝ

/-- Pointwise Cartan residual of a covariant two-tensor section. -/
def metricCartanResidualAt
    (acting : TangentSection I M)
    (tensor : CovariantTwoTensorSection I M)
    (point : M)
    (first second : TangentSection I M) : ℝ :=
  mvfderiv I
      (fun current => tensor current (first current) (second current))
      point (acting point) -
    tensor point (VectorField.mlieBracket I acting first point)
      (second point) -
    tensor point (first point)
      (VectorField.mlieBracket I acting second point)

/-- The metric Cartan residual is tensorial in its first test field. -/
theorem metricCartanResidualAt_tensorial_first
    (acting : TangentSection I M)
    (tensor : CovariantTwoTensorSection I M)
    (point : M)
    (hTensor :
      ∀ first second : TangentSection I M,
        MDiffAt (T% first) point →
        MDiffAt (T% second) point →
        MDiffAt
          (fun current => tensor current (first current) (second current))
          point)
    (second : TangentSection I M)
    (hSecond : MDiffAt (T% second) point) :
    TensorialAt I E
      (fun first =>
        metricCartanResidualAt I acting tensor point first second) point where
  smul := by
    intro scalar first hScalar hFirst
    have hEvaluation := hTensor first second hFirst hSecond
    unfold metricCartanResidualAt
    rw [show
      (fun current =>
        tensor current ((scalar • first) current) (second current)) =
        scalar *
          fun current => tensor current (first current) (second current) by
      funext current
      simp]
    rw [mvfderiv_mul hScalar hEvaluation]
    rw [VectorField.mlieBracket_smul_right hScalar hFirst]
    rw [show (scalar • first) point = scalar point • first point by rfl]
    simp only [smul_apply, add_apply, map_add, map_smul, smul_eq_mul]
    ring
  add := by
    intro first third hFirst hThird
    have hFirstEvaluation := hTensor first second hFirst hSecond
    have hThirdEvaluation := hTensor third second hThird hSecond
    unfold metricCartanResidualAt
    rw [show
      (fun current =>
        tensor current ((first + third) current) (second current)) =
        (fun current => tensor current (first current) (second current)) +
          fun current => tensor current (third current) (second current) by
      funext current
      simp]
    rw [mvfderiv_add hFirstEvaluation hThirdEvaluation]
    rw [VectorField.mlieBracket_add_right hFirst hThird]
    simp only [Pi.add_apply, add_apply, map_add]
    ring

/-- The metric Cartan residual is tensorial in its second test field. -/
theorem metricCartanResidualAt_tensorial_second
    (acting : TangentSection I M)
    (tensor : CovariantTwoTensorSection I M)
    (point : M)
    (hTensor :
      ∀ first second : TangentSection I M,
        MDiffAt (T% first) point →
        MDiffAt (T% second) point →
        MDiffAt
          (fun current => tensor current (first current) (second current))
          point)
    (first : TangentSection I M)
    (hFirst : MDiffAt (T% first) point) :
    TensorialAt I E
      (metricCartanResidualAt I acting tensor point first) point where
  smul := by
    intro scalar second hScalar hSecond
    have hEvaluation := hTensor first second hFirst hSecond
    unfold metricCartanResidualAt
    rw [show
      (fun current =>
        tensor current (first current) ((scalar • second) current)) =
        scalar *
          fun current => tensor current (first current) (second current) by
      funext current
      simp]
    rw [mvfderiv_mul hScalar hEvaluation]
    rw [VectorField.mlieBracket_smul_right hScalar hSecond]
    rw [show (scalar • second) point = scalar point • second point by rfl]
    simp only [smul_apply, add_apply, map_add, map_smul, smul_eq_mul]
    ring
  add := by
    intro second third hSecond hThird
    have hSecondEvaluation := hTensor first second hFirst hSecond
    have hThirdEvaluation := hTensor first third hFirst hThird
    unfold metricCartanResidualAt
    rw [show
      (fun current =>
        tensor current (first current) ((second + third) current)) =
        (fun current => tensor current (first current) (second current)) +
          fun current => tensor current (first current) (third current) by
      funext current
      simp]
    rw [mvfderiv_add hSecondEvaluation hThirdEvaluation]
    rw [VectorField.mlieBracket_add_right hSecond hThird]
    simp only [Pi.add_apply, add_apply, map_add]
    ring

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- Symmetry of the original tensor is preserved by the residual. -/
theorem metricCartanResidualAt_symm
    (acting : TangentSection I M)
    (tensor : CovariantTwoTensorSection I M)
    (point : M)
    (hSymm : ∀ current first second,
      tensor current first second = tensor current second first)
    (first second : TangentSection I M) :
    metricCartanResidualAt I acting tensor point first second =
      metricCartanResidualAt I acting tensor point second first := by
  unfold metricCartanResidualAt
  rw [show
    (fun current => tensor current (first current) (second current)) =
      fun current => tensor current (second current) (first current) by
    funext current
    exact hSymm current _ _]
  rw [hSymm point
    (VectorField.mlieBracket I acting first point) (second point)]
  rw [hSymm point (first point)
    (VectorField.mlieBracket I acting second point)]
  ring

/-- Intrinsic covariant two-tensor value of the metric Cartan residual. -/
def metricCartanFiberCovariantTwoTensor
    [FiniteDimensional ℝ E]
    (acting : TangentSection I M)
    (tensor : CovariantTwoTensorSection I M)
    (point : M)
    (hTensor :
      ∀ first second : TangentSection I M,
        MDiffAt (T% first) point →
        MDiffAt (T% second) point →
        MDiffAt
          (fun current => tensor current (first current) (second current))
          point) :
    TangentSpace I point →L[ℝ] TangentSpace I point →L[ℝ] ℝ :=
  TensorialAt.mkHom₂
    (metricCartanResidualAt I acting tensor point) point
    (metricCartanResidualAt_tensorial_first I acting tensor point hTensor)
    (metricCartanResidualAt_tensorial_second I acting tensor point hTensor)

/-- Evaluation on smooth test fields recovers the Cartan residual. -/
theorem metricCartanFiberCovariantTwoTensor_apply
    [FiniteDimensional ℝ E]
    (acting : TangentSection I M)
    (tensor : CovariantTwoTensorSection I M)
    (point : M)
    (hTensor :
      ∀ first second : TangentSection I M,
        MDiffAt (T% first) point →
        MDiffAt (T% second) point →
        MDiffAt
          (fun current => tensor current (first current) (second current))
          point)
    (first second : TangentSection I M)
    (hFirst : MDiffAt (T% first) point)
    (hSecond : MDiffAt (T% second) point) :
    metricCartanFiberCovariantTwoTensor I acting tensor point hTensor
        (first point) (second point) =
      metricCartanResidualAt I acting tensor point first second := by
  exact TensorialAt.mkHom₂_apply
    (metricCartanResidualAt_tensorial_first I acting tensor point hTensor)
    (metricCartanResidualAt_tensorial_second I acting tensor point hTensor)
    hFirst hSecond

/-- The packaged fiber tensor remains symmetric. -/
theorem metricCartanFiberCovariantTwoTensor_symm
    [FiniteDimensional ℝ E]
    (acting : TangentSection I M)
    (tensor : CovariantTwoTensorSection I M)
    (point : M)
    (hTensor :
      ∀ first second : TangentSection I M,
        MDiffAt (T% first) point →
        MDiffAt (T% second) point →
        MDiffAt
          (fun current => tensor current (first current) (second current))
          point)
    (hSymm : ∀ current first second,
      tensor current first second = tensor current second first)
    (first second : TangentSpace I point) :
    metricCartanFiberCovariantTwoTensor I acting tensor point hTensor
        first second =
      metricCartanFiberCovariantTwoTensor I acting tensor point hTensor
        second first := by
  unfold metricCartanFiberCovariantTwoTensor
  rw [TensorialAt.mkHom₂_apply_eq_extend,
    TensorialAt.mkHom₂_apply_eq_extend]
  exact metricCartanResidualAt_symm I acting tensor point hSymm _ _

end

end P0EFTJanusMappingTorusMetricCartanFiberCore4D
end JanusFormal
