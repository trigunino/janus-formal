import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Fiberwise Cartan residual

This reusable core proves that `X (A Y) - A [X,Y]` is tensorial in `Y`
and packages its value as a cotangent-fiber map.  A concrete gauge-potential
gate only has to provide smoothness of `x ↦ A x (Y x)`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGaugePotentialCartanFiber4D

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

private abbrev CovectorSection
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] :=
  ∀ point : M, TangentSpace I point →L[ℝ] ℝ

/-- The pointwise Cartan residual of a covector section. -/
def gaugePotentialCartanResidualAt
    (first : TangentSection I M)
    (potential : CovectorSection I M)
    (point : M)
    (second : TangentSection I M) : ℝ :=
  mvfderiv I (fun current => potential current (second current))
      point (first point) -
    potential point (VectorField.mlieBracket I first second point)

/-- The Cartan residual depends linearly only on the value of its second
vector field at the selected point. -/
theorem gaugePotentialCartanResidualAt_tensorial
    (first : TangentSection I M)
    (potential : CovectorSection I M)
    (point : M)
    (hPotential :
      ∀ second : TangentSection I M,
        MDiffAt (T% second) point →
          MDiffAt (fun current => potential current (second current)) point) :
    TensorialAt I E
      (gaugePotentialCartanResidualAt I first potential point) point where
  smul := by
    intro scalar second hScalar hSecond
    have hEvaluation := hPotential second hSecond
    unfold gaugePotentialCartanResidualAt
    rw [show
      (fun current => potential current ((scalar • second) current)) =
        scalar * (fun current => potential current (second current)) by
      funext current
      simp]
    rw [mvfderiv_mul hScalar hEvaluation]
    rw [VectorField.mlieBracket_smul_right hScalar hSecond]
    simp only [add_apply, smul_apply, smul_eq_mul, map_add, map_smul]
    ring
  add := by
    intro second third hSecond hThird
    have hSecondEvaluation := hPotential second hSecond
    have hThirdEvaluation := hPotential third hThird
    unfold gaugePotentialCartanResidualAt
    rw [show
      (fun current => potential current ((second + third) current)) =
        (fun current => potential current (second current)) +
          fun current => potential current (third current) by
      funext current
      exact map_add _ _ _]
    rw [mvfderiv_add hSecondEvaluation hThirdEvaluation]
    rw [VectorField.mlieBracket_add_right hSecond hThird]
    simp only [add_apply, map_add]
    ring

/-- The residual is additive in its first vector field at points where both
first vector fields are differentiable. -/
theorem gaugePotentialCartanResidualAt_add_first
    (first third : TangentSection I M)
    (potential : CovectorSection I M)
    (point : M)
    (second : TangentSection I M)
    (hFirst : MDiffAt (T% first) point)
    (hThird : MDiffAt (T% third) point) :
    gaugePotentialCartanResidualAt I (first + third) potential point second =
      gaugePotentialCartanResidualAt I first potential point second +
        gaugePotentialCartanResidualAt I third potential point second := by
  simp only [gaugePotentialCartanResidualAt, Pi.add_apply, map_add,
    VectorField.mlieBracket_add_left hFirst hThird]
  ring

/-- The residual is homogeneous in its first vector field at points where
that vector field is differentiable. -/
theorem gaugePotentialCartanResidualAt_smul_first
    (scalar : ℝ)
    (first : TangentSection I M)
    (potential : CovectorSection I M)
    (point : M)
    (second : TangentSection I M)
    (hFirst : MDiffAt (T% first) point) :
    gaugePotentialCartanResidualAt I (scalar • first) potential point second =
      scalar • gaugePotentialCartanResidualAt I first potential point second := by
  simp only [gaugePotentialCartanResidualAt, Pi.smul_apply, map_smul,
    VectorField.mlieBracket_const_smul_left hFirst, smul_eq_mul]
  ring

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- The residual is additive in the covector section. -/
theorem gaugePotentialCartanResidualAt_add_potential
    (first : TangentSection I M)
    (potential extra : CovectorSection I M)
    (point : M)
    (second : TangentSection I M)
    (hPotential :
      MDiffAt (fun current => potential current (second current)) point)
    (hExtra :
      MDiffAt (fun current => extra current (second current)) point) :
    gaugePotentialCartanResidualAt I first (potential + extra) point second =
      gaugePotentialCartanResidualAt I first potential point second +
        gaugePotentialCartanResidualAt I first extra point second := by
  unfold gaugePotentialCartanResidualAt
  rw [show
    (fun current => (potential + extra) current (second current)) =
      (fun current => potential current (second current)) +
        fun current => extra current (second current) by
    funext current
    rfl]
  rw [mvfderiv_add hPotential hExtra]
  simp only [Pi.add_apply, add_apply]
  ring

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- The residual is homogeneous in the covector section. -/
theorem gaugePotentialCartanResidualAt_smul_potential
    (scalar : ℝ)
    (first : TangentSection I M)
    (potential : CovectorSection I M)
    (point : M)
    (second : TangentSection I M)
    (hPotential :
      MDiffAt (fun current => potential current (second current)) point) :
    gaugePotentialCartanResidualAt I first (scalar • potential) point second =
      scalar • gaugePotentialCartanResidualAt I first potential point second := by
  unfold gaugePotentialCartanResidualAt
  rw [show
    (fun current => (scalar • potential) current (second current)) =
      (fun _ : M => scalar) *
        fun current => potential current (second current) by
    funext current
    simp]
  rw [mvfderiv_mul mdifferentiableAt_const hPotential]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul,
    mvfderiv_const, smul_zero, add_zero]
  ring

/-- Intrinsic cotangent-fiber value of the Cartan residual. -/
def gaugePotentialCartanFiberCovector
    [FiniteDimensional ℝ E]
    (first : TangentSection I M)
    (potential : CovectorSection I M)
    (point : M)
    (hPotential :
      ∀ second : TangentSection I M,
        MDiffAt (T% second) point →
          MDiffAt (fun current => potential current (second current)) point) :
    TangentSpace I point →L[ℝ] ℝ :=
  TensorialAt.mkHom
    (gaugePotentialCartanResidualAt I first potential point) point
    (gaugePotentialCartanResidualAt_tensorial I first potential point hPotential)

/-- Evaluating the fiber covector on a smooth section recovers the residual. -/
theorem gaugePotentialCartanFiberCovector_apply
    [FiniteDimensional ℝ E]
    (first : TangentSection I M)
    (potential : CovectorSection I M)
    (point : M)
    (hPotential :
      ∀ second : TangentSection I M,
        MDiffAt (T% second) point →
          MDiffAt (fun current => potential current (second current)) point)
    (second : TangentSection I M)
    (hSecond : MDiffAt (T% second) point) :
    gaugePotentialCartanFiberCovector I first potential point hPotential
        (second point) =
      gaugePotentialCartanResidualAt I first potential point second := by
  exact TensorialAt.mkHom_apply
    (gaugePotentialCartanResidualAt_tensorial I first potential point hPotential)
    hSecond

end

end P0EFTJanusMappingTorusGaugePotentialCartanFiber4D
end JanusFormal
