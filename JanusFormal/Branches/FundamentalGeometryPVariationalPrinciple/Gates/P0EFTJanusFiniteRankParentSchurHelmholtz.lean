import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteRankParentSchurHelmholtz

set_option autoImplicit false

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/--
A single scalar bulk coefficient coupled to an arbitrary finite nonempty family
of boundary coefficients.  This is only a finite-dimensional coefficient
model; it does not construct the Janus bulk PDE or its microscopic parent.
-/
structure FiniteRankParentData (ι : Type*) [Fintype ι] [Nonempty ι] where
  bulkCoefficient : ℝ
  coupling : ι → ℝ
  boundaryHessian : ι → ι → ℝ
  boundaryHessian_symmetric :
    ∀ i j, boundaryHessian i j = boundaryHessian j i
  bulkCoefficientNonzero : bulkCoefficient ≠ 0

/-- Contraction of the bulk-to-boundary coupling with boundary data. -/
noncomputable def couplingPairing
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) : ℝ :=
  ∑ i, data.coupling i * boundary i

/-- Quadratic form of the unreduced boundary Hessian. -/
noncomputable def boundaryQuadratic
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) : ℝ :=
  ∑ i, ∑ j,
    boundary i * data.boundaryHessian i j * boundary j

/-- Finite parent bulk-plus-boundary quadratic action. -/
noncomputable def parentAction
    (data : FiniteRankParentData ι)
    (bulk : ℝ)
    (boundary : ι → ℝ) : ℝ :=
  data.bulkCoefficient * bulk ^ 2 / 2 +
    bulk * couplingPairing data boundary +
    boundaryQuadratic data boundary / 2

/-- Bulk Euler derivative at fixed boundary coefficients. -/
noncomputable def bulkEulerDerivative
    (data : FiniteRankParentData ι)
    (bulk : ℝ)
    (boundary : ι → ℝ) : ℝ :=
  data.bulkCoefficient * bulk + couplingPairing data boundary

/-- The unique stationary scalar bulk coefficient. -/
noncomputable def stationaryBulk
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) : ℝ :=
  -couplingPairing data boundary / data.bulkCoefficient

theorem stationary_bulk_solves_euler
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    bulkEulerDerivative data (stationaryBulk data boundary) boundary = 0 := by
  unfold bulkEulerDerivative stationaryBulk
  field_simp [data.bulkCoefficientNonzero]
  ring

theorem stationary_bulk_unique
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (bulk : ℝ)
    (hBulk : bulkEulerDerivative data bulk boundary = 0) :
    bulk = stationaryBulk data boundary := by
  unfold bulkEulerDerivative at hBulk
  unfold stationaryBulk
  apply (eq_div_iff data.bulkCoefficientNonzero).2
  nlinarith

theorem stationary_bulk_exists_unique
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    ∃! bulk : ℝ, bulkEulerDerivative data bulk boundary = 0 := by
  refine ⟨stationaryBulk data boundary,
    stationary_bulk_solves_euler data boundary, ?_⟩
  intro bulk hBulk
  exact stationary_bulk_unique data boundary bulk hBulk

/-- The finite-rank Schur complement `Bᵢⱼ - cᵢ cⱼ / a`. -/
noncomputable def reducedBoundaryHessian
    (data : FiniteRankParentData ι)
    (i j : ι) : ℝ :=
  data.boundaryHessian i j -
    data.coupling i * data.coupling j / data.bulkCoefficient

/-- The Schur-reduced boundary Hessian remains reciprocal. -/
theorem reduced_boundary_hessian_symmetric
    (data : FiniteRankParentData ι)
    (i j : ι) :
    reducedBoundaryHessian data i j =
      reducedBoundaryHessian data j i := by
  unfold reducedBoundaryHessian
  rw [data.boundaryHessian_symmetric i j]
  ring

/-- Finite coefficient form of the Helmholtz reciprocity condition. -/
def FiniteHelmholtz
    (kernel : ι → ι → ℝ) : Prop :=
  ∀ i j, kernel i j = kernel j i

/-- The Schur complement obeys the finite Helmholtz condition. -/
theorem reduced_hessian_formally_helmholtz
    (data : FiniteRankParentData ι) :
    FiniteHelmholtz (reducedBoundaryHessian data) := by
  intro i j
  exact reduced_boundary_hessian_symmetric data i j

/-- Linear boundary operator induced by the Schur-reduced Hessian. -/
noncomputable def reducedHessianOperator
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (i : ι) : ℝ :=
  ∑ j, reducedBoundaryHessian data i j * boundary j

/-- Formal self-adjointness in the standard finite Euclidean pairing. -/
def FiniteFormallySelfAdjoint
    (operator : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ left right,
    (∑ i, left i * operator right i) =
      ∑ i, operator left i * right i

omit [Nonempty ι] in
/-- Kernel symmetry gives pairing-level formal self-adjointness. -/
theorem symmetric_kernel_formally_self_adjoint
    (kernel : ι → ι → ℝ)
    (hSymmetric : ∀ i j, kernel i j = kernel j i) :
    FiniteFormallySelfAdjoint
      (fun boundary i => ∑ j, kernel i j * boundary j) := by
  intro left right
  calc
    (∑ i, left i * ∑ j, kernel i j * right j) =
        ∑ i, ∑ j, left i * (kernel i j * right j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, left i * (kernel i j * right j) := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (kernel i j * left j) * right i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hSymmetric j i]
      ring
    _ = ∑ i, (∑ j, kernel i j * left j) * right i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]

theorem reduced_hessian_formally_self_adjoint
    (data : FiniteRankParentData ι) :
    FiniteFormallySelfAdjoint (reducedHessianOperator data) := by
  exact symmetric_kernel_formally_self_adjoint
    (reducedBoundaryHessian data)
    (reduced_boundary_hessian_symmetric data)

/-- The finite Schur-reduced quadratic action. -/
noncomputable def reducedAction
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) : ℝ :=
  boundaryQuadratic data boundary / 2 -
    couplingPairing data boundary ^ 2 /
      (2 * data.bulkCoefficient)

/-- The rank-one coupling quadratic is the square of its pairing. -/
theorem coupling_rank_one_quadratic
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    (∑ i, ∑ j,
      boundary i * (data.coupling i * data.coupling j) * boundary j) =
      couplingPairing data boundary ^ 2 := by
  unfold couplingPairing
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The reduced action is exactly the quadratic form of the Schur Hessian. -/
theorem reduced_action_kernel_formula
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    reducedAction data boundary =
      (∑ i, ∑ j,
        boundary i * reducedBoundaryHessian data i j * boundary j) / 2 := by
  have hExpanded :
      (∑ i, ∑ j,
        boundary i * reducedBoundaryHessian data i j * boundary j) =
        boundaryQuadratic data boundary -
          (∑ i, ∑ j,
            (boundary i * (data.coupling i * data.coupling j) * boundary j) /
              data.bulkCoefficient) := by
    unfold boundaryQuadratic reducedBoundaryHessian
    calc
      (∑ i, ∑ j,
        boundary i *
          (data.boundaryHessian i j -
            data.coupling i * data.coupling j / data.bulkCoefficient) *
          boundary j) =
          ∑ i, ∑ j,
            ((boundary i * data.boundaryHessian i j * boundary j) -
              (boundary i * (data.coupling i * data.coupling j) * boundary j) /
                data.bulkCoefficient) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i,
          ((∑ j, boundary i * data.boundaryHessian i j * boundary j) -
            ∑ j,
              (boundary i * (data.coupling i * data.coupling j) * boundary j) /
                data.bulkCoefficient) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_sub_distrib]
      _ =
          (∑ i, ∑ j,
            boundary i * data.boundaryHessian i j * boundary j) -
          ∑ i, ∑ j,
            (boundary i * (data.coupling i * data.coupling j) * boundary j) /
              data.bulkCoefficient := by
        rw [Finset.sum_sub_distrib]
  have hDivide :
      (∑ i, ∑ j,
        (boundary i * (data.coupling i * data.coupling j) * boundary j) /
          data.bulkCoefficient) =
        (∑ i, ∑ j,
          boundary i * (data.coupling i * data.coupling j) * boundary j) /
            data.bulkCoefficient := by
    calc
      (∑ i, ∑ j,
        (boundary i * (data.coupling i * data.coupling j) * boundary j) /
          data.bulkCoefficient) =
          ∑ i,
            (∑ j,
              boundary i * (data.coupling i * data.coupling j) * boundary j) /
                data.bulkCoefficient := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_div Finset.univ
          (fun j =>
            boundary i * (data.coupling i * data.coupling j) * boundary j)
          data.bulkCoefficient).symm
      _ =
          (∑ i, ∑ j,
            boundary i * (data.coupling i * data.coupling j) * boundary j) /
              data.bulkCoefficient := by
        exact (Finset.sum_div Finset.univ
          (fun i => ∑ j,
            boundary i * (data.coupling i * data.coupling j) * boundary j)
          data.bulkCoefficient).symm
  rw [hExpanded, hDivide, coupling_rank_one_quadratic]
  unfold reducedAction
  field_simp [data.bulkCoefficientNonzero]

/-- Exact on-shell Schur-complement formula. -/
theorem parent_action_on_shell
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    parentAction data (stationaryBulk data boundary) boundary =
      reducedAction data boundary := by
  unfold parentAction stationaryBulk reducedAction
  field_simp [data.bulkCoefficientNonzero]
  ring

/--
Finite-rank synthesis: the bulk stationary point is unique, its on-shell
action is the Schur reduction, and the reduced Hessian is Helmholtz/self-adjoint.
-/
theorem finite_rank_parent_schur_helmholtz_synthesis
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    (∃! bulk : ℝ, bulkEulerDerivative data bulk boundary = 0) ∧
    parentAction data (stationaryBulk data boundary) boundary =
      reducedAction data boundary ∧
    FiniteHelmholtz (reducedBoundaryHessian data) ∧
    FiniteFormallySelfAdjoint (reducedHessianOperator data) := by
  exact ⟨stationary_bulk_exists_unique data boundary,
    parent_action_on_shell data boundary,
    reduced_hessian_formally_helmholtz data,
    reduced_hessian_formally_self_adjoint data⟩

end P0EFTJanusFiniteRankParentSchurHelmholtz
end JanusFormal
