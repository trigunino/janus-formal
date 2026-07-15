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

/-- The displayed bulk Euler expression is the actual derivative of the
finite parent action at fixed boundary data. -/
theorem parent_action_hasDerivAt_bulk
    (data : FiniteRankParentData ι)
    (bulk : ℝ)
    (boundary : ι → ℝ) :
    HasDerivAt
      (fun variedBulk => parentAction data variedBulk boundary)
      (bulkEulerDerivative data bulk boundary)
      bulk := by
  unfold parentAction bulkEulerDerivative
  have hSquare := (hasDerivAt_id bulk).pow 2
  have hBulkTerm :=
    (hSquare.const_mul data.bulkCoefficient).div_const 2
  have hCouplingTerm :=
    (hasDerivAt_id bulk).mul_const (couplingPairing data boundary)
  have hDerivativeEq :
      data.bulkCoefficient * (↑2 * id bulk ^ (2 - 1) * 1) / 2 +
          1 * couplingPairing data boundary =
        data.bulkCoefficient * bulk + couplingPairing data boundary := by
    simp [id]
    ring
  have hCore :=
    (hBulkTerm.add hCouplingTerm).congr_deriv hDerivativeEq
  simpa [id, pow_two] using
    hCore.add_const (boundaryQuadratic data boundary / 2)

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

/-- The eliminated bulk coefficient is genuinely stationary for the parent
action, not merely a root of a separately declared expression. -/
theorem stationary_bulk_hasDerivAt_zero
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    HasDerivAt
      (fun bulk => parentAction data bulk boundary)
      0
      (stationaryBulk data boundary) := by
  exact (parent_action_hasDerivAt_bulk data
    (stationaryBulk data boundary) boundary).congr_deriv
      (stationary_bulk_solves_euler data boundary)

/-- The genuine stationary point of the finite parent action is unique. -/
theorem stationary_bulk_actual_unique
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (bulk : ℝ)
    (hStationary :
      HasDerivAt (fun variedBulk => parentAction data variedBulk boundary)
        0 bulk) :
    bulk = stationaryBulk data boundary := by
  apply stationary_bulk_unique data boundary bulk
  exact (parent_action_hasDerivAt_bulk data bulk boundary).unique hStationary

/-- Existence and uniqueness stated directly in terms of the derivative of
the finite parent action. -/
theorem stationary_bulk_actual_exists_unique
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    ∃! bulk : ℝ,
      HasDerivAt (fun variedBulk => parentAction data variedBulk boundary)
        0 bulk := by
  refine ⟨stationaryBulk data boundary,
    stationary_bulk_hasDerivAt_zero data boundary, ?_⟩
  intro bulk hBulk
  exact stationary_bulk_actual_unique data boundary bulk hBulk

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

/-- Continuous evaluation at one coordinate of the finite boundary space. -/
noncomputable def boundaryCoordinate
    (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.proj i)

omit [Nonempty ι] in
@[simp]
theorem boundaryCoordinate_apply
    (i : ι) (boundary : ι → ℝ) :
    boundaryCoordinate i boundary = boundary i := rfl

/-- Continuous linear functional represented by the Schur-reduced gradient
in the standard finite coordinate pairing. -/
noncomputable def reducedGradientFunctional
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
  (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (reducedHessianOperator data boundary i) •
    boundaryCoordinate i

@[simp]
theorem reducedGradientFunctional_apply
    (data : FiniteRankParentData ι)
    (boundary variation : ι → ℝ) :
    reducedGradientFunctional data boundary variation =
      ∑ i, reducedHessianOperator data boundary i * variation i := by
  simp [reducedGradientFunctional, smul_eq_mul]

/-- Linearity of the finite Schur gradient as a dual-valued map. -/
noncomputable def reducedGradientLinearMap
    (data : FiniteRankParentData ι) :
    (ι → ℝ) →ₗ[ℝ] ((ι → ℝ) →L[ℝ] ℝ) where
  toFun := reducedGradientFunctional data
  map_add' left right := by
    ext variation
    simp [reducedGradientFunctional_apply, reducedHessianOperator,
      Finset.sum_add_distrib, mul_add, add_mul]
  map_smul' scalar boundary := by
    ext variation
    simp [reducedGradientFunctional_apply, reducedHessianOperator,
      Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- The second derivative as a continuous linear map into the finite dual. -/
noncomputable def reducedGradientDerivative
    (data : FiniteRankParentData ι) :
    (ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap (reducedGradientLinearMap data)

@[simp]
theorem reducedGradientDerivative_apply
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    reducedGradientDerivative data boundary =
      reducedGradientFunctional data boundary := rfl

@[simp]
theorem reducedGradientDerivative_apply_apply
    (data : FiniteRankParentData ι)
    (boundary variation : ι → ℝ) :
    reducedGradientDerivative data boundary variation =
      ∑ i, reducedHessianOperator data boundary i * variation i := by
  rw [reducedGradientDerivative_apply,
    reducedGradientFunctional_apply]

/-- The Schur kernel as an actual continuous linear operator on the finite
boundary coefficient space. -/
noncomputable def reducedHessianContinuousLinearMap
    (data : FiniteRankParentData ι) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, (reducedBoundaryHessian data i j) •
      boundaryCoordinate j

@[simp]
theorem reducedHessianContinuousLinearMap_apply
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    reducedHessianContinuousLinearMap data boundary =
      reducedHessianOperator data boundary := by
  funext i
  simp [reducedHessianContinuousLinearMap, reducedHessianOperator,
    smul_eq_mul]

/-- Unsimplified product-rule derivative of the symmetric reduced quadratic
form. -/
noncomputable def reducedActionDerivativeExpansion
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ •
    ∑ i, ∑ j,
      ((boundary i * reducedBoundaryHessian data i j) •
          boundaryCoordinate j +
        boundary j •
          ((reducedBoundaryHessian data i j) •
            boundaryCoordinate i))

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

/-- Product-rule Fréchet derivative of the finite Schur quadratic, before
using symmetry to combine its two equal contributions. -/
theorem reduced_action_hasFDerivAt_expansion
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    HasFDerivAt
      (reducedAction data)
      (reducedActionDerivativeExpansion data boundary)
      boundary := by
  have hTerm (i j : ι) :
      HasFDerivAt
        ((fun variedBoundary : ι → ℝ =>
            variedBoundary i * reducedBoundaryHessian data i j) *
          fun variedBoundary : ι → ℝ => variedBoundary j)
        ((boundary i * reducedBoundaryHessian data i j) •
            boundaryCoordinate j +
          boundary j • reducedBoundaryHessian data i j •
            boundaryCoordinate i)
        boundary := by
    have hi : HasFDerivAt
        (boundaryCoordinate i) (boundaryCoordinate i) boundary :=
      (boundaryCoordinate i).hasFDerivAt
    have hj : HasFDerivAt
        (boundaryCoordinate j) (boundaryCoordinate j) boundary :=
      (boundaryCoordinate j).hasFDerivAt
    exact (hi.mul_const (reducedBoundaryHessian data i j)).mul hj
  have hDoubleSum :=
    HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        hTerm i j
  have hScaled := hDoubleSum.mul_const (2 : ℝ)⁻¹
  have hFormula :
      reducedAction data = fun variedBoundary =>
        (∑ i, ∑ j,
          variedBoundary i * reducedBoundaryHessian data i j *
            variedBoundary j) / 2 := by
    funext variedBoundary
    exact reduced_action_kernel_formula data variedBoundary
  rw [hFormula]
  simpa [reducedActionDerivativeExpansion, div_eq_mul_inv] using hScaled

/-- Symmetry combines the two product-rule contributions into the Schur
gradient functional. -/
theorem reducedActionDerivativeExpansion_eq_gradient
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    reducedActionDerivativeExpansion data boundary =
      reducedGradientFunctional data boundary := by
  ext variation
  simp [reducedActionDerivativeExpansion, reducedGradientFunctional,
    reducedHessianOperator, smul_eq_mul]
  have hDistribute :
      (∑ i, ∑ j,
        (boundary i * reducedBoundaryHessian data i j * variation j +
          boundary j * (reducedBoundaryHessian data i j * variation i))) =
        (∑ i, ∑ j,
          boundary i * reducedBoundaryHessian data i j * variation j) +
        ∑ i, ∑ j,
          boundary j * (reducedBoundaryHessian data i j * variation i) := by
    calc
      _ = ∑ i,
          ((∑ j,
            boundary i * reducedBoundaryHessian data i j * variation j) +
          ∑ j,
            boundary j * (reducedBoundaryHessian data i j * variation i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_add_distrib
      _ = _ := Finset.sum_add_distrib
  have hSwap :
      (∑ i, ∑ j,
        boundary i * reducedBoundaryHessian data i j * variation j) =
      ∑ i, ∑ j,
        boundary j * (reducedBoundaryHessian data i j * variation i) := by
    calc
      _ = ∑ j, ∑ i,
          boundary i * reducedBoundaryHessian data i j * variation j := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [reduced_boundary_hessian_symmetric data j i]
        ring
  have hGradient :
      (∑ i, ∑ j,
        boundary j * (reducedBoundaryHessian data i j * variation i)) =
      ∑ i,
        (∑ j, reducedBoundaryHessian data i j * boundary j) * variation i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hDistribute, hSwap, hGradient]
  ring

/-- The Fréchet derivative of the reduced action is represented exactly by
the Schur-reduced Hessian operator in the finite coordinate pairing. -/
theorem reduced_action_hasFDerivAt
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    HasFDerivAt
      (reducedAction data)
      (reducedGradientFunctional data boundary)
      boundary := by
  exact (reduced_action_hasFDerivAt_expansion data boundary).congr_fderiv
    (reducedActionDerivativeExpansion_eq_gradient data boundary)

/-- Computed Fréchet derivative of the finite reduced action. -/
theorem reduced_action_fderiv
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    fderiv ℝ (reducedAction data) boundary =
      reducedGradientFunctional data boundary :=
  (reduced_action_hasFDerivAt data boundary).fderiv

/-- The reduced gradient is linear, so its Fréchet derivative is the constant
dual-valued Schur Hessian. -/
theorem reduced_gradient_hasFDerivAt
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    HasFDerivAt
      (reducedGradientFunctional data)
      (reducedGradientDerivative data)
      boundary := by
  have hFunction :
      (reducedGradientDerivative data :
        (ι → ℝ) → ((ι → ℝ) →L[ℝ] ℝ)) =
        reducedGradientFunctional data := by
    funext variedBoundary
    exact reducedGradientDerivative_apply data variedBoundary
  rw [← hFunction]
  exact (reducedGradientDerivative data).hasFDerivAt

/-- The actual second Fréchet derivative of the reduced action is the
dual-valued Schur Hessian. -/
theorem reduced_action_fderiv_hasFDerivAt
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    HasFDerivAt
      (fun variedBoundary =>
        fderiv ℝ (reducedAction data) variedBoundary)
      (reducedGradientDerivative data)
      boundary := by
  have hFunction :
      (fun variedBoundary =>
        fderiv ℝ (reducedAction data) variedBoundary) =
        reducedGradientFunctional data := by
    funext variedBoundary
    exact reduced_action_fderiv data variedBoundary
  rw [hFunction]
  exact reduced_gradient_hasFDerivAt data boundary

/-- Computed second Fréchet derivative of the finite reduced action. -/
theorem reduced_action_second_fderiv
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    fderiv ℝ
      (fun variedBoundary =>
        fderiv ℝ (reducedAction data) variedBoundary)
      boundary = reducedGradientDerivative data :=
  (reduced_action_fderiv_hasFDerivAt data boundary).fderiv

/-- The linear Schur gradient operator has the Schur kernel itself as its
Fréchet derivative at every finite boundary coefficient vector. -/
theorem reduced_hessian_operator_hasFDerivAt
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    HasFDerivAt
      (reducedHessianOperator data)
      (reducedHessianContinuousLinearMap data)
      boundary := by
  have hFunction :
      (reducedHessianContinuousLinearMap data :
        (ι → ℝ) → (ι → ℝ)) =
        reducedHessianOperator data := by
    funext variedBoundary
    exact reducedHessianContinuousLinearMap_apply data variedBoundary
  rw [← hFunction]
  exact (reducedHessianContinuousLinearMap data).hasFDerivAt

/-- Computed Fréchet derivative of the finite Schur gradient operator. -/
theorem reduced_hessian_operator_fderiv
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    fderiv ℝ (reducedHessianOperator data) boundary =
      reducedHessianContinuousLinearMap data :=
  (reduced_hessian_operator_hasFDerivAt data boundary).fderiv

/-- Exact on-shell Schur-complement formula. -/
theorem parent_action_on_shell
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    parentAction data (stationaryBulk data boundary) boundary =
      reducedAction data boundary := by
  unfold parentAction stationaryBulk reducedAction
  field_simp [data.bulkCoefficientNonzero]
  ring

/-- Exact square completion of the parent action at fixed boundary data. -/
theorem parent_action_sub_reduced_action_eq_square
    (data : FiniteRankParentData ι)
    (bulk : ℝ)
    (boundary : ι → ℝ) :
    parentAction data bulk boundary - reducedAction data boundary =
      data.bulkCoefficient / 2 *
        (bulk - stationaryBulk data boundary) ^ 2 := by
  unfold parentAction reducedAction stationaryBulk
  field_simp [data.bulkCoefficientNonzero]
  ring

/-- Square completion relative to the stationary parent-action value. -/
theorem parent_action_sub_stationary_action_eq_square
    (data : FiniteRankParentData ι)
    (bulk : ℝ)
    (boundary : ι → ℝ) :
    parentAction data bulk boundary -
        parentAction data (stationaryBulk data boundary) boundary =
      data.bulkCoefficient / 2 *
        (bulk - stationaryBulk data boundary) ^ 2 := by
  rw [parent_action_on_shell data boundary]
  exact parent_action_sub_reduced_action_eq_square data bulk boundary

/-- A positive bulk coefficient makes the stationary bulk value a global
minimum at every fixed boundary value. -/
theorem stationary_bulk_global_minimum
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (_hPositive : 0 < data.bulkCoefficient)
    (bulk : ℝ) :
    parentAction data (stationaryBulk data boundary) boundary ≤
      parentAction data bulk boundary := by
  have hSquare : 0 ≤ (bulk - stationaryBulk data boundary) ^ 2 :=
    sq_nonneg _
  have hCompletion :=
    parent_action_sub_stationary_action_eq_square data bulk boundary
  nlinarith

/-- Equality in the positive-coefficient minimum bound occurs only at the
stationary bulk value. -/
theorem stationary_bulk_global_minimum_eq_iff
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (_hPositive : 0 < data.bulkCoefficient)
    (bulk : ℝ) :
    parentAction data bulk boundary =
        parentAction data (stationaryBulk data boundary) boundary ↔
      bulk = stationaryBulk data boundary := by
  constructor
  · intro hEqual
    have hCompletion :=
      parent_action_sub_stationary_action_eq_square data bulk boundary
    have hProduct :
        data.bulkCoefficient / 2 *
            (bulk - stationaryBulk data boundary) ^ 2 = 0 := by
      rw [← hCompletion]
      exact sub_eq_zero.mpr hEqual
    have hCoefficient : data.bulkCoefficient / 2 ≠ 0 :=
      div_ne_zero data.bulkCoefficientNonzero (by norm_num)
    have hSquare : (bulk - stationaryBulk data boundary) ^ 2 = 0 :=
      (mul_eq_zero.mp hProduct).resolve_left hCoefficient
    nlinarith
  · intro hBulk
    rw [hBulk]

/-- For a positive bulk coefficient, the stationary bulk value is the
unique global minimizer with the boundary data held fixed. -/
theorem stationary_bulk_unique_global_minimizer
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (hPositive : 0 < data.bulkCoefficient) :
    ∃! minimizingBulk : ℝ, ∀ bulk : ℝ,
      parentAction data minimizingBulk boundary ≤
        parentAction data bulk boundary := by
  refine ⟨stationaryBulk data boundary,
    stationary_bulk_global_minimum data boundary hPositive, ?_⟩
  intro minimizingBulk hMinimum
  have hForward := hMinimum (stationaryBulk data boundary)
  have hBackward :=
    stationary_bulk_global_minimum data boundary hPositive minimizingBulk
  exact (stationary_bulk_global_minimum_eq_iff
    data boundary hPositive minimizingBulk).1
      (le_antisymm hForward hBackward)

/-- A negative bulk coefficient makes the stationary bulk value a global
maximum at every fixed boundary value. -/
theorem stationary_bulk_global_maximum
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (_hNegative : data.bulkCoefficient < 0)
    (bulk : ℝ) :
    parentAction data bulk boundary ≤
      parentAction data (stationaryBulk data boundary) boundary := by
  have hSquare : 0 ≤ (bulk - stationaryBulk data boundary) ^ 2 :=
    sq_nonneg _
  have hCompletion :=
    parent_action_sub_stationary_action_eq_square data bulk boundary
  nlinarith

/-- Equality in the negative-coefficient maximum bound occurs only at the
stationary bulk value. -/
theorem stationary_bulk_global_maximum_eq_iff
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (_hNegative : data.bulkCoefficient < 0)
    (bulk : ℝ) :
    parentAction data bulk boundary =
        parentAction data (stationaryBulk data boundary) boundary ↔
      bulk = stationaryBulk data boundary := by
  constructor
  · intro hEqual
    have hCompletion :=
      parent_action_sub_stationary_action_eq_square data bulk boundary
    have hProduct :
        data.bulkCoefficient / 2 *
            (bulk - stationaryBulk data boundary) ^ 2 = 0 := by
      rw [← hCompletion]
      exact sub_eq_zero.mpr hEqual
    have hCoefficient : data.bulkCoefficient / 2 ≠ 0 :=
      div_ne_zero data.bulkCoefficientNonzero (by norm_num)
    have hSquare : (bulk - stationaryBulk data boundary) ^ 2 = 0 :=
      (mul_eq_zero.mp hProduct).resolve_left hCoefficient
    nlinarith
  · intro hBulk
    rw [hBulk]

/-- For a negative bulk coefficient, the stationary bulk value is the
unique global maximizer with the boundary data held fixed. -/
theorem stationary_bulk_unique_global_maximizer
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ)
    (hNegative : data.bulkCoefficient < 0) :
    ∃! maximizingBulk : ℝ, ∀ bulk : ℝ,
      parentAction data bulk boundary ≤
        parentAction data maximizingBulk boundary := by
  refine ⟨stationaryBulk data boundary,
    stationary_bulk_global_maximum data boundary hNegative, ?_⟩
  intro maximizingBulk hMaximum
  have hForward :=
    stationary_bulk_global_maximum data boundary hNegative maximizingBulk
  have hBackward := hMaximum (stationaryBulk data boundary)
  exact (stationary_bulk_global_maximum_eq_iff
    data boundary hNegative maximizingBulk).1
      (le_antisymm hForward hBackward)

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

/-- Strengthened finite-dimensional synthesis stated entirely with actual
Fréchet derivatives of the parent and reduced actions. -/
theorem finite_rank_parent_actual_variational_synthesis
    (data : FiniteRankParentData ι)
    (boundary : ι → ℝ) :
    (∃! bulk : ℝ,
      HasDerivAt (fun variedBulk => parentAction data variedBulk boundary)
        0 bulk) ∧
    HasFDerivAt (reducedAction data)
      (reducedGradientFunctional data boundary) boundary ∧
    HasFDerivAt
      (fun variedBoundary =>
        fderiv ℝ (reducedAction data) variedBoundary)
      (reducedGradientDerivative data) boundary ∧
    parentAction data (stationaryBulk data boundary) boundary =
      reducedAction data boundary ∧
    FiniteHelmholtz (reducedBoundaryHessian data) ∧
    FiniteFormallySelfAdjoint (reducedHessianOperator data) := by
  exact ⟨stationary_bulk_actual_exists_unique data boundary,
    reduced_action_hasFDerivAt data boundary,
    reduced_action_fderiv_hasFDerivAt data boundary,
    parent_action_on_shell data boundary,
    reduced_hessian_formally_helmholtz data,
    reduced_hessian_formally_self_adjoint data⟩

end P0EFTJanusFiniteRankParentSchurHelmholtz
end JanusFormal
