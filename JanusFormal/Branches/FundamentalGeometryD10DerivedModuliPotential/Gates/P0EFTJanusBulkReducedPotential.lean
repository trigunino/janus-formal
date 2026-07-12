import Mathlib

namespace JanusFormal
namespace P0EFTJanusBulkReducedPotential

set_option autoImplicit false

/--
Finite-dimensional proxy for a quadratic bulk field coupled to one throat
field. `bulkCoefficient` is assumed nonzero so the bulk Euler equation can be
solved at fixed boundary data.
-/
structure QuadraticBulkBoundaryData where
  bulkCoefficient : ℝ
  coupling : ℝ
  boundaryCoefficient : ℝ
  bulkCoefficientNonzero : bulkCoefficient ≠ 0

/-- Coupled quadratic action. -/
noncomputable def coupledAction
    (s : QuadraticBulkBoundaryData)
    (bulk boundary : ℝ) : ℝ :=
  s.bulkCoefficient * bulk ^ 2 / 2 +
    s.coupling * bulk * boundary +
    s.boundaryCoefficient * boundary ^ 2 / 2

/-- Bulk Euler derivative at fixed boundary field. -/
def bulkEulerDerivative
    (s : QuadraticBulkBoundaryData)
    (bulk boundary : ℝ) : ℝ :=
  s.bulkCoefficient * bulk + s.coupling * boundary

/-- Unique stationary bulk field for prescribed boundary data. -/
noncomputable def stationaryBulkField
    (s : QuadraticBulkBoundaryData)
    (boundary : ℝ) : ℝ :=
  -s.coupling * boundary / s.bulkCoefficient

/-- The stationary bulk field solves the bulk equation. -/
theorem stationary_bulk_solves_euler_equation
    (s : QuadraticBulkBoundaryData)
    (boundary : ℝ) :
    bulkEulerDerivative s
        (stationaryBulkField s boundary) boundary = 0 := by
  unfold bulkEulerDerivative stationaryBulkField
  field_simp [s.bulkCoefficientNonzero]
  ring

/-- The bulk stationary solution is unique. -/
theorem stationary_bulk_unique
    (s : QuadraticBulkBoundaryData)
    (bulk boundary : ℝ)
    (hStationary : bulkEulerDerivative s bulk boundary = 0) :
    bulk = stationaryBulkField s boundary := by
  unfold bulkEulerDerivative at hStationary
  unfold stationaryBulkField
  apply (eq_div_iff s.bulkCoefficientNonzero).2
  nlinarith [hStationary]

/-- On-shell boundary effective action. -/
noncomputable def reducedBoundaryAction
    (s : QuadraticBulkBoundaryData)
    (boundary : ℝ) : ℝ :=
  coupledAction s (stationaryBulkField s boundary) boundary

/-- Schur-complement coefficient of the reduced action. -/
noncomputable def reducedBoundaryHessian
    (s : QuadraticBulkBoundaryData) : ℝ :=
  s.boundaryCoefficient -
    s.coupling ^ 2 / s.bulkCoefficient

/-- Exact Schur-complement formula. -/
theorem reduced_boundary_action_formula
    (s : QuadraticBulkBoundaryData)
    (boundary : ℝ) :
    reducedBoundaryAction s boundary =
      reducedBoundaryHessian s * boundary ^ 2 / 2 := by
  unfold reducedBoundaryAction coupledAction
    stationaryBulkField reducedBoundaryHessian
  field_simp [s.bulkCoefficientNonzero]
  ring

/-- Boundary Euler derivative of the reduced potential. -/
noncomputable def reducedBoundaryEulerDerivative
    (s : QuadraticBulkBoundaryData)
    (boundary : ℝ) : ℝ :=
  reducedBoundaryHessian s * boundary

/-- Positive Schur complement gives a stable quadratic boundary mode. -/
theorem positive_reduced_hessian_gives_positive_action
    (s : QuadraticBulkBoundaryData)
    (hPositive : 0 < reducedBoundaryHessian s)
    (boundary : ℝ)
    (hBoundary : boundary ≠ 0) :
    0 < reducedBoundaryAction s boundary := by
  rw [reduced_boundary_action_formula]
  exact div_pos
    (mul_pos hPositive (sq_pos_of_ne_zero hBoundary))
    (by norm_num)

/-- Vanishing Schur complement leaves an exact flat boundary direction. -/
theorem zero_reduced_hessian_gives_flat_direction
    (s : QuadraticBulkBoundaryData)
    (hZero : reducedBoundaryHessian s = 0)
    (boundary : ℝ) :
    reducedBoundaryAction s boundary = 0 := by
  rw [reduced_boundary_action_formula, hZero]
  ring

/-- Same boundary field space but different bulk couplings can produce different boundary Hessians. -/
theorem boundary_moduli_alone_do_not_fix_reduced_hessian :
    ∃ first second : QuadraticBulkBoundaryData,
      first.boundaryCoefficient = second.boundaryCoefficient /\
      reducedBoundaryHessian first ≠
        reducedBoundaryHessian second := by
  refine ⟨
    { bulkCoefficient := 1
      coupling := 0
      boundaryCoefficient := 2
      bulkCoefficientNonzero := by norm_num },
    { bulkCoefficient := 1
      coupling := 1
      boundaryCoefficient := 2
      bulkCoefficientNonzero := by norm_num },
    rfl, ?_⟩
  norm_num [reducedBoundaryHessian]

/-- Rescaling the whole bulk-plus-boundary action rescales the effective Hessian. -/
def rescaleQuadraticData
    (scale : ℝ)
    (s : QuadraticBulkBoundaryData)
    (hScale : scale ≠ 0) : QuadraticBulkBoundaryData where
  bulkCoefficient := scale * s.bulkCoefficient
  coupling := scale * s.coupling
  boundaryCoefficient := scale * s.boundaryCoefficient
  bulkCoefficientNonzero :=
    mul_ne_zero hScale s.bulkCoefficientNonzero

/-- Schur complement scales with the action normalization. -/
theorem reduced_hessian_rescaling
    (scale : ℝ)
    (s : QuadraticBulkBoundaryData)
    (hScale : scale ≠ 0) :
    reducedBoundaryHessian
        (rescaleQuadraticData scale s hScale) =
      scale * reducedBoundaryHessian s := by
  unfold reducedBoundaryHessian rescaleQuadraticData
  field_simp [hScale, s.bulkCoefficientNonzero] <;> ring

/--
The most natural throat potential is therefore **relative**, not intrinsic:
choose a bulk action and admissible boundary/junction data, solve the bulk Euler
problem, and evaluate the action on shell. Its Hessian is the Schur complement
(or, for PDEs, a Dirichlet-to-Neumann/Calderon boundary operator plus local
brane terms). This produces the nonlocal information absent from local
Seeley--DeWitt coefficients, but it remains canonical only relative to the
chosen bulk action, normalization and boundary conditions.
-/
structure BulkReducedPotentialPhysicalStatus where
  bulkConfigurationSpaceConstructed : Prop
  bulkGaugeGroupConstructed : Prop
  bulkActionDerived : Prop
  boundaryAndJunctionTermsDerived : Prop
  wellPosedBoundaryValueProblemProved : Prop
  classicalBulkSolutionForBoundaryDataConstructed : Prop
  onShellBoundaryFunctionalDefined : Prop
  dirichletToNeumannOperatorDerived : Prop
  localCountertermsFixedMicroscopically : Prop
  reducedHessianEllipticAndSelfAdjoint : Prop
  throatCriticalPointDerived : Prop


def bulkReducedPotentialPhysicalClosure
    (s : BulkReducedPotentialPhysicalStatus) : Prop :=
  s.bulkConfigurationSpaceConstructed /\
  s.bulkGaugeGroupConstructed /\
  s.bulkActionDerived /\
  s.boundaryAndJunctionTermsDerived /\
  s.wellPosedBoundaryValueProblemProved /\
  s.classicalBulkSolutionForBoundaryDataConstructed /\
  s.onShellBoundaryFunctionalDefined /\
  s.dirichletToNeumannOperatorDerived /\
  s.localCountertermsFixedMicroscopically /\
  s.reducedHessianEllipticAndSelfAdjoint /\
  s.throatCriticalPointDerived

end P0EFTJanusBulkReducedPotential
end JanusFormal
