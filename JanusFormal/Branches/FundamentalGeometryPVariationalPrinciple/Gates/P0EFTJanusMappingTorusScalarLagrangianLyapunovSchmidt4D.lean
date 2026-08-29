import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianCoerciveVariationalProblem4D

/-!
# Lyapunov--Schmidt reduction for scalar Lagrangian bifurcation

Near a degenerate scalar critical point, the operator domain and target split
into kernel/complement and cokernel/range coordinates.  Solving the range
equation uniquely as a function of the kernel coordinate leaves a
finite-dimensional reduced Euler map.

This file formalizes that logical reduction without hiding the analytic input.
The complement solver, its range equation and uniqueness are explicit fields.
The resulting theorems identify full nonlinear zeros, reduced zeros and lifted
solution branches exactly.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianLyapunovSchmidt4D

set_option autoImplicit false
noncomputable section

universe u₁ u₂ v₁ v₂

variable {Kernel : Type u₁} {Complement : Type u₂}
  {Cokernel : Type v₁} {Range : Type v₂}
  [AddCommGroup Kernel] [Module Real Kernel]
  [AddCommGroup Complement] [Module Real Complement]
  [AddCommGroup Cokernel] [Module Real Cokernel]
  [AddCommGroup Range] [Module Real Range]

/-- Nonlinear Euler map written in Lyapunov--Schmidt coordinates. -/
structure CanonicalScalarLyapunovSchmidtProblem where
  euler : Kernel × Complement → Cokernel × Range
  complementSolver : Kernel → Complement
  rangeEquation : ∀ kernel : Kernel,
    (euler (kernel, complementSolver kernel)).2 = 0
  rangeUnique : ∀ (kernel : Kernel) (complement : Complement),
    (euler (kernel, complement)).2 = 0 →
      complement = complementSolver kernel

namespace CanonicalScalarLyapunovSchmidtProblem

/-- Reduced finite-dimensional Euler map on the kernel coordinate. -/
def reducedEuler
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range)) :
    Kernel → Cokernel :=
  fun kernel => (problem.euler (kernel, problem.complementSolver kernel)).1

/-- Lift of a kernel coordinate to the full domain. -/
def lift
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range)) :
    Kernel → Kernel × Complement :=
  fun kernel => (kernel, problem.complementSolver kernel)

@[simp] theorem lift_fst
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel) :
    (problem.lift kernel).1 = kernel :=
  rfl

@[simp] theorem lift_snd
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel) :
    (problem.lift kernel).2 = problem.complementSolver kernel :=
  rfl

/-- Euler map on the lifted graph has vanishing range component. -/
theorem euler_lift_range_zero
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel) :
    (problem.euler (problem.lift kernel)).2 = 0 :=
  problem.rangeEquation kernel

/-- Euler map on the lifted graph is exactly `(reducedEuler,0)`. -/
theorem euler_lift
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel) :
    problem.euler (problem.lift kernel) =
      (problem.reducedEuler kernel, 0) := by
  apply Prod.ext
  · rfl
  · exact problem.rangeEquation kernel

/-- Every full zero lies on the complement-solver graph. -/
theorem complement_eq_solver_of_euler_eq_zero
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel) (complement : Complement)
    (hEuler : problem.euler (kernel, complement) = 0) :
    complement = problem.complementSolver kernel := by
  apply problem.rangeUnique kernel complement
  exact congrArg Prod.snd hEuler

/-- Full nonlinear zeros are exactly lifted reduced zeros. -/
theorem euler_eq_zero_iff
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel) (complement : Complement) :
    problem.euler (kernel, complement) = 0 ↔
      complement = problem.complementSolver kernel ∧
        problem.reducedEuler kernel = 0 := by
  constructor
  · intro hEuler
    have hComplement := problem.complement_eq_solver_of_euler_eq_zero
      kernel complement hEuler
    constructor
    · exact hComplement
    · have hFirst := congrArg Prod.fst hEuler
      simpa [reducedEuler, hComplement] using hFirst
  · rintro ⟨rfl, hReduced⟩
    change problem.euler (problem.lift kernel) = 0
    rw [problem.euler_lift]
    simp [hReduced]

/-- Reduced zero if and only if its canonical lift is a full nonlinear zero. -/
theorem reducedEuler_eq_zero_iff_lift
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel) :
    problem.reducedEuler kernel = 0 ↔
      problem.euler (problem.lift kernel) = 0 := by
  rw [problem.euler_lift]
  simp

/-- Full solution set as the graph of the complement solver over the reduced
zero set. -/
theorem fullSolutionSet_eq
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range)) :
    {field : Kernel × Complement | problem.euler field = 0} =
      problem.lift '' {kernel : Kernel | problem.reducedEuler kernel = 0} := by
  ext field
  constructor
  · intro hField
    have hCharacterization := (problem.euler_eq_zero_iff field.1 field.2).1 hField
    refine ⟨field.1, hCharacterization.2, ?_⟩
    apply Prod.ext
    · rfl
    · exact hCharacterization.1.symm
  · rintro ⟨kernel, hKernel, rfl⟩
    exact (problem.reducedEuler_eq_zero_iff_lift kernel).1 hKernel

/-- A parameterized reduced branch lifts to a full branch. -/
theorem lift_reduced_solution_curve
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    {Parameter : Type*}
    (kernelCurve : Parameter → Kernel)
    (hCurve : ∀ parameter,
      problem.reducedEuler (kernelCurve parameter) = 0) :
    ∀ parameter,
      problem.euler (problem.lift (kernelCurve parameter)) = 0 := by
  intro parameter
  exact (problem.reducedEuler_eq_zero_iff_lift _).1 (hCurve parameter)

/-- Uniqueness of a full branch over a prescribed kernel coordinate. -/
theorem full_solution_unique_over_kernel
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernel : Kernel)
    (first second : Complement)
    (hFirst : problem.euler (kernel, first) = 0)
    (hSecond : problem.euler (kernel, second) = 0) :
    first = second := by
  rw [problem.complement_eq_solver_of_euler_eq_zero kernel first hFirst,
    problem.complement_eq_solver_of_euler_eq_zero kernel second hSecond]

/-- Optional finite-dimensionality package for the reduced problem. -/
structure FiniteReductionData
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range)) where
  kernelFinite : FiniteDimensional Real Kernel
  cokernelFinite : FiniteDimensional Real Cokernel

/-- Logical closure certificate of the Lyapunov--Schmidt reduction. -/
theorem canonicalScalarLyapunovSchmidt_certificate
    (problem : CanonicalScalarLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range)) :
    (∀ kernel complement,
      problem.euler (kernel, complement) = 0 ↔
        complement = problem.complementSolver kernel ∧
          problem.reducedEuler kernel = 0) ∧
      {field : Kernel × Complement | problem.euler field = 0} =
        problem.lift '' {kernel : Kernel | problem.reducedEuler kernel = 0} :=
  ⟨problem.euler_eq_zero_iff,
    problem.fullSolutionSet_eq⟩

end CanonicalScalarLyapunovSchmidtProblem

end
end P0EFTJanusMappingTorusScalarLagrangianLyapunovSchmidt4D
end JanusFormal
