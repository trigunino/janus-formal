import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianLyapunovSchmidt4D

/-!
# Parameterized Lyapunov--Schmidt reduction and pitchfork normal form

This file adds an external real parameter to the nonlinear reduction.  The
range equation is solved uniquely for each parameter and kernel coordinate,
leaving a reduced Euler map.

For a one-dimensional reduced problem with exact normal form

`r(mu,a) = a * (mu + c a^2)`,

all zeros are classified.  The trivial branch `a=0` is always present; the two
nontrivial branches occur when `-mu/c` is positive and are given by
`a = ± sqrt(-mu/c)`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianPitchforkBifurcation4D

set_option autoImplicit false
noncomputable section

universe u₁ u₂ v₁ v₂

variable {Kernel : Type u₁} {Complement : Type u₂}
  {Cokernel : Type v₁} {Range : Type v₂}
  [AddCommGroup Kernel] [Module Real Kernel]
  [AddCommGroup Complement] [Module Real Complement]
  [AddCommGroup Cokernel] [Module Real Cokernel]
  [AddCommGroup Range] [Module Real Range]

/-- Parameterized nonlinear Lyapunov--Schmidt problem. -/
structure CanonicalScalarParameterizedLyapunovSchmidtProblem where
  euler : Real → Kernel × Complement → Cokernel × Range
  complementSolver : Real → Kernel → Complement
  rangeEquation : ∀ parameter kernel,
    (euler parameter (kernel, complementSolver parameter kernel)).2 = 0
  rangeUnique : ∀ parameter kernel complement,
    (euler parameter (kernel, complement)).2 = 0 →
      complement = complementSolver parameter kernel

namespace CanonicalScalarParameterizedLyapunovSchmidtProblem

/-- Reduced Euler map. -/
def reducedEuler
    (problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range)) :
    Real → Kernel → Cokernel :=
  fun parameter kernel =>
    (problem.euler parameter
      (kernel, problem.complementSolver parameter kernel)).1

/-- Lift from parameter/kernel coordinates to the full nonlinear domain. -/
def lift
    (problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range)) :
    Real → Kernel → Kernel × Complement :=
  fun parameter kernel =>
    (kernel, problem.complementSolver parameter kernel)

/-- Euler map on the lift. -/
theorem euler_lift
    (problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (parameter : Real) (kernel : Kernel) :
    problem.euler parameter (problem.lift parameter kernel) =
      (problem.reducedEuler parameter kernel, 0) := by
  apply Prod.ext
  · rfl
  · exact problem.rangeEquation parameter kernel

/-- Full zeros are exactly lifted reduced zeros at each parameter. -/
theorem euler_eq_zero_iff
    (problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (parameter : Real) (kernel : Kernel) (complement : Complement) :
    problem.euler parameter (kernel, complement) = 0 ↔
      complement = problem.complementSolver parameter kernel ∧
        problem.reducedEuler parameter kernel = 0 := by
  constructor
  · intro hEuler
    have hComplement := problem.rangeUnique parameter kernel complement
      (congrArg Prod.snd hEuler)
    constructor
    · exact hComplement
    · have hFirst := congrArg Prod.fst hEuler
      simpa [reducedEuler, hComplement] using hFirst
  · rintro ⟨rfl, hReduced⟩
    change problem.euler parameter (problem.lift parameter kernel) = 0
    rw [problem.euler_lift]
    simp [hReduced]

/-- A reduced solution curve lifts to a full solution curve. -/
theorem lift_reduced_solution_curve
    (problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Kernel) (Complement := Complement)
      (Cokernel := Cokernel) (Range := Range))
    (kernelCurve : Real → Kernel)
    (hCurve : ∀ parameter,
      problem.reducedEuler parameter (kernelCurve parameter) = 0) :
    ∀ parameter,
      problem.euler parameter (problem.lift parameter
        (kernelCurve parameter)) = 0 := by
  intro parameter
  rw [problem.euler_lift, hCurve]
  simp

end CanonicalScalarParameterizedLyapunovSchmidtProblem

/-- Exact scalar pitchfork reduced normal form. -/
def canonicalScalarPitchforkReducedEuler
    (cubic parameter amplitude : Real) : Real :=
  amplitude * (parameter + cubic * amplitude ^ 2)

/-- Zero classification of the pitchfork polynomial. -/
theorem canonicalScalarPitchforkReducedEuler_eq_zero_iff
    (cubic parameter amplitude : Real) :
    canonicalScalarPitchforkReducedEuler cubic parameter amplitude = 0 ↔
      amplitude = 0 ∨ parameter + cubic * amplitude ^ 2 = 0 := by
  unfold canonicalScalarPitchforkReducedEuler
  exact mul_eq_zero

/-- Trivial pitchfork branch. -/
@[simp] theorem canonicalScalarPitchforkReducedEuler_zero
    (cubic parameter : Real) :
    canonicalScalarPitchforkReducedEuler cubic parameter 0 = 0 := by
  simp [canonicalScalarPitchforkReducedEuler]

/-- Positive-amplitude nontrivial pitchfork branch. -/
theorem canonicalScalarPitchforkReducedEuler_sqrt
    (cubic parameter : Real)
    (hCubic : cubic ≠ 0)
    (hRatio : 0 ≤ -parameter / cubic) :
    canonicalScalarPitchforkReducedEuler cubic parameter
        (Real.sqrt (-parameter / cubic)) = 0 := by
  rw [canonicalScalarPitchforkReducedEuler_eq_zero_iff]
  right
  rw [Real.sq_sqrt hRatio]
  field_simp
  ring

/-- Negative-amplitude nontrivial pitchfork branch. -/
theorem canonicalScalarPitchforkReducedEuler_neg_sqrt
    (cubic parameter : Real)
    (hCubic : cubic ≠ 0)
    (hRatio : 0 ≤ -parameter / cubic) :
    canonicalScalarPitchforkReducedEuler cubic parameter
        (-Real.sqrt (-parameter / cubic)) = 0 := by
  rw [canonicalScalarPitchforkReducedEuler_eq_zero_iff]
  right
  rw [show (-Real.sqrt (-parameter / cubic)) ^ 2 =
      Real.sqrt (-parameter / cubic) ^ 2 by ring,
    Real.sq_sqrt hRatio]
  field_simp
  ring

/-- Classification of all nontrivial roots by their squared amplitude. -/
theorem canonicalScalarPitchforkReducedEuler_nonzero_iff_sq
    (cubic parameter amplitude : Real)
    (hCubic : cubic ≠ 0)
    (hAmplitude : amplitude ≠ 0) :
    canonicalScalarPitchforkReducedEuler cubic parameter amplitude = 0 ↔
      amplitude ^ 2 = -parameter / cubic := by
  rw [canonicalScalarPitchforkReducedEuler_eq_zero_iff]
  simp [hAmplitude]
  constructor
  · intro hEquation
    apply (eq_div_iff hCubic).2
    linarith
  · intro hSquare
    rw [hSquare]
    field_simp
    ring

/-- If `-parameter/cubic` is negative, only the trivial branch exists. -/
theorem canonicalScalarPitchforkReducedEuler_eq_zero_iff_zero_of_ratio_neg
    (cubic parameter amplitude : Real)
    (hCubic : cubic ≠ 0)
    (hRatio : -parameter / cubic < 0) :
    canonicalScalarPitchforkReducedEuler cubic parameter amplitude = 0 ↔
      amplitude = 0 := by
  constructor
  · intro hEuler
    rcases (canonicalScalarPitchforkReducedEuler_eq_zero_iff
      cubic parameter amplitude).1 hEuler with hZero | hEquation
    · exact hZero
    · by_contra hAmplitude
      have hSquare :=
        (canonicalScalarPitchforkReducedEuler_nonzero_iff_sq
          cubic parameter amplitude hCubic hAmplitude).1 hEuler
      have hNonnegative : 0 ≤ amplitude ^ 2 := sq_nonneg amplitude
      linarith
  · rintro rfl
    simp

/-- Exact pitchfork normal-form data for a parameterized reduction with
one-dimensional kernel and cokernel. -/
structure CanonicalScalarPitchforkNormalFormData
    {Complement : Type u₂} {Range : Type v₂}
    [AddCommGroup Complement] [Module Real Complement]
    [AddCommGroup Range] [Module Real Range]
    (problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Real) (Complement := Complement)
      (Cokernel := Real) (Range := Range)) where
  cubic : Real
  cubic_ne_zero : cubic ≠ 0
  reduced_eq : ∀ parameter amplitude,
    problem.reducedEuler parameter amplitude =
      canonicalScalarPitchforkReducedEuler cubic parameter amplitude

namespace CanonicalScalarPitchforkNormalFormData

/-- Lifted trivial branch. -/
theorem trivial_branch
    {Complement : Type u₂} {Range : Type v₂}
    [AddCommGroup Complement] [Module Real Complement]
    [AddCommGroup Range] [Module Real Range]
    {problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Real) (Complement := Complement)
      (Cokernel := Real) (Range := Range)}
    (normalForm : CanonicalScalarPitchforkNormalFormData problem)
    (parameter : Real) :
    problem.euler parameter (problem.lift parameter 0) = 0 := by
  rw [problem.euler_lift, normalForm.reduced_eq,
    canonicalScalarPitchforkReducedEuler_zero]
  simp

/-- Lifted positive nontrivial branch. -/
theorem positive_branch
    {Complement : Type u₂} {Range : Type v₂}
    [AddCommGroup Complement] [Module Real Complement]
    [AddCommGroup Range] [Module Real Range]
    {problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Real) (Complement := Complement)
      (Cokernel := Real) (Range := Range)}
    (normalForm : CanonicalScalarPitchforkNormalFormData problem)
    (parameter : Real)
    (hRatio : 0 ≤ -parameter / normalForm.cubic) :
    problem.euler parameter
        (problem.lift parameter
          (Real.sqrt (-parameter / normalForm.cubic))) = 0 := by
  rw [problem.euler_lift, normalForm.reduced_eq,
    canonicalScalarPitchforkReducedEuler_sqrt
      normalForm.cubic parameter normalForm.cubic_ne_zero hRatio]
  simp

/-- Lifted negative nontrivial branch. -/
theorem negative_branch
    {Complement : Type u₂} {Range : Type v₂}
    [AddCommGroup Complement] [Module Real Complement]
    [AddCommGroup Range] [Module Real Range]
    {problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Real) (Complement := Complement)
      (Cokernel := Real) (Range := Range)}
    (normalForm : CanonicalScalarPitchforkNormalFormData problem)
    (parameter : Real)
    (hRatio : 0 ≤ -parameter / normalForm.cubic) :
    problem.euler parameter
        (problem.lift parameter
          (-Real.sqrt (-parameter / normalForm.cubic))) = 0 := by
  rw [problem.euler_lift, normalForm.reduced_eq,
    canonicalScalarPitchforkReducedEuler_neg_sqrt
      normalForm.cubic parameter normalForm.cubic_ne_zero hRatio]
  simp

/-- Pitchfork branch certificate. -/
theorem certificate
    {Complement : Type u₂} {Range : Type v₂}
    [AddCommGroup Complement] [Module Real Complement]
    [AddCommGroup Range] [Module Real Range]
    {problem : CanonicalScalarParameterizedLyapunovSchmidtProblem
      (Kernel := Real) (Complement := Complement)
      (Cokernel := Real) (Range := Range)}
    (normalForm : CanonicalScalarPitchforkNormalFormData problem) :
    (∀ parameter,
      problem.euler parameter (problem.lift parameter 0) = 0) ∧
      (∀ parameter,
        0 ≤ -parameter / normalForm.cubic →
          problem.euler parameter
            (problem.lift parameter
              (Real.sqrt (-parameter / normalForm.cubic))) = 0) ∧
      (∀ parameter,
        0 ≤ -parameter / normalForm.cubic →
          problem.euler parameter
            (problem.lift parameter
              (-Real.sqrt (-parameter / normalForm.cubic))) = 0) :=
  ⟨normalForm.trivial_branch,
    normalForm.positive_branch,
    normalForm.negative_branch⟩

end CanonicalScalarPitchforkNormalFormData

end
end P0EFTJanusMappingTorusScalarLagrangianPitchforkBifurcation4D
end JanusFormal
