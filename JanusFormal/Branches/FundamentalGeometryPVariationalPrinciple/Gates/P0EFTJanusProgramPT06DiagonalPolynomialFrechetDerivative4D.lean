import Mathlib

/-!
# Frechet derivatives of diagonal polynomials through degree four

This support gate computes the Frechet derivative of a continuous multilinear
form restricted to the diagonal.  The derivative is the sum obtained by
inserting the variation in each slot.  Constant, linear, quadratic, cubic and
quartic terms are then assembled into one degree-at-most-four polynomial.

The result is generic in the normed field-value fiber.  It does not identify a
physical Euler operator or assert a Candidate-A realization.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

universe u

/-- Continuous homogeneous forms of a fixed degree on one field fiber. -/
abbrev ProgramPT06ContinuousHomogeneousForm4D
    (FieldFiber : Type u) [NormedAddCommGroup FieldFiber]
    [NormedSpace Real FieldFiber] (degree : Nat) :=
  ContinuousMultilinearMap Real (fun _ : Fin degree => FieldFiber) Real

abbrev ProgramPT06ContinuousQuadraticForm4D
    (FieldFiber : Type u) [NormedAddCommGroup FieldFiber]
    [NormedSpace Real FieldFiber] :=
  ProgramPT06ContinuousHomogeneousForm4D FieldFiber 2

abbrev ProgramPT06ContinuousCubicForm4D
    (FieldFiber : Type u) [NormedAddCommGroup FieldFiber]
    [NormedSpace Real FieldFiber] :=
  ProgramPT06ContinuousHomogeneousForm4D FieldFiber 3

abbrev ProgramPT06ContinuousQuarticForm4D
    (FieldFiber : Type u) [NormedAddCommGroup FieldFiber]
    [NormedSpace Real FieldFiber] :=
  ProgramPT06ContinuousHomogeneousForm4D FieldFiber 4

variable {FieldFiber : Type u}
variable [NormedAddCommGroup FieldFiber] [NormedSpace Real FieldFiber]

/-- Diagonal evaluation of a continuous homogeneous form. -/
def programPT06DiagonalHomogeneousTerm
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree) :
    FieldFiber → Real :=
  fun field => form (fun _ => field)

/-- The derivative of a diagonal homogeneous term: insert the variation once
in every multilinear slot and sum the resulting linear maps. -/
def programPT06DiagonalHomogeneousDerivative
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) : FieldFiber →L[Real] Real :=
  ∑ slot : Fin degree,
    form.toContinuousLinearMap (fun _ => field) slot

@[simp] theorem programPT06DiagonalHomogeneousDerivative_apply
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field direction : FieldFiber) :
    programPT06DiagonalHomogeneousDerivative form field direction =
      ∑ slot : Fin degree,
        form (Function.update (fun _ => field) slot direction) := by
  simp [programPT06DiagonalHomogeneousDerivative]

/-- Frechet derivative of diagonal evaluation in arbitrary finite degree. -/
theorem programPT06DiagonalHomogeneousTerm_hasFDerivAt
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    HasFDerivAt (programPT06DiagonalHomogeneousTerm form)
      (programPT06DiagonalHomogeneousDerivative form field) field := by
  change HasFDerivAt
    (fun candidate : FieldFiber => form (fun _ => candidate))
    (∑ slot : Fin degree,
      form.toContinuousLinearMap (fun _ => field) slot) field
  exact HasFDerivAt.multilinear_comp form
    (g := fun _ : Fin degree => fun candidate : FieldFiber => candidate)
    (g' := fun _ : Fin degree => ContinuousLinearMap.id Real FieldFiber)
    (x := field)
    (fun _ => (ContinuousLinearMap.id Real FieldFiber).hasFDerivAt)

/-- A constant term has zero Frechet derivative. -/
def programPT06DiagonalConstantTerm (constant : Real) : FieldFiber → Real :=
  fun _ => constant

theorem programPT06DiagonalConstantTerm_hasFDerivAt
    (constant : Real) (field : FieldFiber) :
    HasFDerivAt (programPT06DiagonalConstantTerm constant)
      (0 : FieldFiber →L[Real] Real) field := by
  change HasFDerivAt (fun _ : FieldFiber => constant) 0 field
  exact hasFDerivAt_const (𝕜 := Real) (E := FieldFiber) constant field

/-- A linear term is its own Frechet derivative. -/
def programPT06DiagonalLinearTerm
    (linear : FieldFiber →L[Real] Real) : FieldFiber → Real :=
  linear

theorem programPT06DiagonalLinearTerm_hasFDerivAt
    (linear : FieldFiber →L[Real] Real) (field : FieldFiber) :
    HasFDerivAt (programPT06DiagonalLinearTerm linear) linear field := by
  simpa [programPT06DiagonalLinearTerm] using
    (linear.hasFDerivAt :
      HasFDerivAt (fun candidate : FieldFiber => linear candidate) linear field)

def programPT06DiagonalQuadraticTerm
    (form : ProgramPT06ContinuousQuadraticForm4D FieldFiber) :
    FieldFiber → Real :=
  programPT06DiagonalHomogeneousTerm form

def programPT06DiagonalQuadraticDerivative
    (form : ProgramPT06ContinuousQuadraticForm4D FieldFiber)
    (field : FieldFiber) : FieldFiber →L[Real] Real :=
  programPT06DiagonalHomogeneousDerivative form field

@[simp] theorem programPT06DiagonalQuadraticDerivative_apply
    (form : ProgramPT06ContinuousQuadraticForm4D FieldFiber)
    (field direction : FieldFiber) :
    programPT06DiagonalQuadraticDerivative form field direction =
      ∑ slot : Fin 2,
        form (Function.update (fun _ => field) slot direction) := by
  simpa [programPT06DiagonalQuadraticDerivative] using
    programPT06DiagonalHomogeneousDerivative_apply form field direction

theorem programPT06DiagonalQuadraticTerm_hasFDerivAt
    (form : ProgramPT06ContinuousQuadraticForm4D FieldFiber)
    (field : FieldFiber) :
    HasFDerivAt (programPT06DiagonalQuadraticTerm form)
      (programPT06DiagonalQuadraticDerivative form field) field := by
  simpa [programPT06DiagonalQuadraticTerm,
    programPT06DiagonalQuadraticDerivative] using
    programPT06DiagonalHomogeneousTerm_hasFDerivAt form field

def programPT06DiagonalCubicTerm
    (form : ProgramPT06ContinuousCubicForm4D FieldFiber) :
    FieldFiber → Real :=
  programPT06DiagonalHomogeneousTerm form

def programPT06DiagonalCubicDerivative
    (form : ProgramPT06ContinuousCubicForm4D FieldFiber)
    (field : FieldFiber) : FieldFiber →L[Real] Real :=
  programPT06DiagonalHomogeneousDerivative form field

@[simp] theorem programPT06DiagonalCubicDerivative_apply
    (form : ProgramPT06ContinuousCubicForm4D FieldFiber)
    (field direction : FieldFiber) :
    programPT06DiagonalCubicDerivative form field direction =
      ∑ slot : Fin 3,
        form (Function.update (fun _ => field) slot direction) := by
  simpa [programPT06DiagonalCubicDerivative] using
    programPT06DiagonalHomogeneousDerivative_apply form field direction

theorem programPT06DiagonalCubicTerm_hasFDerivAt
    (form : ProgramPT06ContinuousCubicForm4D FieldFiber)
    (field : FieldFiber) :
    HasFDerivAt (programPT06DiagonalCubicTerm form)
      (programPT06DiagonalCubicDerivative form field) field := by
  simpa [programPT06DiagonalCubicTerm,
    programPT06DiagonalCubicDerivative] using
    programPT06DiagonalHomogeneousTerm_hasFDerivAt form field

def programPT06DiagonalQuarticTerm
    (form : ProgramPT06ContinuousQuarticForm4D FieldFiber) :
    FieldFiber → Real :=
  programPT06DiagonalHomogeneousTerm form

def programPT06DiagonalQuarticDerivative
    (form : ProgramPT06ContinuousQuarticForm4D FieldFiber)
    (field : FieldFiber) : FieldFiber →L[Real] Real :=
  programPT06DiagonalHomogeneousDerivative form field

@[simp] theorem programPT06DiagonalQuarticDerivative_apply
    (form : ProgramPT06ContinuousQuarticForm4D FieldFiber)
    (field direction : FieldFiber) :
    programPT06DiagonalQuarticDerivative form field direction =
      ∑ slot : Fin 4,
        form (Function.update (fun _ => field) slot direction) := by
  simpa [programPT06DiagonalQuarticDerivative] using
    programPT06DiagonalHomogeneousDerivative_apply form field direction

theorem programPT06DiagonalQuarticTerm_hasFDerivAt
    (form : ProgramPT06ContinuousQuarticForm4D FieldFiber)
    (field : FieldFiber) :
    HasFDerivAt (programPT06DiagonalQuarticTerm form)
      (programPT06DiagonalQuarticDerivative form field) field := by
  simpa [programPT06DiagonalQuarticTerm,
    programPT06DiagonalQuarticDerivative] using
    programPT06DiagonalHomogeneousTerm_hasFDerivAt form field

/-- Continuous diagonal polynomial data through degree four. -/
structure ProgramPT06DiagonalPolynomialUpToFour4D
    (FieldFiber : Type u) [NormedAddCommGroup FieldFiber]
    [NormedSpace Real FieldFiber] where
  constant : Real
  linear : FieldFiber →L[Real] Real
  quadratic : ProgramPT06ContinuousQuadraticForm4D FieldFiber
  cubic : ProgramPT06ContinuousCubicForm4D FieldFiber
  quartic : ProgramPT06ContinuousQuarticForm4D FieldFiber

def programPT06DiagonalPolynomialEvaluation
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber) :
    FieldFiber → Real :=
  fun field =>
    programPT06DiagonalConstantTerm polynomial.constant field +
      programPT06DiagonalLinearTerm polynomial.linear field +
      programPT06DiagonalQuadraticTerm polynomial.quadratic field +
      programPT06DiagonalCubicTerm polynomial.cubic field +
      programPT06DiagonalQuarticTerm polynomial.quartic field

def programPT06DiagonalPolynomialDerivative
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) : FieldFiber →L[Real] Real :=
  polynomial.linear +
    programPT06DiagonalQuadraticDerivative polynomial.quadratic field +
    programPT06DiagonalCubicDerivative polynomial.cubic field +
    programPT06DiagonalQuarticDerivative polynomial.quartic field

@[simp] theorem programPT06DiagonalPolynomialDerivative_apply
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field direction : FieldFiber) :
    programPT06DiagonalPolynomialDerivative polynomial field direction =
      polynomial.linear direction +
        (∑ slot : Fin 2, polynomial.quadratic
          (Function.update (fun _ => field) slot direction)) +
        (∑ slot : Fin 3, polynomial.cubic
          (Function.update (fun _ => field) slot direction)) +
        ∑ slot : Fin 4, polynomial.quartic
          (Function.update (fun _ => field) slot direction) := by
  simp [programPT06DiagonalPolynomialDerivative]

/-- Explicit Frechet derivative of the full degree-at-most-four diagonal
polynomial. -/
theorem programPT06DiagonalPolynomialEvaluation_hasFDerivAt
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) :
    HasFDerivAt (programPT06DiagonalPolynomialEvaluation polynomial)
      (programPT06DiagonalPolynomialDerivative polynomial field) field := by
  have hConstant := programPT06DiagonalConstantTerm_hasFDerivAt
    (FieldFiber := FieldFiber) polynomial.constant field
  have hLinear := programPT06DiagonalLinearTerm_hasFDerivAt
    polynomial.linear field
  have hQuadratic := programPT06DiagonalQuadraticTerm_hasFDerivAt
    polynomial.quadratic field
  have hCubic := programPT06DiagonalCubicTerm_hasFDerivAt
    polynomial.cubic field
  have hQuartic := programPT06DiagonalQuarticTerm_hasFDerivAt
    polynomial.quartic field
  change HasFDerivAt
    (fun candidate : FieldFiber =>
      programPT06DiagonalConstantTerm polynomial.constant candidate +
        programPT06DiagonalLinearTerm polynomial.linear candidate +
        programPT06DiagonalQuadraticTerm polynomial.quadratic candidate +
        programPT06DiagonalCubicTerm polynomial.cubic candidate +
        programPT06DiagonalQuarticTerm polynomial.quartic candidate)
    (polynomial.linear +
      programPT06DiagonalQuadraticDerivative polynomial.quadratic field +
      programPT06DiagonalCubicDerivative polynomial.cubic field +
      programPT06DiagonalQuarticDerivative polynomial.quartic field) field
  have hSum :=
    (((hConstant.add hLinear).add hQuadratic).add hCubic).add hQuartic
  have hFunction :
      (programPT06DiagonalConstantTerm polynomial.constant +
          programPT06DiagonalLinearTerm polynomial.linear +
          programPT06DiagonalQuadraticTerm polynomial.quadratic +
          programPT06DiagonalCubicTerm polynomial.cubic +
          programPT06DiagonalQuarticTerm polynomial.quartic) =
        fun candidate : FieldFiber =>
          programPT06DiagonalConstantTerm polynomial.constant candidate +
            programPT06DiagonalLinearTerm polynomial.linear candidate +
            programPT06DiagonalQuadraticTerm polynomial.quadratic candidate +
            programPT06DiagonalCubicTerm polynomial.cubic candidate +
            programPT06DiagonalQuarticTerm polynomial.quartic candidate := by
    funext candidate
    rfl
  have hDerivative :
      (0 : FieldFiber →L[Real] Real) + polynomial.linear +
          programPT06DiagonalQuadraticDerivative polynomial.quadratic field +
          programPT06DiagonalCubicDerivative polynomial.cubic field +
          programPT06DiagonalQuarticDerivative polynomial.quartic field =
        polynomial.linear +
          programPT06DiagonalQuadraticDerivative polynomial.quadratic field +
          programPT06DiagonalCubicDerivative polynomial.cubic field +
          programPT06DiagonalQuarticDerivative polynomial.quartic field := by
    simp
  rw [hFunction, hDerivative] at hSum
  exact hSum

theorem programPT06DiagonalPolynomialEvaluation_fderiv
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) :
    fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial) field =
      programPT06DiagonalPolynomialDerivative polynomial field :=
  (programPT06DiagonalPolynomialEvaluation_hasFDerivAt polynomial field).fderiv

end

end P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D
end JanusFormal
