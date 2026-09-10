import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D

/-!
# Euler identity for diagonal homogeneous forms

This support gate proves that the Frechet derivative of a continuous
degree-`d` multilinear form restricted to the diagonal, evaluated in the
radial direction, is `d` times the original diagonal value.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06DiagonalHomogeneousEulerIdentity4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

universe u

variable {FieldFiber : Type u}
variable [NormedAddCommGroup FieldFiber] [NormedSpace Real FieldFiber]

/-- Diagonal evaluation scales by the defining homogeneous degree. -/
theorem programPT06DiagonalHomogeneousTerm_smul
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (scalar : Real) (field : FieldFiber) :
    programPT06DiagonalHomogeneousTerm form (scalar • field) =
      scalar ^ degree * programPT06DiagonalHomogeneousTerm form field := by
  simpa [programPT06DiagonalHomogeneousTerm] using
    (form.map_smul_univ (fun _ : Fin degree => scalar) (fun _ => field))

/-- Euler's radial identity for a diagonal homogeneous form. -/
theorem programPT06DiagonalHomogeneousDerivative_self
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    programPT06DiagonalHomogeneousDerivative form field field =
      (degree : Real) * programPT06DiagonalHomogeneousTerm form field := by
  simp [programPT06DiagonalHomogeneousDerivative_apply,
    programPT06DiagonalHomogeneousTerm]

/-- The genuine Frechet derivative satisfies the same radial identity. -/
theorem programPT06DiagonalHomogeneousTerm_fderiv_self
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    fderiv Real (programPT06DiagonalHomogeneousTerm form) field field =
      (degree : Real) * programPT06DiagonalHomogeneousTerm form field := by
  rw [(programPT06DiagonalHomogeneousTerm_hasFDerivAt form field).fderiv]
  exact programPT06DiagonalHomogeneousDerivative_self form field

end
end P0EFTJanusProgramPT06DiagonalHomogeneousEulerIdentity4D
end JanusFormal
