import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarTwoSectorExchangeCoupling4D

/-!
# Quadratic diagonalization of the two-sector scalar operator

For one bounded symmetric scalar operator `A` and exchange coupling `kappa`, the
two-sector operator is

`T(x,y) = (A x + kappa y, A y + kappa x)`.

Writing

`e = (x+y)/2`, `o = (x-y)/2`,

one has `(x,y) = (e,e) + (o,-o)`.  The quadratic form of `T` splits exactly into
an even block `A+kappa` and an odd block `A-kappa`.  This is the analytic
realization of the same-parity two-sector mixing classification.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarTwoSectorQuadraticDiagonalization4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarTwoSectorExchangeCoupling4D

universe u

variable {Hilbert : Type u}
  [NormedAddCommGroup Hilbert] [InnerProductSpace Real Hilbert]

/-- Diagonal operator on two identical sectors. -/
def canonicalScalarTwoSectorDiagonalOperator
    (operator : Hilbert →L[Real] Hilbert) :
    Hilbert × Hilbert →L[Real] Hilbert × Hilbert where
  toFun field := (operator field.1, operator field.2)
  map_add' first second := by ext <;> simp
  map_smul' scalar field := by ext <;> simp
  cont := by fun_prop

/-- Coupled two-sector operator `diag(A,A) + kappa exchange`. -/
def canonicalScalarTwoSectorCoupledOperator
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) :
    Hilbert × Hilbert →L[Real] Hilbert × Hilbert :=
  canonicalScalarTwoSectorDiagonalOperator operator +
    canonicalScalarTwoSectorMixingOperator coupling

@[simp] theorem canonicalScalarTwoSectorCoupledOperator_apply
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorCoupledOperator operator coupling field =
      (operator field.1 + coupling • field.2,
        operator field.2 + coupling • field.1) :=
  rfl

/-- Symmetry of the coupled two-sector operator. -/
theorem canonicalScalarTwoSectorCoupledOperator_isSymmetric
    (operator : Hilbert →L[Real] Hilbert)
    (hOperator : operator.toLinearMap.IsSymmetric)
    (coupling : Real) :
    (canonicalScalarTwoSectorCoupledOperator operator coupling).toLinearMap.IsSymmetric := by
  intro first second
  simp only [canonicalScalarTwoSectorCoupledOperator_apply,
    inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hOperator first.1 second.1, hOperator first.2 second.2]
  have hCrossFirst := real_inner_comm first.2 second.1
  have hCrossSecond := real_inner_comm first.1 second.2
  linarith

/-- Even coordinate `(x+y)/2`. -/
def canonicalScalarTwoSectorEvenCoordinate :
    Hilbert × Hilbert →L[Real] Hilbert :=
  (1 / 2 : Real) •
    (ContinuousLinearMap.fst Real Hilbert Hilbert +
      ContinuousLinearMap.snd Real Hilbert Hilbert)

/-- Odd coordinate `(x-y)/2`. -/
def canonicalScalarTwoSectorOddCoordinate :
    Hilbert × Hilbert →L[Real] Hilbert :=
  (1 / 2 : Real) •
    (ContinuousLinearMap.fst Real Hilbert Hilbert -
      ContinuousLinearMap.snd Real Hilbert Hilbert)

@[simp] theorem canonicalScalarTwoSectorEvenCoordinate_apply
    (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorEvenCoordinate field =
      (1 / 2 : Real) • (field.1 + field.2) :=
  rfl

@[simp] theorem canonicalScalarTwoSectorOddCoordinate_apply
    (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorOddCoordinate field =
      (1 / 2 : Real) • (field.1 - field.2) :=
  rfl

/-- Reconstruction from even and odd coordinates. -/
theorem canonicalScalarTwoSectorCoordinate_reconstruction
    (field : Hilbert × Hilbert) :
    field =
      (canonicalScalarTwoSectorEvenCoordinate field +
          canonicalScalarTwoSectorOddCoordinate field,
        canonicalScalarTwoSectorEvenCoordinate field -
          canonicalScalarTwoSectorOddCoordinate field) := by
  apply Prod.ext <;>
    simp [canonicalScalarTwoSectorEvenCoordinate,
      canonicalScalarTwoSectorOddCoordinate] <;> module

/-- Coupled operator on a pure even pair. -/
theorem canonicalScalarTwoSectorCoupledOperator_even_pair
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert) :
    canonicalScalarTwoSectorCoupledOperator operator coupling (field, field) =
      (operator field + coupling • field,
        operator field + coupling • field) := by
  rfl

/-- Coupled operator on a pure odd pair. -/
theorem canonicalScalarTwoSectorCoupledOperator_odd_pair
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert) :
    canonicalScalarTwoSectorCoupledOperator operator coupling (field, -field) =
      (operator field - coupling • field,
        -(operator field - coupling • field)) := by
  apply Prod.ext
  · simp
    module
  · simp
    module

/-- Two-sector quadratic form. -/
def canonicalScalarTwoSectorCoupledQuadratic
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert × Hilbert) : Real :=
  inner Real
    (canonicalScalarTwoSectorCoupledOperator operator coupling field) field

/-- Even one-sector shifted quadratic form. -/
def canonicalScalarTwoSectorEvenQuadratic
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert) : Real :=
  inner Real (operator field + coupling • field) field

/-- Odd one-sector shifted quadratic form. -/
def canonicalScalarTwoSectorOddQuadratic
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert) : Real :=
  inner Real (operator field - coupling • field) field

/-- Exact even/odd diagonalization of the coupled quadratic form. -/
theorem canonicalScalarTwoSectorCoupledQuadratic_diagonalization
    (operator : Hilbert →L[Real] Hilbert)
    (hOperator : operator.toLinearMap.IsSymmetric)
    (coupling : Real) (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorCoupledQuadratic operator coupling field =
      2 * canonicalScalarTwoSectorEvenQuadratic operator coupling
        (canonicalScalarTwoSectorEvenCoordinate field) +
      2 * canonicalScalarTwoSectorOddQuadratic operator coupling
        (canonicalScalarTwoSectorOddCoordinate field) := by
  let evenField := canonicalScalarTwoSectorEvenCoordinate field
  let oddField := canonicalScalarTwoSectorOddCoordinate field
  have hReconstruct := canonicalScalarTwoSectorCoordinate_reconstruction field
  rw [hReconstruct]
  unfold canonicalScalarTwoSectorCoupledQuadratic
    canonicalScalarTwoSectorEvenQuadratic
    canonicalScalarTwoSectorOddQuadratic
  rw [canonicalScalarTwoSectorCoupledOperator_apply]
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hOperator evenField oddField]
  have hInner := real_inner_comm evenField oddField
  ring_nf at hInner ⊢
  linarith

/-- Lower bounds on the shifted even/odd blocks imply a lower bound for the full
coupled quadratic form. -/
theorem canonicalScalarTwoSectorCoupledQuadratic_lower_bound
    (operator : Hilbert →L[Real] Hilbert)
    (hOperator : operator.toLinearMap.IsSymmetric)
    (coupling evenLower oddLower : Real)
    (hEven : ∀ field : Hilbert,
      evenLower * ‖field‖ ^ 2 ≤
        canonicalScalarTwoSectorEvenQuadratic operator coupling field)
    (hOdd : ∀ field : Hilbert,
      oddLower * ‖field‖ ^ 2 ≤
        canonicalScalarTwoSectorOddQuadratic operator coupling field)
    (field : Hilbert × Hilbert) :
    2 * evenLower * ‖canonicalScalarTwoSectorEvenCoordinate field‖ ^ 2 +
        2 * oddLower * ‖canonicalScalarTwoSectorOddCoordinate field‖ ^ 2 ≤
      canonicalScalarTwoSectorCoupledQuadratic operator coupling field := by
  rw [canonicalScalarTwoSectorCoupledQuadratic_diagonalization
    operator hOperator coupling field]
  nlinarith [hEven (canonicalScalarTwoSectorEvenCoordinate field),
    hOdd (canonicalScalarTwoSectorOddCoordinate field)]

/-- Two-sector diagonalization certificate. -/
theorem canonicalScalarTwoSectorQuadraticDiagonalization_certificate
    (operator : Hilbert →L[Real] Hilbert)
    (hOperator : operator.toLinearMap.IsSymmetric)
    (coupling : Real) :
    (canonicalScalarTwoSectorCoupledOperator operator coupling).toLinearMap.IsSymmetric ∧
      (∀ field : Hilbert × Hilbert,
        canonicalScalarTwoSectorCoupledQuadratic operator coupling field =
          2 * canonicalScalarTwoSectorEvenQuadratic operator coupling
            (canonicalScalarTwoSectorEvenCoordinate field) +
          2 * canonicalScalarTwoSectorOddQuadratic operator coupling
            (canonicalScalarTwoSectorOddCoordinate field)) :=
  ⟨canonicalScalarTwoSectorCoupledOperator_isSymmetric
      operator hOperator coupling,
    canonicalScalarTwoSectorCoupledQuadratic_diagonalization
      operator hOperator coupling⟩

end
end P0EFTJanusMappingTorusScalarTwoSectorQuadraticDiagonalization4D
end JanusFormal
