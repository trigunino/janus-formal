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

private abbrev SectorPair := WithLp 2 (Hilbert × Hilbert)

/-- Diagonal operator on two identical sectors. -/
def canonicalScalarTwoSectorDiagonalOperator
    (operator : Hilbert →L[Real] Hilbert) :
    SectorPair (Hilbert := Hilbert) →L[Real]
      SectorPair (Hilbert := Hilbert) where
  toFun field := WithLp.toLp 2 (operator field.fst, operator field.snd)
  map_add' first second := by
    apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
    ext <;> simp
  map_smul' scalar field := by
    apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
    ext <;> simp
  cont := by fun_prop

/-- Coupled two-sector operator `diag(A,A) + kappa exchange`. -/
def canonicalScalarTwoSectorCoupledOperator
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) :
    SectorPair (Hilbert := Hilbert) →L[Real]
      SectorPair (Hilbert := Hilbert) :=
  canonicalScalarTwoSectorDiagonalOperator operator +
    canonicalScalarTwoSectorMixingOperator coupling

@[simp] theorem canonicalScalarTwoSectorCoupledOperator_apply
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorCoupledOperator operator coupling field =
      WithLp.toLp 2
        (operator field.fst + coupling • field.snd,
          operator field.snd + coupling • field.fst) := by
  apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
  ext <;> simp [canonicalScalarTwoSectorCoupledOperator,
    canonicalScalarTwoSectorDiagonalOperator,
    canonicalScalarTwoSectorMixingOperator]

/-- Symmetry of the coupled two-sector operator. -/
theorem canonicalScalarTwoSectorCoupledOperator_isSymmetric
    (operator : Hilbert →L[Real] Hilbert)
    (hOperator : operator.toLinearMap.IsSymmetric)
    (coupling : Real) :
    (canonicalScalarTwoSectorCoupledOperator operator coupling).toLinearMap.IsSymmetric := by
  intro first second
  change
    (inner Real (operator first.fst + coupling • first.snd) second.fst +
      inner Real (operator first.snd + coupling • first.fst) second.snd) =
    (inner Real first.fst (operator second.fst + coupling • second.snd) +
      inner Real first.snd (operator second.snd + coupling • second.fst))
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  have hFirst := hOperator first.fst second.fst
  have hSecond := hOperator first.snd second.snd
  change inner Real (operator first.fst) second.fst =
    inner Real first.fst (operator second.fst) at hFirst
  change inner Real (operator first.snd) second.snd =
    inner Real first.snd (operator second.snd) at hSecond
  linear_combination hFirst + hSecond

/-- Even coordinate `(x+y)/2`. -/
def canonicalScalarTwoSectorEvenCoordinate :
    SectorPair (Hilbert := Hilbert) →L[Real] Hilbert where
  toFun field := (1 / 2 : Real) • (field.fst + field.snd)
  map_add' first second := by simp; module
  map_smul' scalar field := by simp; module
  cont := by fun_prop

/-- Odd coordinate `(x-y)/2`. -/
def canonicalScalarTwoSectorOddCoordinate :
    SectorPair (Hilbert := Hilbert) →L[Real] Hilbert where
  toFun field := (1 / 2 : Real) • (field.fst - field.snd)
  map_add' first second := by simp; module
  map_smul' scalar field := by simp; module
  cont := by fun_prop

@[simp] theorem canonicalScalarTwoSectorEvenCoordinate_apply
    (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorEvenCoordinate field =
      (1 / 2 : Real) • (field.fst + field.snd) :=
  rfl

@[simp] theorem canonicalScalarTwoSectorOddCoordinate_apply
    (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorOddCoordinate field =
      (1 / 2 : Real) • (field.fst - field.snd) :=
  rfl

/-- Reconstruction from even and odd coordinates. -/
theorem canonicalScalarTwoSectorCoordinate_reconstruction
    (field : SectorPair (Hilbert := Hilbert)) :
    field =
      WithLp.toLp 2
        (canonicalScalarTwoSectorEvenCoordinate field +
            canonicalScalarTwoSectorOddCoordinate field,
          canonicalScalarTwoSectorEvenCoordinate field -
            canonicalScalarTwoSectorOddCoordinate field) := by
  apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
  apply Prod.ext <;>
    simp [canonicalScalarTwoSectorEvenCoordinate,
      canonicalScalarTwoSectorOddCoordinate] <;> module

/-- Coupled operator on a pure even pair. -/
theorem canonicalScalarTwoSectorCoupledOperator_even_pair
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert) :
    canonicalScalarTwoSectorCoupledOperator operator coupling
        (WithLp.toLp 2 (field, field)) =
      WithLp.toLp 2
        (operator field + coupling • field,
          operator field + coupling • field) := by
  simp

/-- Coupled operator on a pure odd pair. -/
theorem canonicalScalarTwoSectorCoupledOperator_odd_pair
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : Hilbert) :
    canonicalScalarTwoSectorCoupledOperator operator coupling
        (WithLp.toLp 2 (field, -field)) =
      WithLp.toLp 2
        (operator field - coupling • field,
          -(operator field - coupling • field)) := by
  apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
  apply Prod.ext
  · simp
    module
  · simp
    module

/-- Two-sector quadratic form. -/
def canonicalScalarTwoSectorCoupledQuadratic
    (operator : Hilbert →L[Real] Hilbert)
    (coupling : Real) (field : SectorPair (Hilbert := Hilbert)) : Real :=
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
    (coupling : Real) (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorCoupledQuadratic operator coupling field =
      2 * canonicalScalarTwoSectorEvenQuadratic operator coupling
        (canonicalScalarTwoSectorEvenCoordinate field) +
      2 * canonicalScalarTwoSectorOddQuadratic operator coupling
        (canonicalScalarTwoSectorOddCoordinate field) := by
  let evenField := canonicalScalarTwoSectorEvenCoordinate field
  let oddField := canonicalScalarTwoSectorOddCoordinate field
  have hReconstruct := canonicalScalarTwoSectorCoordinate_reconstruction field
  conv_lhs => rw [hReconstruct]
  unfold canonicalScalarTwoSectorCoupledQuadratic
    canonicalScalarTwoSectorEvenQuadratic
    canonicalScalarTwoSectorOddQuadratic
  rw [canonicalScalarTwoSectorCoupledOperator_apply]
  simp only [WithLp.prod_inner_apply, WithLp.toLp_fst, WithLp.toLp_snd,
    map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

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
    (field : SectorPair (Hilbert := Hilbert)) :
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
      (∀ field : SectorPair (Hilbert := Hilbert),
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
