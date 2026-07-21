import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenSystemDirectSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianBoundedPerturbation4D

/-!
# Two-sector scalar exchange and symmetric mixing

For two identical real Hilbert sectors, this file constructs the exact exchange
involution, its diagonal and relative subspaces, and the symmetric bounded
cross-coupling

`V_kappa(x,y) = (kappa y, kappa x)`.

The coupling has eigenvalue `+kappa` on the exchange-even diagonal sector and
`-kappa` on the exchange-odd relative sector.  This is the Hilbert-space version
of the surviving same-parity two-sector mixing emphasized in Program P-D.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarTwoSectorExchangeCoupling4D

set_option autoImplicit false
noncomputable section

open Set Topology

universe u

variable {Hilbert : Type u}
  [NormedAddCommGroup Hilbert] [InnerProductSpace Real Hilbert]

/-- Exchange involution on two identical Hilbert sectors. -/
def canonicalScalarTwoSectorExchange :
    Hilbert × Hilbert →L[Real] Hilbert × Hilbert where
  toFun field := (field.2, field.1)
  map_add' first second := by ext <;> rfl
  map_smul' scalar field := by ext <;> rfl
  cont := by fun_prop

@[simp] theorem canonicalScalarTwoSectorExchange_apply
    (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorExchange field = (field.2, field.1) :=
  rfl

/-- Exchange is involutive. -/
theorem canonicalScalarTwoSectorExchange_involutive
    (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorExchange
        (canonicalScalarTwoSectorExchange field) = field := by
  ext <;> rfl

/-- Exchange is an isometry. -/
theorem canonicalScalarTwoSectorExchange_norm
    (field : Hilbert × Hilbert) :
    ‖canonicalScalarTwoSectorExchange field‖ = ‖field‖ := by
  simp [Prod.norm_def, add_comm]

/-- Exchange preserves the product inner product. -/
theorem canonicalScalarTwoSectorExchange_inner
    (first second : Hilbert × Hilbert) :
    inner Real (canonicalScalarTwoSectorExchange first)
        (canonicalScalarTwoSectorExchange second) =
      inner Real first second := by
  simp [add_comm]

/-- Exchange-even diagonal sector. -/
def canonicalScalarTwoSectorEvenSubmodule :
    Submodule Real (Hilbert × Hilbert) :=
  LinearMap.ker
    (canonicalScalarTwoSectorExchange.toLinearMap - LinearMap.id)

/-- Exchange-odd relative sector. -/
def canonicalScalarTwoSectorOddSubmodule :
    Submodule Real (Hilbert × Hilbert) :=
  LinearMap.ker
    (canonicalScalarTwoSectorExchange.toLinearMap + LinearMap.id)

@[simp] theorem mem_canonicalScalarTwoSectorEvenSubmodule
    (field : Hilbert × Hilbert) :
    field ∈ canonicalScalarTwoSectorEvenSubmodule ↔ field.1 = field.2 := by
  rw [canonicalScalarTwoSectorEvenSubmodule, LinearMap.mem_ker]
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    apply Prod.ext <;> simp [h]

@[simp] theorem mem_canonicalScalarTwoSectorOddSubmodule
    (field : Hilbert × Hilbert) :
    field ∈ canonicalScalarTwoSectorOddSubmodule ↔ field.1 = -field.2 := by
  rw [canonicalScalarTwoSectorOddSubmodule, LinearMap.mem_ker]
  constructor
  · intro h
    have hFirst := congrArg Prod.fst h
    simpa using hFirst
  · intro h
    apply Prod.ext
    · simpa [h]
    · have h' : field.2 = -field.1 := by rw [h]; simp
      simpa [h']

/-- Projection onto the exchange-even sector. -/
def canonicalScalarTwoSectorEvenProjection :
    Hilbert × Hilbert →L[Real] Hilbert × Hilbert :=
  (1 / 2 : Real) •
    (canonicalScalarTwoSectorExchange + ContinuousLinearMap.id Real _)

/-- Projection onto the exchange-odd sector. -/
def canonicalScalarTwoSectorOddProjection :
    Hilbert × Hilbert →L[Real] Hilbert × Hilbert :=
  (1 / 2 : Real) •
    (ContinuousLinearMap.id Real _ - canonicalScalarTwoSectorExchange)

/-- Even and odd projections reconstruct every two-sector field. -/
theorem canonicalScalarTwoSectorEven_add_odd
    (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorEvenProjection field +
        canonicalScalarTwoSectorOddProjection field = field := by
  unfold canonicalScalarTwoSectorEvenProjection
    canonicalScalarTwoSectorOddProjection
  module

/-- The even projection lies in the diagonal sector. -/
theorem canonicalScalarTwoSectorEvenProjection_mem
    (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorEvenProjection field ∈
      canonicalScalarTwoSectorEvenSubmodule := by
  rw [mem_canonicalScalarTwoSectorEvenSubmodule]
  simp [canonicalScalarTwoSectorEvenProjection, add_comm]

/-- The odd projection lies in the relative sector. -/
theorem canonicalScalarTwoSectorOddProjection_mem
    (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorOddProjection field ∈
      canonicalScalarTwoSectorOddSubmodule := by
  rw [mem_canonicalScalarTwoSectorOddSubmodule]
  simp [canonicalScalarTwoSectorOddProjection]
  module

/-- Symmetric exchange coupling `V_kappa(x,y) = (kappa y,kappa x)`. -/
def canonicalScalarTwoSectorMixingOperator
    (coefficient : Real) :
    Hilbert × Hilbert →L[Real] Hilbert × Hilbert :=
  coefficient • canonicalScalarTwoSectorExchange

@[simp] theorem canonicalScalarTwoSectorMixingOperator_apply
    (coefficient : Real) (field : Hilbert × Hilbert) :
    canonicalScalarTwoSectorMixingOperator coefficient field =
      (coefficient • field.2, coefficient • field.1) := by
  rfl

/-- The exchange mixing is symmetric. -/
theorem canonicalScalarTwoSectorMixingOperator_isSymmetric
    (coefficient : Real) :
    (canonicalScalarTwoSectorMixingOperator coefficient).toLinearMap.IsSymmetric := by
  intro first second
  unfold canonicalScalarTwoSectorMixingOperator
  simp only [ContinuousLinearMap.smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  have h := canonicalScalarTwoSectorExchange_inner first
    (canonicalScalarTwoSectorExchange second)
  rw [canonicalScalarTwoSectorExchange_involutive] at h
  exact h

/-- Exchange mixing commutes with exchange. -/
theorem canonicalScalarTwoSectorMixingOperator_commutes_exchange
    (coefficient : Real) :
    (canonicalScalarTwoSectorMixingOperator coefficient).comp
        canonicalScalarTwoSectorExchange =
      canonicalScalarTwoSectorExchange.comp
        (canonicalScalarTwoSectorMixingOperator coefficient) := by
  ext field <;> rfl

/-- Mixing eigenvalue on the even sector. -/
theorem canonicalScalarTwoSectorMixingOperator_even
    (coefficient : Real)
    (field : canonicalScalarTwoSectorEvenSubmodule (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorMixingOperator coefficient field.1 =
      coefficient • field.1 := by
  have hEven := (mem_canonicalScalarTwoSectorEvenSubmodule field.1).1 field.2
  apply Prod.ext <;> simp [canonicalScalarTwoSectorMixingOperator, hEven]

/-- Mixing eigenvalue on the odd sector. -/
theorem canonicalScalarTwoSectorMixingOperator_odd
    (coefficient : Real)
    (field : canonicalScalarTwoSectorOddSubmodule (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorMixingOperator coefficient field.1 =
      (-coefficient) • field.1 := by
  have hOdd := (mem_canonicalScalarTwoSectorOddSubmodule field.1).1 field.2
  apply Prod.ext <;> simp [canonicalScalarTwoSectorMixingOperator, hOdd]
  module

/-- Orthogonality of exchange-even and exchange-odd sectors. -/
theorem canonicalScalarTwoSectorEven_orthogonal_odd
    (evenField : canonicalScalarTwoSectorEvenSubmodule (Hilbert := Hilbert))
    (oddField : canonicalScalarTwoSectorOddSubmodule (Hilbert := Hilbert)) :
    inner Real evenField.1 oddField.1 = 0 := by
  have hEven := (mem_canonicalScalarTwoSectorEvenSubmodule evenField.1).1 evenField.2
  have hOdd := (mem_canonicalScalarTwoSectorOddSubmodule oddField.1).1 oddField.2
  simp [hEven, hOdd, real_inner_neg_right]

/-- Two-sector exchange/mixing certificate. -/
theorem canonicalScalarTwoSectorExchangeCoupling_certificate
    (coefficient : Real) :
    (canonicalScalarTwoSectorMixingOperator coefficient).toLinearMap.IsSymmetric ∧
      (canonicalScalarTwoSectorMixingOperator coefficient).comp
          canonicalScalarTwoSectorExchange =
        canonicalScalarTwoSectorExchange.comp
          (canonicalScalarTwoSectorMixingOperator coefficient) ∧
      (∀ evenField : canonicalScalarTwoSectorEvenSubmodule (Hilbert := Hilbert),
        canonicalScalarTwoSectorMixingOperator coefficient evenField.1 =
          coefficient • evenField.1) ∧
      (∀ oddField : canonicalScalarTwoSectorOddSubmodule (Hilbert := Hilbert),
        canonicalScalarTwoSectorMixingOperator coefficient oddField.1 =
          (-coefficient) • oddField.1) :=
  ⟨canonicalScalarTwoSectorMixingOperator_isSymmetric coefficient,
    canonicalScalarTwoSectorMixingOperator_commutes_exchange coefficient,
    canonicalScalarTwoSectorMixingOperator_even coefficient,
    canonicalScalarTwoSectorMixingOperator_odd coefficient⟩

end
end P0EFTJanusMappingTorusScalarTwoSectorExchangeCoupling4D
end JanusFormal
