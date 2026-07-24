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

private abbrev SectorPair := WithLp 2 (Hilbert × Hilbert)

/-- Exchange involution on two identical Hilbert sectors. -/
def canonicalScalarTwoSectorExchange :
    SectorPair (Hilbert := Hilbert) →L[Real] SectorPair (Hilbert := Hilbert) where
  toFun field := WithLp.toLp 2 (field.snd, field.fst)
  map_add' first second := by
    apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
    ext <;> simp
  map_smul' scalar field := by
    apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
    ext <;> simp
  cont := by fun_prop

@[simp] theorem canonicalScalarTwoSectorExchange_apply
    (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorExchange field =
      WithLp.toLp 2 (field.snd, field.fst) :=
  rfl

/-- Exchange is involutive. -/
theorem canonicalScalarTwoSectorExchange_involutive
    (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorExchange
        (canonicalScalarTwoSectorExchange field) = field := by
  apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
  ext <;> simp [canonicalScalarTwoSectorExchange]

/-- Exchange is an isometry. -/
theorem canonicalScalarTwoSectorExchange_norm
    (field : SectorPair (Hilbert := Hilbert)) :
    ‖canonicalScalarTwoSectorExchange field‖ = ‖field‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  simp [canonicalScalarTwoSectorExchange, add_comm]

/-- Exchange preserves the product inner product. -/
theorem canonicalScalarTwoSectorExchange_inner
    (first second : SectorPair (Hilbert := Hilbert)) :
    inner Real (canonicalScalarTwoSectorExchange first)
        (canonicalScalarTwoSectorExchange second) =
      inner Real first second := by
  simp [WithLp.prod_inner_apply, canonicalScalarTwoSectorExchange, add_comm]

/-- Exchange-even diagonal sector. -/
def canonicalScalarTwoSectorEvenSubmodule :
    Submodule Real (SectorPair (Hilbert := Hilbert)) :=
  LinearMap.ker
    (canonicalScalarTwoSectorExchange.toLinearMap - LinearMap.id)

/-- Exchange-odd relative sector. -/
def canonicalScalarTwoSectorOddSubmodule :
    Submodule Real (SectorPair (Hilbert := Hilbert)) :=
  LinearMap.ker
    (canonicalScalarTwoSectorExchange.toLinearMap + LinearMap.id)

@[simp] theorem mem_canonicalScalarTwoSectorEvenSubmodule
    (field : SectorPair (Hilbert := Hilbert)) :
    field ∈ canonicalScalarTwoSectorEvenSubmodule ↔ field.fst = field.snd := by
  rw [canonicalScalarTwoSectorEvenSubmodule, LinearMap.mem_ker]
  constructor
  · intro h
    have hFirst := congrArg
      (fun pair : SectorPair (Hilbert := Hilbert) => pair.fst) h
    have hDifference : field.snd - field.fst = 0 := by
      simpa [LinearMap.sub_apply] using hFirst
    exact (sub_eq_zero.mp hDifference).symm
  · intro h
    apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
    ext <;> simp [LinearMap.sub_apply, canonicalScalarTwoSectorExchange, h]

@[simp] theorem mem_canonicalScalarTwoSectorOddSubmodule
    (field : SectorPair (Hilbert := Hilbert)) :
    field ∈ canonicalScalarTwoSectorOddSubmodule ↔ field.fst = -field.snd := by
  rw [canonicalScalarTwoSectorOddSubmodule, LinearMap.mem_ker]
  constructor
  · intro h
    have hFirst := congrArg
      (fun pair : SectorPair (Hilbert := Hilbert) => pair.fst) h
    have hSum : field.snd + field.fst = 0 := by
      simpa [LinearMap.add_apply] using hFirst
    exact eq_neg_of_add_eq_zero_right hSum
  · intro h
    apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
    ext <;> simp [LinearMap.add_apply, canonicalScalarTwoSectorExchange, h]

/-- Projection onto the exchange-even sector. -/
def canonicalScalarTwoSectorEvenProjection :
    SectorPair (Hilbert := Hilbert) →L[Real] SectorPair (Hilbert := Hilbert) :=
  (1 / 2 : Real) •
    (canonicalScalarTwoSectorExchange + ContinuousLinearMap.id Real _)

/-- Projection onto the exchange-odd sector. -/
def canonicalScalarTwoSectorOddProjection :
    SectorPair (Hilbert := Hilbert) →L[Real] SectorPair (Hilbert := Hilbert) :=
  (1 / 2 : Real) •
    (ContinuousLinearMap.id Real _ - canonicalScalarTwoSectorExchange)

/-- Even and odd projections reconstruct every two-sector field. -/
theorem canonicalScalarTwoSectorEven_add_odd
    (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorEvenProjection field +
        canonicalScalarTwoSectorOddProjection field = field := by
  unfold canonicalScalarTwoSectorEvenProjection
    canonicalScalarTwoSectorOddProjection
  change (1 / 2 : Real) • (canonicalScalarTwoSectorExchange field + field) +
      (1 / 2 : Real) • (field - canonicalScalarTwoSectorExchange field) = field
  module

/-- The even projection lies in the diagonal sector. -/
theorem canonicalScalarTwoSectorEvenProjection_mem
    (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorEvenProjection field ∈
      canonicalScalarTwoSectorEvenSubmodule := by
  rw [mem_canonicalScalarTwoSectorEvenSubmodule]
  simp [canonicalScalarTwoSectorEvenProjection, add_comm]

/-- The odd projection lies in the relative sector. -/
theorem canonicalScalarTwoSectorOddProjection_mem
    (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorOddProjection field ∈
      canonicalScalarTwoSectorOddSubmodule := by
  rw [mem_canonicalScalarTwoSectorOddSubmodule]
  simp [canonicalScalarTwoSectorOddProjection]
  module

/-- Symmetric exchange coupling `V_kappa(x,y) = (kappa y,kappa x)`. -/
def canonicalScalarTwoSectorMixingOperator
    (coefficient : Real) :
    SectorPair (Hilbert := Hilbert) →L[Real] SectorPair (Hilbert := Hilbert) :=
  coefficient • canonicalScalarTwoSectorExchange

@[simp] theorem canonicalScalarTwoSectorMixingOperator_apply
    (coefficient : Real) (field : SectorPair (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorMixingOperator coefficient field =
      WithLp.toLp 2
        (coefficient • field.snd, coefficient • field.fst) := by
  rfl

/-- The exchange mixing is symmetric. -/
theorem canonicalScalarTwoSectorMixingOperator_isSymmetric
    (coefficient : Real) :
    (canonicalScalarTwoSectorMixingOperator (Hilbert := Hilbert)
      coefficient).toLinearMap.IsSymmetric := by
  intro first second
  change inner Real
      (coefficient • canonicalScalarTwoSectorExchange first) second =
    inner Real first
      (coefficient • canonicalScalarTwoSectorExchange second)
  rw [real_inner_smul_left, real_inner_smul_right]
  have h := canonicalScalarTwoSectorExchange_inner first
    (canonicalScalarTwoSectorExchange second)
  rw [canonicalScalarTwoSectorExchange_involutive] at h
  exact congrArg (fun value : Real => coefficient * value) h

/-- Exchange mixing commutes with exchange. -/
theorem canonicalScalarTwoSectorMixingOperator_commutes_exchange
    (coefficient : Real) :
    (canonicalScalarTwoSectorMixingOperator (Hilbert := Hilbert)
      coefficient).comp
        (canonicalScalarTwoSectorExchange (Hilbert := Hilbert)) =
      (canonicalScalarTwoSectorExchange (Hilbert := Hilbert)).comp
        (canonicalScalarTwoSectorMixingOperator (Hilbert := Hilbert)
          coefficient) := by
  ext field <;> rfl

/-- Mixing eigenvalue on the even sector. -/
theorem canonicalScalarTwoSectorMixingOperator_even
    (coefficient : Real)
    (field : canonicalScalarTwoSectorEvenSubmodule (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorMixingOperator coefficient field.1 =
      coefficient • field.1 := by
  have hEven := (mem_canonicalScalarTwoSectorEvenSubmodule field.1).1 field.2
  apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
  ext <;> simp [canonicalScalarTwoSectorMixingOperator, hEven]

/-- Mixing eigenvalue on the odd sector. -/
theorem canonicalScalarTwoSectorMixingOperator_odd
    (coefficient : Real)
    (field : canonicalScalarTwoSectorOddSubmodule (Hilbert := Hilbert)) :
    canonicalScalarTwoSectorMixingOperator coefficient field.1 =
      (-coefficient) • field.1 := by
  have hOdd := (mem_canonicalScalarTwoSectorOddSubmodule field.1).1 field.2
  apply (WithLp.equiv 2 (Hilbert × Hilbert)).injective
  ext <;> simp [canonicalScalarTwoSectorMixingOperator, hOdd]

/-- Orthogonality of exchange-even and exchange-odd sectors. -/
theorem canonicalScalarTwoSectorEven_orthogonal_odd
    (evenField : canonicalScalarTwoSectorEvenSubmodule (Hilbert := Hilbert))
    (oddField : canonicalScalarTwoSectorOddSubmodule (Hilbert := Hilbert)) :
    inner Real evenField.1 oddField.1 = 0 := by
  have hEven := (mem_canonicalScalarTwoSectorEvenSubmodule evenField.1).1 evenField.2
  have hOdd := (mem_canonicalScalarTwoSectorOddSubmodule oddField.1).1 oddField.2
  change inner Real (WithLp.fst evenField.1) (WithLp.fst oddField.1) +
      inner Real (WithLp.snd evenField.1) (WithLp.snd oddField.1) = 0
  rw [hEven, hOdd]
  simp

/-- Two-sector exchange/mixing certificate. -/
theorem canonicalScalarTwoSectorExchangeCoupling_certificate
    (coefficient : Real) :
    (canonicalScalarTwoSectorMixingOperator (Hilbert := Hilbert)
      coefficient).toLinearMap.IsSymmetric ∧
      (canonicalScalarTwoSectorMixingOperator (Hilbert := Hilbert)
        coefficient).comp
          (canonicalScalarTwoSectorExchange (Hilbert := Hilbert)) =
        (canonicalScalarTwoSectorExchange (Hilbert := Hilbert)).comp
          (canonicalScalarTwoSectorMixingOperator (Hilbert := Hilbert)
            coefficient) ∧
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
