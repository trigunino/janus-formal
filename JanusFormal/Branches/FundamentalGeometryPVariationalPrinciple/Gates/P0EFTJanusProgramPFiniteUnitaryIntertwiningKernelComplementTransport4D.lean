import Mathlib.Analysis.InnerProductSpace.Orthogonal
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D

/-!
# Unitary intertwining transport of kernels and their orthogonal complements

A linear equivalence intertwining two operators transports their kernels.  To
transport the canonical reduced spaces `(ker H)ᗮ` without introducing a second
completion, the ambient equivalence must also preserve the Hilbert product.

This file records the exact generic statement.  A coherent family of linear
isometric equivalences `U_ab` satisfying

`H_b U_ab = U_ab H_a`

restricts simultaneously to

* a linear isometric equivalence `ker H_a ≃ ker H_b`;
* a linear isometric equivalence `(ker H_a)ᗮ ≃ (ker H_b)ᗮ`.

Identity and cocycle laws descend exactly to both restrictions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteUnitaryIntertwiningKernelComplementTransport4D

set_option autoImplicit false
noncomputable section

open Set
open scoped InnerProductSpace

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Coherent unitary ambient transport intertwining an operator family. -/
structure FiniteUnitaryIntertwiningOperatorTransportData
    (operator : Real → E →L[Real] E) where
  transport : ∀ first second, E ≃ₗᵢ[Real] E
  transport_self : ∀ parameter,
    transport parameter parameter = LinearIsometryEquiv.refl Real E
  transport_trans : ∀ first second third,
    (transport first second).trans (transport second third) =
      transport first third
  intertwines : ∀ first second vector,
    operator second (transport first second vector) =
      transport first second (operator first vector)

namespace FiniteUnitaryIntertwiningOperatorTransportData

/-- Forgetting metric preservation recovers the ordinary ambient intertwining
transport. -/
def toFiniteIntertwiningOperatorTransport
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator) :
    P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D.FiniteIntertwiningOperatorTransportData
      operator where
  transport := fun first second =>
    (data.transport first second).toLinearEquiv
  transport_self := by
    intro parameter
    rw [data.transport_self parameter]
    rfl
  transport_trans := by
    intro first second third
    ext vector
    have hTransport := congrArg
      (fun equivalence => equivalence vector)
      (data.transport_trans first second third)
    simpa using hTransport
  intertwines := data.intertwines

/-- The inverse unitary transport intertwines in the reverse direction. -/
theorem symm_intertwines
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) (vector : E) :
    operator first ((data.transport first second).symm vector) =
      (data.transport first second).symm (operator second vector) := by
  apply (data.transport first second).injective
  rw [(data.transport first second).apply_symm_apply]
  have hIntertwine := data.intertwines first second
    ((data.transport first second).symm vector)
  rw [(data.transport first second).apply_symm_apply] at hIntertwine
  exact hIntertwine.symm

/-- Unitary transport preserves membership in the true kernel. -/
theorem transport_mem_kernel
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) {vector : E}
    (hVector : vector ∈ (operator first).ker) :
    data.transport first second vector ∈ (operator second).ker := by
  apply LinearMap.mem_ker.mpr
  change operator second (data.transport first second vector) = 0
  have hZero : operator first vector = 0 := by
    exact LinearMap.mem_ker.mp hVector
  calc
    operator second (data.transport first second vector) =
        data.transport first second (operator first vector) :=
      data.intertwines first second vector
    _ = data.transport first second 0 := by
      rw [hZero]
    _ = 0 := map_zero (data.transport first second)

/-- Inverse unitary transport preserves kernel membership. -/
theorem symm_transport_mem_kernel
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) {vector : E}
    (hVector : vector ∈ (operator second).ker) :
    (data.transport first second).symm vector ∈ (operator first).ker := by
  apply LinearMap.mem_ker.mpr
  change operator first ((data.transport first second).symm vector) = 0
  have hZero : operator second vector = 0 := by
    exact LinearMap.mem_ker.mp hVector
  calc
    operator first ((data.transport first second).symm vector) =
        (data.transport first second).symm (operator second vector) :=
      data.symm_intertwines first second vector
    _ = (data.transport first second).symm 0 := by
      rw [hZero]
    _ = 0 := map_zero (data.transport first second).symm

/-- Unitary transport preserves the orthogonal complement of the true kernel. -/
theorem transport_mem_kernel_orthogonal
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) {vector : E}
    (hVector : vector ∈ (operator first).kerᗮ) :
    data.transport first second vector ∈ (operator second).kerᗮ := by
  rw [Submodule.mem_orthogonal'] at hVector ⊢
  intro target hTarget
  let source : E := (data.transport first second).symm target
  have hSource : source ∈ (operator first).ker :=
    data.symm_transport_mem_kernel first second hTarget
  have hTargetEq : data.transport first second source = target := by
    exact (data.transport first second).apply_symm_apply target
  rw [← hTargetEq]
  rw [(data.transport first second).inner_map_map]
  exact hVector source hSource

/-- Inverse unitary transport preserves the orthogonal kernel complement. -/
theorem symm_transport_mem_kernel_orthogonal
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) {vector : E}
    (hVector : vector ∈ (operator second).kerᗮ) :
    (data.transport first second).symm vector ∈ (operator first).kerᗮ := by
  rw [Submodule.mem_orthogonal'] at hVector ⊢
  intro source hSource
  have hTarget : data.transport first second source ∈ (operator second).ker :=
    data.transport_mem_kernel first second hSource
  rw [← (data.transport first second).inner_map_map]
  rw [(data.transport first second).apply_symm_apply]
  exact hVector (data.transport first second source) hTarget

/-- Restriction of the unitary ambient transport to the true kernels. -/
def kernelTransport
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) :
    (operator first).ker ≃ₗᵢ[Real] (operator second).ker where
  toFun := fun vector =>
    ⟨data.transport first second vector.1,
      data.transport_mem_kernel first second vector.2⟩
  invFun := fun vector =>
    ⟨(data.transport first second).symm vector.1,
      data.symm_transport_mem_kernel first second vector.2⟩
  left_inv := by
    intro vector
    apply Subtype.ext
    exact (data.transport first second).symm_apply_apply vector.1
  right_inv := by
    intro vector
    apply Subtype.ext
    exact (data.transport first second).apply_symm_apply vector.1
  map_add' := by
    intro firstVector secondVector
    apply Subtype.ext
    exact map_add (data.transport first second) firstVector.1 secondVector.1
  map_smul' := by
    intro scalar vector
    apply Subtype.ext
    exact map_smul (data.transport first second) scalar vector.1
  norm_map' := by
    intro vector
    exact (data.transport first second).norm_map vector.1

/-- Restriction of the unitary ambient transport to the canonical orthogonal
kernel complements. -/
def kernelComplementTransport
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) :
    (operator first).kerᗮ ≃ₗᵢ[Real] (operator second).kerᗮ where
  toFun := fun vector =>
    ⟨data.transport first second vector.1,
      data.transport_mem_kernel_orthogonal first second vector.2⟩
  invFun := fun vector =>
    ⟨(data.transport first second).symm vector.1,
      data.symm_transport_mem_kernel_orthogonal first second vector.2⟩
  left_inv := by
    intro vector
    apply Subtype.ext
    exact (data.transport first second).symm_apply_apply vector.1
  right_inv := by
    intro vector
    apply Subtype.ext
    exact (data.transport first second).apply_symm_apply vector.1
  map_add' := by
    intro firstVector secondVector
    apply Subtype.ext
    exact map_add (data.transport first second) firstVector.1 secondVector.1
  map_smul' := by
    intro scalar vector
    apply Subtype.ext
    exact map_smul (data.transport first second) scalar vector.1
  norm_map' := by
    intro vector
    exact (data.transport first second).norm_map vector.1

@[simp]
theorem kernelTransport_apply_val
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) (vector : (operator first).ker) :
    (data.kernelTransport first second vector).1 =
      data.transport first second vector.1 :=
  rfl

@[simp]
theorem kernelComplementTransport_apply_val
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second : Real) (vector : (operator first).kerᗮ) :
    (data.kernelComplementTransport first second vector).1 =
      data.transport first second vector.1 :=
  rfl

/-- Identity descends to the restricted kernel transport. -/
theorem kernelTransport_self
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (parameter : Real) :
    data.kernelTransport parameter parameter =
      LinearIsometryEquiv.refl Real _ := by
  ext vector
  rw [kernelTransport_apply_val, data.transport_self parameter]
  rfl

/-- Identity descends to the orthogonal-complement transport. -/
theorem kernelComplementTransport_self
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (parameter : Real) :
    data.kernelComplementTransport parameter parameter =
      LinearIsometryEquiv.refl Real _ := by
  ext vector
  rw [kernelComplementTransport_apply_val, data.transport_self parameter]
  rfl

/-- Cocycle law on the true kernels. -/
theorem kernelTransport_trans
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second third : Real) :
    (data.kernelTransport first second).trans
        (data.kernelTransport second third) =
      data.kernelTransport first third := by
  ext vector
  simp only [LinearIsometryEquiv.trans_apply, kernelTransport_apply_val]
  have hTransport := congrArg
    (fun equivalence => equivalence vector.1)
    (data.transport_trans first second third)
  exact hTransport

/-- Cocycle law on the orthogonal kernel complements. -/
theorem kernelComplementTransport_trans
    {operator : Real → E →L[Real] E}
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator)
    (first second third : Real) :
    (data.kernelComplementTransport first second).trans
        (data.kernelComplementTransport second third) =
      data.kernelComplementTransport first third := by
  ext vector
  simp only [LinearIsometryEquiv.trans_apply,
    kernelComplementTransport_apply_val]
  have hTransport := congrArg
    (fun equivalence => equivalence vector.1)
    (data.transport_trans first second third)
  exact hTransport

/-- Public unitary kernel/complement transport checkpoint. -/
theorem finite_unitary_intertwining_kernel_complement_transport_gate
    (operator : Real → E →L[Real] E)
    (data : FiniteUnitaryIntertwiningOperatorTransportData operator) :
    (∀ first second vector,
      operator second (data.transport first second vector) =
        data.transport first second (operator first vector)) ∧
    (∀ first second vector,
      ‖data.kernelTransport first second vector‖ = ‖vector‖) ∧
    (∀ first second vector,
      ‖data.kernelComplementTransport first second vector‖ = ‖vector‖) ∧
    (∀ parameter,
      data.kernelComplementTransport parameter parameter =
        LinearIsometryEquiv.refl Real _) ∧
    (∀ first second third,
      (data.kernelComplementTransport first second).trans
          (data.kernelComplementTransport second third) =
        data.kernelComplementTransport first third) :=
  ⟨data.intertwines,
    fun first second vector =>
      (data.kernelTransport first second).norm_map vector,
    fun first second vector =>
      (data.kernelComplementTransport first second).norm_map vector,
    data.kernelComplementTransport_self,
    data.kernelComplementTransport_trans⟩

end FiniteUnitaryIntertwiningOperatorTransportData

end
end P0EFTJanusProgramPFiniteUnitaryIntertwiningKernelComplementTransport4D
end JanusFormal
