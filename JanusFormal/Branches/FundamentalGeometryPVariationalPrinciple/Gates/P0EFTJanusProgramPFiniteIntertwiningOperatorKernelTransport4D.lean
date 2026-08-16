import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Restrict an intertwining ambient transport to actual kernels

Let `H_a` be a family of continuous linear operators on one fixed real normed
space.  A coherent family of ambient linear equivalences `U_ab` satisfying

`H_b U_ab = U_ab H_a`

maps `ker H_a` isomorphically onto `ker H_b`.  This file constructs the
restricted kernel equivalences and transports the identity/composition laws.

This is the exact algebraic bridge from a linearized D11 pullback or geometric
state transport to the sector-preserving finite-kernel transport used by the
Candidate-A determinant line.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D

set_option autoImplicit false
noncomputable section

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Coherent ambient linear transport intertwining an operator family. -/
structure FiniteIntertwiningOperatorTransportData
    (operator : Real → E →L[Real] E) where
  transport : ∀ first second, E ≃ₗ[Real] E
  transport_self : ∀ parameter,
    transport parameter parameter = LinearEquiv.refl Real E
  transport_trans : ∀ first second third,
    (transport first second).trans (transport second third) =
      transport first third
  intertwines : ∀ first second vector,
    operator second (transport first second vector) =
      transport first second (operator first vector)

namespace FiniteIntertwiningOperatorTransportData

/-- Restriction of the ambient intertwiner to the true kernels. -/
def kernelTransport
    {operator : Real → E →L[Real] E}
    (data : FiniteIntertwiningOperatorTransportData operator)
    (first second : Real) :
    (operator first).ker ≃ₗ[Real] (operator second).ker where
  toFun := fun vector =>
    ⟨data.transport first second vector.1, by
      change operator second (data.transport first second vector.1) = 0
      rw [data.intertwines first second vector.1]
      calc
        data.transport first second (operator first vector.1) =
            data.transport first second 0 :=
          congrArg (data.transport first second) vector.2
        _ = 0 := map_zero (data.transport first second)⟩
  invFun := fun vector =>
    ⟨(data.transport first second).symm vector.1, by
      change operator first ((data.transport first second).symm vector.1) = 0
      have hIntertwine := data.intertwines first second
        ((data.transport first second).symm vector.1)
      rw [(data.transport first second).apply_symm_apply] at hIntertwine
      apply (data.transport first second).injective
      exact (hIntertwine.symm.trans vector.2).trans
        (map_zero (data.transport first second)).symm⟩
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

@[simp]
theorem kernelTransport_apply_val
    {operator : Real → E →L[Real] E}
    (data : FiniteIntertwiningOperatorTransportData operator)
    (first second : Real) (vector : (operator first).ker) :
    (data.kernelTransport first second vector).1 =
      data.transport first second vector.1 :=
  rfl

/-- Identity transport descends to the kernel family. -/
theorem kernelTransport_self
    {operator : Real → E →L[Real] E}
    (data : FiniteIntertwiningOperatorTransportData operator)
    (parameter : Real) :
    data.kernelTransport parameter parameter = LinearEquiv.refl Real _ := by
  apply LinearEquiv.ext
  intro vector
  apply Subtype.ext
  rw [kernelTransport_apply_val, data.transport_self parameter]
  rfl

/-- Composition of ambient transports descends exactly to composition of the
restricted kernel transports. -/
theorem kernelTransport_trans
    {operator : Real → E →L[Real] E}
    (data : FiniteIntertwiningOperatorTransportData operator)
    (first second third : Real) :
    (data.kernelTransport first second).trans
        (data.kernelTransport second third) =
      data.kernelTransport first third := by
  apply LinearEquiv.ext
  intro vector
  apply Subtype.ext
  simp only [LinearEquiv.trans_apply, kernelTransport_apply_val]
  have hTrans := congrArg (fun equivalence => equivalence vector.1)
    (data.transport_trans first second third)
  exact hTrans

/-- The restricted transport still intertwines the zero equations by
construction. -/
theorem kernelTransport_mem_kernel
    {operator : Real → E →L[Real] E}
    (data : FiniteIntertwiningOperatorTransportData operator)
    (first second : Real) (vector : (operator first).ker) :
    operator second (data.kernelTransport first second vector).1 = 0 :=
  (data.kernelTransport first second vector).2

/-- Public ambient-to-kernel transport checkpoint. -/
theorem finite_intertwining_operator_kernel_transport_gate
    (operator : Real → E →L[Real] E)
    (data : FiniteIntertwiningOperatorTransportData operator) :
    (∀ first second vector,
      operator second (data.transport first second vector) =
        data.transport first second (operator first vector)) ∧
    (∀ first second vector,
      operator second (data.kernelTransport first second vector).1 = 0) ∧
    (∀ parameter,
      data.kernelTransport parameter parameter = LinearEquiv.refl Real _) ∧
    (∀ first second third,
      (data.kernelTransport first second).trans
          (data.kernelTransport second third) =
        data.kernelTransport first third) :=
  ⟨data.intertwines,
    data.kernelTransport_mem_kernel,
    data.kernelTransport_self,
    data.kernelTransport_trans⟩

end FiniteIntertwiningOperatorTransportData

end
end P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D
end JanusFormal
