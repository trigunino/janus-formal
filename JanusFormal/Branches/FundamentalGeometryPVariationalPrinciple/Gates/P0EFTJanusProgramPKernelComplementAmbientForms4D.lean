import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Ambient bilinear forms on the actual kernel complement

The H12 space `(ker H)ᗮ` is a closed subspace of the original Candidate-A
Hilbert space.  Principal and physical Hessian forms therefore restrict to it
by the canonical inclusion; no second completion and no smoothing map back to
the dense core are required.

This file records the generic restriction once and proves the two estimates
used downstream:

* the ambient bilinear-form norm controls the restricted quadratic energy;
* the quadratic energy of the reduced actual operator is bounded above by
  `‖x‖ ‖H_red x‖`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPKernelComplementAmbientForms4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Canonical continuous inclusion of the true zero-mode complement into the
ambient Hilbert space. -/
def selfAdjointKernelComplementInclusion
    (operator : E →L[Real] E) :
    SelfAdjointKernelComplement operator →L[Real] E := by
  let linear : SelfAdjointKernelComplement operator →ₗ[Real] E :=
    { toFun := fun vector => vector.1
      map_add' := by intro first second; rfl
      map_smul' := by intro scalar vector; rfl }
  exact linear.mkContinuous 1 (by
    intro vector
    change ‖vector.1‖ ≤ 1 * ‖vector.1‖
    simp)

@[simp]
theorem selfAdjointKernelComplementInclusion_apply
    (operator : E →L[Real] E)
    (vector : SelfAdjointKernelComplement operator) :
    selfAdjointKernelComplementInclusion operator vector = vector.1 :=
  rfl

/-- Restrict an ambient continuous bilinear form to `(ker H)ᗮ` in both
arguments. -/
def restrictBilinearToKernelComplement
    (operator : E →L[Real] E)
    (form : E →L[Real] E →L[Real] Real) :
    SelfAdjointKernelComplement operator →L[Real]
      SelfAdjointKernelComplement operator →L[Real] Real :=
  form.bilinearComp
    (selfAdjointKernelComplementInclusion operator)
    (selfAdjointKernelComplementInclusion operator)

@[simp]
theorem restrictBilinearToKernelComplement_apply
    (operator : E →L[Real] E)
    (form : E →L[Real] E →L[Real] Real)
    (first second : SelfAdjointKernelComplement operator) :
    restrictBilinearToKernelComplement operator form first second =
      form first.1 second.1 :=
  rfl

/-- Symmetry of an ambient form descends without an additional hypothesis on
the reduced space. -/
theorem restrictBilinearToKernelComplement_symmetric
    (operator : E →L[Real] E)
    (form : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second, form first second = form second first)
    (first second : SelfAdjointKernelComplement operator) :
    restrictBilinearToKernelComplement operator form first second =
      restrictBilinearToKernelComplement operator form second first :=
  hSymmetric first.1 second.1

/-- The original ambient form norm controls every restricted quadratic value. -/
theorem restrictBilinearToKernelComplement_quadratic_bound
    (operator : E →L[Real] E)
    (form : E →L[Real] E →L[Real] Real)
    (vector : SelfAdjointKernelComplement operator) :
    |restrictBilinearToKernelComplement operator form vector vector| ≤
      ‖form‖ * ‖vector‖ ^ 2 := by
  change |form vector.1 vector.1| ≤ ‖form‖ * ‖vector.1‖ ^ 2
  calc
    |form vector.1 vector.1| = ‖form vector.1 vector.1‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ‖form vector.1‖ * ‖vector.1‖ :=
      (form vector.1).le_opNorm vector.1
    _ ≤ (‖form‖ * ‖vector.1‖) * ‖vector.1‖ :=
      mul_le_mul_of_nonneg_right (form.le_opNorm vector.1)
        (norm_nonneg vector.1)
    _ = ‖form‖ * ‖vector.1‖ ^ 2 := by ring

/-- Bilinear form obtained by pairing an ambient bounded operator with two
vectors from the true kernel complement.  The operator need not preserve the
complement. -/
def ambientOperatorFormOnKernelComplement
    (kernelOperator ambientOperator : E →L[Real] E) :
    SelfAdjointKernelComplement kernelOperator →L[Real]
      SelfAdjointKernelComplement kernelOperator →L[Real] Real :=
  (innerSL Real).bilinearComp
    (selfAdjointKernelComplementInclusion kernelOperator)
    (ambientOperator.comp
      (selfAdjointKernelComplementInclusion kernelOperator))

@[simp]
theorem ambientOperatorFormOnKernelComplement_apply
    (kernelOperator ambientOperator : E →L[Real] E)
    (first second : SelfAdjointKernelComplement kernelOperator) :
    ambientOperatorFormOnKernelComplement kernelOperator ambientOperator
        first second =
      inner Real first.1 (ambientOperator second.1) :=
  rfl

/-- The usual energy upper bound for the actual reduced operator. -/
theorem selfAdjointKernelComplement_energy_upper
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (vector : SelfAdjointKernelComplement operator) :
    inner Real vector
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector) ≤
      ‖vector‖ *
        ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ := by
  calc
    inner Real vector
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector) ≤
      |inner Real vector
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector)| :=
      le_abs_self _
    _ = ‖inner Real vector
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ‖vector‖ *
        ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ :=
      norm_inner_le_norm (𝕜 := Real) vector
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector)

/-- Public restriction checkpoint. -/
theorem kernel_complement_ambient_forms_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (form : E →L[Real] E →L[Real] Real)
    (vector : SelfAdjointKernelComplement operator) :
    |restrictBilinearToKernelComplement operator form vector vector| ≤
        ‖form‖ * ‖vector‖ ^ 2 ∧
      inner Real vector
          (selfAdjointKernelComplementOperator operator hSelfAdjoint vector) ≤
        ‖vector‖ *
          ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ :=
  ⟨restrictBilinearToKernelComplement_quadratic_bound operator form vector,
    selfAdjointKernelComplement_energy_upper operator hSelfAdjoint vector⟩

end
end P0EFTJanusProgramPKernelComplementAmbientForms4D
end JanusFormal
