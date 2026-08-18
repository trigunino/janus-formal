import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D

/-!
# Bundled reduced and Green operators in a unitary frame

The pointwise transported maps of the preceding Green-frame construction are
linear and bounded.  This file packages them as continuous linear endomorphisms
of the moving canonical reduced fibres.

For every parameter `a` it constructs

```text
H_red,a : (ker H_a)ᗮ →L (ker H_a)ᗮ,
G_a     : (ker H_a)ᗮ →L (ker H_a)ᗮ,
```

proves that `H_red,a` is the genuine ambient `H_a` on the subtype, and proves
both continuous-linear-map inverse identities.  The Green operator norm is at
most the basepoint Green norm.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace FiniteUnitaryIntertwiningOperatorFrameData

/-- Genuine reduced operator bundled as a continuous linear endomorphism of the
current orthogonal kernel complement. -/
def transportedReducedOperatorCLM
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real) :
    (operator parameter).kerᗮ →L[Real] (operator parameter).kerᗮ := by
  let linear :
      (operator parameter).kerᗮ →ₗ[Real] (operator parameter).kerᗮ :=
    { toFun := frame.transportedReducedOperator basepoint parameter
      map_add' := by
        intro first second
        apply Subtype.ext
        simpa only [frame.transportedReducedOperator_apply_val basepoint,
          Submodule.coe_add] using
          map_add (operator parameter) first.1 second.1
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        simpa only [frame.transportedReducedOperator_apply_val basepoint,
          Submodule.coe_smul, RingHom.id_apply] using
          map_smul (operator parameter) scalar vector.1 }
  exact linear.mkContinuous ‖operator parameter‖ (by
    intro vector
    change ‖(frame.transportedReducedOperator basepoint parameter vector).1‖ ≤
      ‖operator parameter‖ * ‖vector.1‖
    rw [frame.transportedReducedOperator_apply_val]
    exact (operator parameter).le_opNorm vector.1)

/-- Transported Green bundled as a continuous linear endomorphism of the
current orthogonal kernel complement. -/
def transportedGreenCLM
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real) :
    (operator parameter).kerᗮ →L[Real] (operator parameter).kerᗮ := by
  let linear :
      (operator parameter).kerᗮ →ₗ[Real] (operator parameter).kerᗮ :=
    { toFun := frame.transportedGreen basepoint parameter
      map_add' := by
        intro first second
        apply Subtype.ext
        simp [transportedGreen]
      map_smul' := by
        intro scalar vector
        apply Subtype.ext
        simp [transportedGreen] }
  exact linear.mkContinuous ‖basepoint.green‖ (by
    intro vector
    exact frame.transportedGreen_norm_le basepoint parameter vector)

@[simp]
theorem transportedReducedOperatorCLM_apply
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    frame.transportedReducedOperatorCLM basepoint parameter vector =
      frame.transportedReducedOperator basepoint parameter vector :=
  rfl

@[simp]
theorem transportedGreenCLM_apply
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    frame.transportedGreenCLM basepoint parameter vector =
      frame.transportedGreen basepoint parameter vector :=
  rfl

/-- Ambient value of the bundled reduced operator. -/
theorem transportedReducedOperatorCLM_apply_val
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    (frame.transportedReducedOperatorCLM basepoint parameter vector).1 =
      operator parameter vector.1 :=
  frame.transportedReducedOperator_apply_val basepoint parameter vector

/-- Bundled reduced operator followed by bundled Green is identity. -/
theorem transportedReducedOperatorCLM_comp_greenCLM
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real) :
    (frame.transportedReducedOperatorCLM basepoint parameter).comp
        (frame.transportedGreenCLM basepoint parameter) =
      ContinuousLinearMap.id Real (operator parameter).kerᗮ := by
  apply ContinuousLinearMap.ext
  intro vector
  change frame.transportedReducedOperator basepoint parameter
      (frame.transportedGreen basepoint parameter vector) = vector
  exact frame.transportedReducedOperator_green basepoint parameter vector

/-- Bundled Green followed by bundled reduced operator is identity. -/
theorem transportedGreenCLM_comp_reducedOperatorCLM
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real) :
    (frame.transportedGreenCLM basepoint parameter).comp
        (frame.transportedReducedOperatorCLM basepoint parameter) =
      ContinuousLinearMap.id Real (operator parameter).kerᗮ := by
  apply ContinuousLinearMap.ext
  intro vector
  change frame.transportedGreen basepoint parameter
      (frame.transportedReducedOperator basepoint parameter vector) = vector
  exact frame.transportedGreen_reducedOperator basepoint parameter vector

/-- Operator norm of the transported Green is no larger than the basepoint
Green norm. -/
theorem norm_transportedGreenCLM_le
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real) :
    ‖frame.transportedGreenCLM basepoint parameter‖ ≤ ‖basepoint.green‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (norm_nonneg basepoint.green) ?_
  intro vector
  exact frame.transportedGreen_norm_le basepoint parameter vector

/-- Public bundled Green-family checkpoint. -/
theorem finite_unitary_kernel_complement_green_operator_gate
    (operator : Real → E →L[Real] E)
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator) :
    (∀ parameter vector,
      (frame.transportedReducedOperatorCLM basepoint parameter vector).1 =
        operator parameter vector.1) ∧
    (∀ parameter,
      (frame.transportedReducedOperatorCLM basepoint parameter).comp
          (frame.transportedGreenCLM basepoint parameter) =
        ContinuousLinearMap.id Real (operator parameter).kerᗮ) ∧
    (∀ parameter,
      (frame.transportedGreenCLM basepoint parameter).comp
          (frame.transportedReducedOperatorCLM basepoint parameter) =
        ContinuousLinearMap.id Real (operator parameter).kerᗮ) ∧
    (∀ parameter,
      ‖frame.transportedGreenCLM basepoint parameter‖ ≤ ‖basepoint.green‖) :=
  ⟨frame.transportedReducedOperatorCLM_apply_val basepoint,
    frame.transportedReducedOperatorCLM_comp_greenCLM basepoint,
    frame.transportedGreenCLM_comp_reducedOperatorCLM basepoint,
    frame.norm_transportedGreenCLM_le basepoint⟩

end FiniteUnitaryIntertwiningOperatorFrameData

end
end P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
end JanusFormal
