import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

/-!
# Transport a reduced Green operator through a unitary frame

Let a unitary frame `F_a` intertwine `H_0` and `H_a`.  If the basepoint
operator preserves `(ker H_0)ᗮ` and has a bounded two-sided Green operator
`G_0` there, define

```text
H_red,a = F_a H_red,0 F_a⁻¹,
G_a     = F_a G_0     F_a⁻¹.
```

The transported reduced operator is exactly the restriction of the genuine
ambient operator `H_a`, the transported Green is its two-sided inverse, and the
pointwise Green norm bound is unchanged by the unitary conjugation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteUnitaryIntertwiningKernelComplementTransport4D
open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- A bounded two-sided Green operator for the basepoint restriction to the
orthogonal kernel complement. -/
structure FiniteKernelComplementBasepointGreenData
    (operator : Real → E →L[Real] E) where
  operator_mem_complement : ∀
    vector : (operator 0).kerᗮ,
      operator 0 vector.1 ∈ (operator 0).kerᗮ
  green : (operator 0).kerᗮ →L[Real] (operator 0).kerᗮ
  operator_green : ∀ vector : (operator 0).kerᗮ,
    operator 0 (green vector).1 = vector.1
  green_operator : ∀ vector : (operator 0).kerᗮ,
    green ⟨operator 0 vector.1, operator_mem_complement vector⟩ = vector

namespace FiniteKernelComplementBasepointGreenData

/-- Basepoint reduced operator as an unbundled map on the canonical reduced
fibre. -/
def reducedOperator
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData operator)
    (vector : (operator 0).kerᗮ) : (operator 0).kerᗮ :=
  ⟨operator 0 vector.1, data.operator_mem_complement vector⟩

@[simp]
theorem reducedOperator_apply_val
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData operator)
    (vector : (operator 0).kerᗮ) :
    (data.reducedOperator vector).1 = operator 0 vector.1 :=
  rfl

/-- Basepoint reduced operator followed by the Green operator is identity. -/
theorem reducedOperator_green
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData operator)
    (vector : (operator 0).kerᗮ) :
    data.reducedOperator (data.green vector) = vector := by
  apply Subtype.ext
  exact data.operator_green vector

/-- Green followed by the basepoint reduced operator is identity. -/
theorem green_reducedOperator
    {operator : Real → E →L[Real] E}
    (data : FiniteKernelComplementBasepointGreenData operator)
    (vector : (operator 0).kerᗮ) :
    data.green (data.reducedOperator vector) = vector :=
  data.green_operator vector

end FiniteKernelComplementBasepointGreenData

namespace FiniteUnitaryIntertwiningOperatorFrameData

/-- Reduced operator at one parameter obtained by unitary conjugation from the
basepoint reduced operator. -/
def transportedReducedOperator
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    (operator parameter).kerᗮ :=
  frame.kernelComplementFrame parameter
    (basepoint.reducedOperator
      ((frame.kernelComplementFrame parameter).symm vector))

/-- Green operator at one parameter obtained by the same unitary conjugation. -/
def transportedGreen
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    (operator parameter).kerᗮ :=
  frame.kernelComplementFrame parameter
    (basepoint.green
      ((frame.kernelComplementFrame parameter).symm vector))

@[simp]
theorem kernelComplementFrame_symm_apply_val
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    ((frame.kernelComplementFrame parameter).symm vector).1 =
      (frame.frame parameter).symm vector.1 :=
  rfl

/-- The conjugated reduced operator is the genuine ambient operator restricted
to the current canonical reduced fibre. -/
theorem transportedReducedOperator_apply_val
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    (frame.transportedReducedOperator basepoint parameter vector).1 =
      operator parameter vector.1 := by
  change frame.frame parameter
      (operator 0 ((frame.frame parameter).symm vector.1)) =
    operator parameter vector.1
  rw [← frame.intertwines_basepoint parameter
    ((frame.frame parameter).symm vector.1)]
  rw [(frame.frame parameter).apply_symm_apply]

/-- The transported reduced operator is a left inverse of the transported
Green operator. -/
theorem transportedReducedOperator_green
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    frame.transportedReducedOperator basepoint parameter
        (frame.transportedGreen basepoint parameter vector) =
      vector := by
  apply Subtype.ext
  change frame.frame parameter
      (operator 0
        (basepoint.green
          ((frame.kernelComplementFrame parameter).symm vector)).1) =
    vector.1
  rw [basepoint.operator_green]
  exact (frame.frame parameter).apply_symm_apply vector.1

/-- The transported Green operator is a left inverse of the transported reduced
operator. -/
theorem transportedGreen_reducedOperator
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    frame.transportedGreen basepoint parameter
        (frame.transportedReducedOperator basepoint parameter vector) =
      vector := by
  apply Subtype.ext
  change frame.frame parameter
      (basepoint.green
        (basepoint.reducedOperator
          ((frame.kernelComplementFrame parameter).symm vector))).1 =
    vector.1
  rw [basepoint.green_reducedOperator]
  exact (frame.frame parameter).apply_symm_apply vector.1

/-- The pointwise Green bound is transported without loss. -/
theorem transportedGreen_norm_le
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator parameter).kerᗮ) :
    ‖frame.transportedGreen basepoint parameter vector‖ ≤
      ‖basepoint.green‖ * ‖vector‖ := by
  change
    ‖frame.kernelComplementFrame parameter
      (basepoint.green
        ((frame.kernelComplementFrame parameter).symm vector))‖ ≤
      ‖basepoint.green‖ * ‖vector‖
  rw [(frame.kernelComplementFrame parameter).norm_map]
  calc
    ‖basepoint.green
        ((frame.kernelComplementFrame parameter).symm vector)‖ ≤
        ‖basepoint.green‖ *
          ‖(frame.kernelComplementFrame parameter).symm vector‖ :=
      basepoint.green.le_opNorm _
    _ = ‖basepoint.green‖ * ‖vector‖ := by
      rw [(frame.kernelComplementFrame parameter).symm.norm_map]

/-- Public transported-Green checkpoint. -/
theorem finite_unitary_kernel_complement_green_frame_gate
    (operator : Real → E →L[Real] E)
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator) :
    (∀ parameter vector,
      (frame.transportedReducedOperator basepoint parameter vector).1 =
        operator parameter vector.1) ∧
    (∀ parameter vector,
      frame.transportedReducedOperator basepoint parameter
          (frame.transportedGreen basepoint parameter vector) = vector) ∧
    (∀ parameter vector,
      frame.transportedGreen basepoint parameter
          (frame.transportedReducedOperator basepoint parameter vector) = vector) ∧
    (∀ parameter vector,
      ‖frame.transportedGreen basepoint parameter vector‖ ≤
        ‖basepoint.green‖ * ‖vector‖) :=
  ⟨frame.transportedReducedOperator_apply_val basepoint,
    frame.transportedReducedOperator_green basepoint,
    frame.transportedGreen_reducedOperator basepoint,
    frame.transportedGreen_norm_le basepoint⟩

end FiniteUnitaryIntertwiningOperatorFrameData

end
end P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D
end JanusFormal