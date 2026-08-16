import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D

/-!
# Fixed-coordinate trivialization of reduced and Green families

The transported reduced and Green operators are defined by unitary conjugation.
Pulling them back by the same complement frame therefore removes all parameter
dependence exactly:

```text
F_a⁻¹ H_red,a F_a = H_red,0,
F_a⁻¹ G_a     F_a = G_0.
```

This is stronger than a C1 statement.  In the frame coordinates the two
families are constant, so their fixed-coordinate derivatives vanish.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenTrivialization4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

namespace FiniteUnitaryIntertwiningOperatorFrameData

/-- Reduced operator expressed in the fixed H12 complement coordinates. -/
def trivializedReducedOperator
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator 0).kerᗮ) : (operator 0).kerᗮ :=
  (frame.kernelComplementFrame parameter).symm
    (frame.transportedReducedOperator basepoint parameter
      (frame.kernelComplementFrame parameter vector))

/-- Green operator expressed in the fixed H12 complement coordinates. -/
def trivializedGreen
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator 0).kerᗮ) : (operator 0).kerᗮ :=
  (frame.kernelComplementFrame parameter).symm
    (frame.transportedGreen basepoint parameter
      (frame.kernelComplementFrame parameter vector))

/-- The reduced family is exactly constant in unitary frame coordinates. -/
theorem trivializedReducedOperator_eq_basepoint
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator 0).kerᗮ) :
    frame.trivializedReducedOperator basepoint parameter vector =
      basepoint.reducedOperator vector := by
  unfold trivializedReducedOperator transportedReducedOperator
  rw [(frame.kernelComplementFrame parameter).symm_apply_apply]
  rw [(frame.kernelComplementFrame parameter).symm_apply_apply]

/-- The Green family is exactly constant in unitary frame coordinates. -/
theorem trivializedGreen_eq_basepoint
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (parameter : Real)
    (vector : (operator 0).kerᗮ) :
    frame.trivializedGreen basepoint parameter vector =
      basepoint.green vector := by
  unfold trivializedGreen transportedGreen
  rw [(frame.kernelComplementFrame parameter).symm_apply_apply]
  rw [(frame.kernelComplementFrame parameter).symm_apply_apply]

/-- Fixed-coordinate reduced vectors form a differentiable constant family. -/
theorem trivializedReducedOperator_differentiable
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (vector : (operator 0).kerᗮ) :
    Differentiable Real
      (fun parameter : Real =>
        frame.trivializedReducedOperator basepoint parameter vector) := by
  convert differentiable_const (c := basepoint.reducedOperator vector) using 1
  funext parameter
  exact frame.trivializedReducedOperator_eq_basepoint basepoint parameter vector

/-- Fixed-coordinate Green vectors form a differentiable constant family. -/
theorem trivializedGreen_differentiable
    {operator : Real → E →L[Real] E}
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator)
    (vector : (operator 0).kerᗮ) :
    Differentiable Real
      (fun parameter : Real =>
        frame.trivializedGreen basepoint parameter vector) := by
  convert differentiable_const (c := basepoint.green vector) using 1
  funext parameter
  exact frame.trivializedGreen_eq_basepoint basepoint parameter vector

/-- Public fixed-coordinate Green trivialization checkpoint. -/
theorem finite_unitary_kernel_complement_green_trivialization_gate
    (operator : Real → E →L[Real] E)
    (frame : FiniteUnitaryIntertwiningOperatorFrameData operator)
    (basepoint : FiniteKernelComplementBasepointGreenData operator) :
    (∀ parameter vector,
      frame.trivializedReducedOperator basepoint parameter vector =
        basepoint.reducedOperator vector) ∧
    (∀ parameter vector,
      frame.trivializedGreen basepoint parameter vector =
        basepoint.green vector) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          frame.trivializedReducedOperator basepoint parameter vector)) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          frame.trivializedGreen basepoint parameter vector)) :=
  ⟨frame.trivializedReducedOperator_eq_basepoint basepoint,
    frame.trivializedGreen_eq_basepoint basepoint,
    frame.trivializedReducedOperator_differentiable basepoint,
    frame.trivializedGreen_differentiable basepoint⟩

end FiniteUnitaryIntertwiningOperatorFrameData

end
end P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenTrivialization4D
end JanusFormal