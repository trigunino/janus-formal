import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeGarding4D

/-!
# Stability of a named-mode Gårding estimate under bounded perturbations

The augmented Candidate-A Hessian is naturally viewed as a principal closed
BRST--SpinC--LL operator plus the bounded physical Hessian.  This file records
the elementary perturbative step needed by that decomposition.

If a reference self-adjoint operator has a global Gårding estimate modulo the
actual named zero modes and a bounded perturbation has norm strictly smaller
than the reference coercivity constant, then their sum has the same finite
named defect and coercivity constant reduced by the perturbation norm.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNamedModeGardingPerturbation4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- A reference Gårding estimate together with a bounded perturbative
realisation of the displayed operator.  The named modes span the kernel of the
full operator, not an auxiliary reference kernel. -/
structure FiniteKernelNamedReferenceGardingPerturbationData
    (operator reference perturbation : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] where
  spanning : FiniteKernelNamedSpanningData operator ZeroMode
  operator_eq : operator = reference + perturbation
  referenceConstant : Real
  perturbation_small : ‖perturbation‖ < referenceConstant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  reference_garding : ∀ vector : E,
    referenceConstant * ‖vector‖ ^ 2 ≤
      ⟪vector, reference vector⟫_Real +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪vector, spanning.vector mode⟫_Real ^ 2

/-- A bounded perturbation contributes at worst its operator norm times the
squared norm to the quadratic form. -/
theorem perturbation_real_inner_lower_bound
    (perturbation : E →L[Real] E)
    (vector : E) :
    -(‖perturbation‖ * ‖vector‖ ^ 2) ≤
      ⟪vector, perturbation vector⟫_Real := by
  have hAbs :
      |⟪vector, perturbation vector⟫_Real| ≤
        ‖perturbation‖ * ‖vector‖ ^ 2 := by
    calc
      |⟪vector, perturbation vector⟫_Real| ≤
          ‖vector‖ * ‖perturbation vector‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖vector‖ * (‖perturbation‖ * ‖vector‖) := by
        exact mul_le_mul_of_nonneg_left (perturbation.le_opNorm vector)
          (norm_nonneg vector)
      _ = ‖perturbation‖ * ‖vector‖ ^ 2 := by ring
  calc
    -(‖perturbation‖ * ‖vector‖ ^ 2) ≤
        -|⟪vector, perturbation vector⟫_Real| :=
      neg_le_neg hAbs
    _ ≤ ⟪vector, perturbation vector⟫_Real :=
      neg_abs_le _

/-- The full operator inherits a global Gårding estimate with reduced positive
constant and the same finite named defect. -/
def FiniteKernelNamedReferenceGardingPerturbationData.toNamedGarding
    {operator reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedReferenceGardingPerturbationData
      operator reference perturbation ZeroMode) :
    FiniteKernelNamedModeGardingData operator ZeroMode where
  spanning := data.spanning
  constant := data.referenceConstant - ‖perturbation‖
  constant_pos := sub_pos.mpr data.perturbation_small
  defectConstant := data.defectConstant
  defectConstant_nonneg := data.defectConstant_nonneg
  garding := by
    intro vector
    have hReference := data.reference_garding vector
    have hPerturbation :=
      perturbation_real_inner_lower_bound perturbation vector
    have hOperator :
        operator vector = reference vector + perturbation vector := by
      simpa only [ContinuousLinearMap.add_apply] using
        congrArg (fun current : E →L[Real] E => current vector) data.operator_eq
    rw [hOperator, inner_add_right]
    linarith

/-- Public bounded-perturbation checkpoint. -/
theorem named_mode_garding_bounded_perturbation_gate
    {operator reference perturbation : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedReferenceGardingPerturbationData
      operator reference perturbation ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapData operator hSelfAdjoint) ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  finite_kernel_named_mode_garding_gate
    (hSelfAdjoint := hSelfAdjoint) data.toNamedGarding

end
end P0EFTJanusProgramPNamedModeGardingPerturbation4D
end JanusFormal
