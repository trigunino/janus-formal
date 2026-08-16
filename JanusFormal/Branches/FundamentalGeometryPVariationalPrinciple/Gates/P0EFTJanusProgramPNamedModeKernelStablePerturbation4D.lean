import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelOrthogonalNamedModeGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNamedModeGardingPerturbation4D

/-!
# Stability of the exact named kernel under a bounded perturbation

Suppose `H = A + K`.  If a finite orthogonal family is killed by both `A` and
`K`, the reference operator `A` has a global Gårding estimate modulo that
family, and `‖K‖` is smaller than the reference coercivity constant, then:

* the same vectors are zero modes of `H`;
* the perturbed Gårding estimate is positive on their orthogonal complement;
* no additional zero mode can appear;
* the kernel of `H` is exactly their span.

Thus kernel classification and coercivity are stable simultaneously, without
assuming the kernel of the perturbed operator in advance.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNamedModeKernelStablePerturbation4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPNamedModeGardingPerturbation4D
open P0EFTJanusProgramPFiniteKernelOrthogonalNamedModeGarding4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Reference zero modes preserved by a bounded perturbation. -/
structure FiniteKernelStableOrthogonalNamedModePerturbationData
    (reference perturbation : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  vector : ZeroMode → E
  reference_annihilated : ∀ mode, reference (vector mode) = 0
  perturbation_annihilated : ∀ mode, perturbation (vector mode) = 0
  nonzero : ∀ mode, vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    ⟪vector first, vector second, Real⟫ = 0
  referenceConstant : Real
  perturbation_small : ‖perturbation‖ < referenceConstant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  reference_garding : ∀ current : E,
    referenceConstant * ‖current‖ ^ 2 ≤
      ⟪current, reference current, Real⟫ +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, vector mode, Real⟫ ^ 2

/-- The displayed full operator. -/
def finiteKernelStablePerturbedOperator
    (reference perturbation : E →L[Real] E) : E →L[Real] E :=
  reference + perturbation

/-- Every reference mode remains a zero mode of the full operator. -/
theorem FiniteKernelStableOrthogonalNamedModePerturbationData.annihilated
    {reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelStableOrthogonalNamedModePerturbationData
      reference perturbation ZeroMode)
    (mode : ZeroMode) :
    finiteKernelStablePerturbedOperator reference perturbation
        (data.vector mode) = 0 := by
  simp [finiteKernelStablePerturbedOperator,
    data.reference_annihilated mode, data.perturbation_annihilated mode]

/-- The full operator inherits positive named-mode Gårding coercivity. -/
def FiniteKernelStableOrthogonalNamedModePerturbationData.toOrthogonalGarding
    {reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelStableOrthogonalNamedModePerturbationData
      reference perturbation ZeroMode) :
    FiniteKernelOrthogonalNamedModeGardingData
      (finiteKernelStablePerturbedOperator reference perturbation) ZeroMode where
  vector := data.vector
  annihilated := data.annihilated
  nonzero := data.nonzero
  orthogonal := data.orthogonal
  constant := data.referenceConstant - ‖perturbation‖
  constant_pos := sub_pos.mpr data.perturbation_small
  defectConstant := data.defectConstant
  defectConstant_nonneg := data.defectConstant_nonneg
  garding := by
    intro current
    have hReference := data.reference_garding current
    have hPerturbation :=
      perturbation_real_inner_lower_bound perturbation current
    unfold finiteKernelStablePerturbedOperator
    rw [ContinuousLinearMap.add_apply, inner_add_right]
    linarith

/-- The perturbed operator has exactly the preserved named modes as its kernel,
and inherits the actual-kernel gap. -/
theorem finite_kernel_stable_named_mode_perturbation_gate
    {reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (hSelfAdjoint : IsSelfAdjoint
      (finiteKernelStablePerturbedOperator reference perturbation))
    (data : FiniteKernelStableOrthogonalNamedModePerturbationData
      reference perturbation ZeroMode) :
    SelfAdjointKernelComplementGapData
        (finiteKernelStablePerturbedOperator reference perturbation)
        hSelfAdjoint ∧
      Module.finrank Real
          (finiteKernelStablePerturbedOperator reference perturbation).ker =
        Fintype.card ZeroMode :=
  finite_kernel_orthogonal_named_mode_garding_gate
    (hSelfAdjoint := hSelfAdjoint) data.toOrthogonalGarding

end
end P0EFTJanusProgramPNamedModeKernelStablePerturbation4D
end JanusFormal
