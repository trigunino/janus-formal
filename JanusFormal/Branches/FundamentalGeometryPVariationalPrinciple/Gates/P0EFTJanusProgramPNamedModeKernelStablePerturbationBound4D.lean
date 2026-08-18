import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNamedModeKernelStablePerturbation4D

/-!
# Stable named kernel from an explicit perturbation majorant

In applications the physical perturbation is usually controlled by an explicit
constant obtained from trace, multiplication and dense-core estimates.  One
should not have to prove the strict operator-norm inequality directly.

This file replaces `‖K‖ < c` by a scalar majorant `M` with

`‖K‖ ≤ M < c`.

All exact-kernel and Gårding conclusions are inherited from the preceding
stable-perturbation theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNamedModeKernelStablePerturbationBound4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPNamedModeKernelStablePerturbation4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Stable orthogonal named modes with an explicit upper bound for the bounded
perturbation. -/
structure FiniteKernelStableOrthogonalNamedModePerturbationBoundData
    (reference perturbation : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] where
  vector : ZeroMode → E
  reference_annihilated : ∀ mode, reference (vector mode) = 0
  perturbation_annihilated : ∀ mode, perturbation (vector mode) = 0
  nonzero : ∀ mode, vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    ⟪vector first, vector second⟫_Real = 0
  referenceConstant : Real
  perturbationBound : Real
  perturbationBound_nonneg : 0 ≤ perturbationBound
  perturbation_norm_le : ‖perturbation‖ ≤ perturbationBound
  perturbationBound_lt_reference : perturbationBound < referenceConstant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  reference_garding : ∀ current : E,
    referenceConstant * ‖current‖ ^ 2 ≤
      ⟪current, reference current⟫_Real +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, vector mode⟫_Real ^ 2

/-- Forget the majorant after deriving the strict operator-norm inequality. -/
def FiniteKernelStableOrthogonalNamedModePerturbationBoundData.toStable
    {reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelStableOrthogonalNamedModePerturbationBoundData
      reference perturbation ZeroMode) :
    FiniteKernelStableOrthogonalNamedModePerturbationData
      reference perturbation ZeroMode where
  vector := data.vector
  reference_annihilated := data.reference_annihilated
  perturbation_annihilated := data.perturbation_annihilated
  nonzero := data.nonzero
  orthogonal := data.orthogonal
  referenceConstant := data.referenceConstant
  perturbation_small :=
    lt_of_le_of_lt data.perturbation_norm_le
      data.perturbationBound_lt_reference
  defectConstant := data.defectConstant
  defectConstant_nonneg := data.defectConstant_nonneg
  reference_garding := data.reference_garding

/-- The inherited positive coercivity constant of the full operator. -/
def FiniteKernelStableOrthogonalNamedModePerturbationBoundData.fullConstant
    {reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelStableOrthogonalNamedModePerturbationBoundData
      reference perturbation ZeroMode) : Real :=
  data.referenceConstant - ‖perturbation‖

/-- The explicit majorant also gives a potentially weaker but fully explicit
positive lower bound `referenceConstant - perturbationBound`. -/
theorem FiniteKernelStableOrthogonalNamedModePerturbationBoundData.explicit_gap_pos
    {reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelStableOrthogonalNamedModePerturbationBoundData
      reference perturbation ZeroMode) :
    0 < data.referenceConstant - data.perturbationBound :=
  sub_pos.mpr data.perturbationBound_lt_reference

/-- Public majorant-based exact-kernel checkpoint. -/
theorem finite_kernel_stable_named_mode_perturbation_bound_gate
    {reference perturbation : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (hSelfAdjoint : IsSelfAdjoint
      (finiteKernelStablePerturbedOperator reference perturbation))
    (data : FiniteKernelStableOrthogonalNamedModePerturbationBoundData
      reference perturbation ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapData
        (finiteKernelStablePerturbedOperator reference perturbation)
        hSelfAdjoint) ∧
      Module.finrank Real
          (finiteKernelStablePerturbedOperator reference perturbation).ker =
        Fintype.card ZeroMode :=
  finite_kernel_stable_named_mode_perturbation_gate hSelfAdjoint data.toStable

end
end P0EFTJanusProgramPNamedModeKernelStablePerturbationBound4D
end JanusFormal
