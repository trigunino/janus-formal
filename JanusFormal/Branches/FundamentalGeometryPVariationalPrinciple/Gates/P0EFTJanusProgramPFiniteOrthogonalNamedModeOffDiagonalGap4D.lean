import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteNamedModeComplementExactCount4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalOperatorGarding4D

/-!
# Exact named kernel from one orthogonal off-diagonal sector estimate

Combine two independent structural reductions:

* nonzero pairwise orthogonal named vectors are linearly independent;
* a five-sector orthogonal-coordinate Gårding estimate on the complement of
  their ambient span gives a positive operator lower bound there.

The complement estimate proves that the named span is the complete actual
kernel.  Thus the finite-kernel hypothesis disappears from the H12 packet, the
kernel dimension is the number of named modes, and the same margin becomes the
canonical actual-kernel gap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteOrthogonalNamedModeOffDiagonalGap4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPFiniteNamedModeComplementGap4D
open P0EFTJanusProgramPFiniteNamedModeComplementExactCount4D
open P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOffDiagonalOperatorGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E]
  [InnerProductSpace Real E] [CompleteSpace E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Orthogonal named zero modes and the complete one-form sector estimate on
the complement of their span. -/
structure FiniteOrthogonalNamedModeOffDiagonalGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type*) [Fintype ZeroMode] where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  nonzero : ∀ mode, vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    inner Real (vector first) (vector second) = 0
  complementGarding :
    CandidateAFiveSectorOrthogonalOffDiagonalOperatorGardingData
      (Component := Component)
      (finiteNamedModeComplementOperator operator hSelfAdjoint vector
        annihilated)

namespace FiniteOrthogonalNamedModeOffDiagonalGapData

/-- Forget the sector construction after extracting its positive margin and
operator lower bound. -/
def toComplementGap
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteOrthogonalNamedModeOffDiagonalGapData
      (Component := Component) operator hSelfAdjoint ZeroMode) :
    FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode where
  vector := data.vector
  annihilated := data.annihilated
  gap := data.complementGarding.finiteMargin.margin Component
  gap_pos :=
    (data.complementGarding.finiteMargin
      |>.candidateA_five_sector_orthogonal_offDiagonal_physical_smallness_gate
        Component).1
  lowerBound := data.complementGarding.lowerBound Component

/-- Orthogonality supplies independence in the genuine kernel subtype. -/
theorem kernelLinearIndependent
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteOrthogonalNamedModeOffDiagonalGapData
      (Component := Component) operator hSelfAdjoint ZeroMode) :
    LinearIndependent Real
      (finiteKernelNamedVector operator data.vector data.annihilated) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro mode hZero
    exact data.nonzero mode (congrArg Subtype.val hZero)
  · intro first second hNe
    exact data.orthogonal hNe

/-- Actual kernel gap without a supplied finite-kernel premise. -/
def toActualKernelGap
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteOrthogonalNamedModeOffDiagonalGapData
      (Component := Component) operator hSelfAdjoint ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  (data.toComplementGap Component).toActualKernelGap

/-- Exact number of actual zero modes. -/
theorem kernel_finrank_eq_card
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteOrthogonalNamedModeOffDiagonalGapData
      (Component := Component) operator hSelfAdjoint ZeroMode) :
    Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  P0EFTJanusProgramPFiniteNamedModeComplementExactCount4D.FiniteNamedModeComplementGapData.kernel_finrank_eq_card
    (data.toComplementGap Component) (data.kernelLinearIndependent Component)

/-- Public strongest generic named-mode/off-diagonal checkpoint. -/
theorem finite_orthogonal_named_mode_offDiagonal_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteOrthogonalNamedModeOffDiagonalGapData
      (Component := Component) operator hSelfAdjoint ZeroMode) :
    operator.ker = finiteNamedModeAmbientSpan data.vector ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode ∧
      Nonempty (SelfAdjointKernelComplementGapData operator hSelfAdjoint) :=
  ⟨(data.toComplementGap Component).kernel_eq_namedSpan,
    data.kernel_finrank_eq_card Component,
    ⟨data.toActualKernelGap Component⟩⟩

end FiniteOrthogonalNamedModeOffDiagonalGapData

end
end P0EFTJanusProgramPFiniteOrthogonalNamedModeOffDiagonalGap4D
end JanusFormal
