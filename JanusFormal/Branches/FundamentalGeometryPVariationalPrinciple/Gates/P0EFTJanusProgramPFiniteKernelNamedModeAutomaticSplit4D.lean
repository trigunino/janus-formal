import Mathlib.Analysis.InnerProductSpace.Projection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D

/-!
# Automatic orthogonal splitting of the named kernel span

The no-hidden-mode gate still exposed the orthogonal splitting of each kernel
vector.  For finitely many named modes this is not analytic input: their span
inside the Hilbert kernel is finite dimensional, hence complete, and therefore
has the canonical orthogonal projection.

This file constructs that projection and removes the splitting field.  The
remaining data are exactly the ambient zero modes, their independence and the
global Gårding inequality with finite named defect.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Named independent zero modes and one global Gårding inequality.  The
orthogonal decomposition and exact kernel spanning are both derived. -/
structure FiniteKernelNamedModeAutomaticSplitData
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  linearIndependent : LinearIndependent Real
    (finiteKernelNamedVector operator vector annihilated)
  constant : Real
  constant_pos : 0 < constant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  garding : ∀ current : E,
    constant * ‖current‖ ^ 2 ≤
      ⟪current, operator current, Real⟫ +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, vector mode, Real⟫ ^ 2

/-- The named span is finite dimensional. -/
local instance namedKernelSpanFiniteDimensional
    (operator : E →L[Real] E)
    {ZeroMode : Type*} [Fintype ZeroMode]
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0) :
    FiniteDimensional Real
      (finiteKernelNamedKernelSpan operator vector annihilated) := by
  unfold finiteKernelNamedKernelSpan
  exact FiniteDimensional.span_of_finite (Set.finite_range _)

/-- The canonical orthogonal projection supplies the splitting used by the
no-hidden-mode argument. -/
theorem FiniteKernelNamedModeAutomaticSplitData.kernel_split
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeAutomaticSplitData operator ZeroMode)
    (zeroMode : operator.ker) :
    ∃ projected :
        finiteKernelNamedKernelSpan operator data.vector data.annihilated,
      ∃ remainder :
        (finiteKernelNamedKernelSpan operator data.vector data.annihilated)ᗮ,
        zeroMode = projected.1 + remainder.1 := by
  let span :=
    finiteKernelNamedKernelSpan operator data.vector data.annihilated
  letI : FiniteDimensional Real span :=
    namedKernelSpanFiniteDimensional operator data.vector data.annihilated
  letI : CompleteSpace span := FiniteDimensional.complete Real span
  let projected : span := span.orthogonalProjection zeroMode
  let remainder : spanᗮ :=
    ⟨zeroMode - projected.1,
      span.sub_orthogonalProjection_mem_orthogonal zeroMode⟩
  refine ⟨projected, remainder, ?_⟩
  change zeroMode = projected.1 + (zeroMode - projected.1)
  abel

/-- Remove the explicit splitting field. -/
def FiniteKernelNamedModeAutomaticSplitData.toNoHidden
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeAutomaticSplitData operator ZeroMode) :
    FiniteKernelNamedModeNoHiddenData operator ZeroMode where
  vector := data.vector
  annihilated := data.annihilated
  linearIndependent := data.linearIndependent
  kernel_split := data.kernel_split
  constant := data.constant
  constant_pos := data.constant_pos
  defectConstant := data.defectConstant
  defectConstant_nonneg := data.defectConstant_nonneg
  garding := data.garding

/-- Public terminal reduction: independent named zero modes and a global
Gårding estimate are sufficient. -/
theorem finite_kernel_named_mode_automatic_split_gate
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeAutomaticSplitData operator ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  finite_kernel_named_mode_no_hidden_gate
    (hSelfAdjoint := hSelfAdjoint) data.toNoHidden

end
end P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
end JanusFormal
