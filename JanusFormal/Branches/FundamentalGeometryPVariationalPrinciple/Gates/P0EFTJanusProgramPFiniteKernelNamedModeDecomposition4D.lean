import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeGarding4D

/-!
# Named kernel spanning from explicit coefficient decompositions

For concrete zero modes it is often easier to prove an expansion formula than
a submodule equality.  This file replaces the field

`span namedModes = ker H`

by the statement that every element of the kernel has an explicit finite
coefficient family in the named ambient vectors.  The span equality and the
canonical kernel basis are then reconstructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModeDecomposition4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Ambient named zero modes with independence and an explicit decomposition
of every genuine kernel vector. -/
structure FiniteKernelNamedDecompositionData
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  linearIndependent : LinearIndependent Real
    (finiteKernelNamedVector operator vector annihilated)
  decompose : ∀ zeroMode : operator.ker,
    ∃ coefficients : ZeroMode → Real,
      zeroMode =
        ∑ mode : ZeroMode,
          coefficients mode •
            finiteKernelNamedVector operator vector annihilated mode

/-- The explicit decomposition formula implies the required span equality. -/
def FiniteKernelNamedDecompositionData.toSpanning
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedDecompositionData operator ZeroMode) :
    FiniteKernelNamedSpanningData operator ZeroMode where
  vector := data.vector
  annihilated := data.annihilated
  linearIndependent := data.linearIndependent
  span_eq_top := by
    apply top_unique
    intro zeroMode _
    obtain ⟨coefficients, hDecompose⟩ := data.decompose zeroMode
    rw [hDecompose]
    exact Finset.sum_mem fun mode _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span
          (Set.mem_range_self
            (finiteKernelNamedVector operator data.vector data.annihilated
              mode)))

/-- A global Gårding packet whose kernel-spanning part is given by explicit
coefficient decompositions. -/
structure FiniteKernelNamedDecompositionGardingData
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  decomposition : FiniteKernelNamedDecompositionData operator ZeroMode
  constant : Real
  constant_pos : 0 < constant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  garding : ∀ vector : E,
    constant * ‖vector‖ ^ 2 ≤
      ⟪vector, operator vector, Real⟫ +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪vector, decomposition.vector mode, Real⟫ ^ 2

/-- Convert the explicit-decomposition form to the named spanning Gårding
packet. -/
def FiniteKernelNamedDecompositionGardingData.toNamedGarding
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedDecompositionGardingData operator ZeroMode) :
    FiniteKernelNamedModeGardingData operator ZeroMode where
  spanning := data.decomposition.toSpanning
  constant := data.constant
  constant_pos := data.constant_pos
  defectConstant := data.defectConstant
  defectConstant_nonneg := data.defectConstant_nonneg
  garding := data.garding

/-- Public explicit-decomposition checkpoint. -/
theorem finite_kernel_named_decomposition_garding_gate
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedDecompositionGardingData operator ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  finite_kernel_named_mode_garding_gate
    (hSelfAdjoint := hSelfAdjoint) data.toNamedGarding

end
end P0EFTJanusProgramPFiniteKernelNamedModeDecomposition4D
end JanusFormal
