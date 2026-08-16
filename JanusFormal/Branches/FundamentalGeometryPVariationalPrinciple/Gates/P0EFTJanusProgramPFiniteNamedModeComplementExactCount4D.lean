import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteNamedModeComplementGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D

/-!
# Exact named-mode count from a complement gap

The named-span complement estimate already proves that the ambient span of the
selected modes is the genuine kernel.  If the selected family is linearly
independent, it is therefore a basis of the kernel and the kernel dimension is
exactly the number of named modes.

This file supplies the small algebraic bridge between the ambient span and the
span of the corresponding vectors in the kernel subtype.  No second Gårding
estimate or independently supplied spanning proof is used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteNamedModeComplementExactCount4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D
open P0EFTJanusProgramPFiniteNamedModeComplementGap4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- Mapping the span of the named kernel-subtype vectors to the ambient space
recovers the ambient named span. -/
theorem finiteKernelNamedKernelSpan_map_subtype
    (operator : E →L[Real] E)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0) :
    (finiteKernelNamedKernelSpan operator vector annihilated).map
        operator.ker.subtype =
      finiteNamedModeAmbientSpan vector := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    rw [finiteKernelNamedKernelSpan, Submodule.span_le]
    rintro named ⟨mode, rfl⟩
    change vector mode ∈ finiteNamedModeAmbientSpan vector
    exact Submodule.subset_span (Set.mem_range_self mode)
  · rw [finiteNamedModeAmbientSpan, Submodule.span_le]
    rintro current ⟨mode, rfl⟩
    refine ⟨finiteKernelNamedVector operator vector annihilated mode, ?_, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self mode)

/-- Linear independence plus the complement gap constructs the exact named
basis of the genuine kernel. -/
def FiniteNamedModeComplementGapData.toNamedSpanning
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode)
    (hIndependent : LinearIndependent Real
      (finiteKernelNamedVector operator data.vector data.annihilated)) :
    FiniteKernelNamedSpanningData operator ZeroMode where
  vector := data.vector
  annihilated := data.annihilated
  linearIndependent := hIndependent
  span_eq_top := by
    apply top_unique
    intro zeroMode _
    have hAmbient :
        (zeroMode.1 : E) ∈ finiteNamedModeAmbientSpan data.vector := by
      rw [← data.kernel_eq_namedSpan]
      exact zeroMode.property
    rw [← finiteKernelNamedKernelSpan_map_subtype operator data.vector
      data.annihilated] at hAmbient
    obtain ⟨named, hNamed, hValue⟩ := hAmbient
    have hEqual : named = zeroMode := Subtype.ext hValue
    rw [← hEqual]
    exact hNamed

/-- Exact zero-mode multiplicity. -/
theorem FiniteNamedModeComplementGapData.kernel_finrank_eq_card
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode)
    (hIndependent : LinearIndependent Real
      (finiteKernelNamedVector operator data.vector data.annihilated)) :
    Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  (data.toNamedSpanning hIndependent).kernel_finrank_eq_card

/-- Public exact-count checkpoint. -/
theorem finite_named_mode_complement_exact_count_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteNamedModeComplementGapData operator hSelfAdjoint ZeroMode)
    (hIndependent : LinearIndependent Real
      (finiteKernelNamedVector operator data.vector data.annihilated)) :
    operator.ker = finiteNamedModeAmbientSpan data.vector ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode ∧
      SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  ⟨data.kernel_eq_namedSpan,
    data.kernel_finrank_eq_card hIndependent,
    data.toActualKernelGap⟩

end
end P0EFTJanusProgramPFiniteNamedModeComplementExactCount4D
end JanusFormal
