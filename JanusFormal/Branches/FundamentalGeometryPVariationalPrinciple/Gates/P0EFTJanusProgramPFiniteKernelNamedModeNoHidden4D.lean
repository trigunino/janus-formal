import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeGarding4D

/-!
# Excluding hidden zero modes by coercivity

A list of physically named zero modes should not also have to carry the
statement that it already spans the full kernel.  In a Hilbert space the
kernel splits orthogonally into the span of the named modes and its orthogonal
complement.  If the global named-mode Gårding estimate is coercive on that
complement, a hidden kernel vector in the complement must vanish.

This file formalizes that argument.  The exact equality between the named span
and `ker H`, the finite kernel basis and the zero-mode count are derived from
independence, the standard orthogonal splitting and the Gårding inequality.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Span of the named vectors inside the genuine kernel subtype. -/
def finiteKernelNamedKernelSpan
    (operator : E →L[Real] E)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0) :
    Submodule Real operator.ker :=
  Submodule.span Real
    (Set.range (finiteKernelNamedVector operator vector annihilated))

/-- Named zero modes, their independence, the orthogonal splitting of every
kernel vector, and one global Gårding estimate.  No spanning assertion is
stored. -/
structure FiniteKernelNamedModeNoHiddenData
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  linearIndependent : LinearIndependent Real
    (finiteKernelNamedVector operator vector annihilated)
  kernel_split : ∀ zeroMode : operator.ker,
    ∃ projected : finiteKernelNamedKernelSpan operator vector annihilated,
      ∃ remainder :
        (finiteKernelNamedKernelSpan operator vector annihilated)ᗮ,
        zeroMode = projected.1 + remainder.1
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

/-- A remainder orthogonal to the named kernel span is orthogonal to every
named ambient zero mode. -/
theorem FiniteKernelNamedModeNoHiddenData.remainder_inner_named_eq_zero
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeNoHiddenData operator ZeroMode)
    (remainder :
      (finiteKernelNamedKernelSpan operator data.vector data.annihilated)ᗮ)
    (mode : ZeroMode) :
    ⟪((remainder.1 : operator.ker) : E), data.vector mode, Real⟫ = 0 := by
  have hNamed :
      finiteKernelNamedVector operator data.vector data.annihilated mode ∈
        finiteKernelNamedKernelSpan operator data.vector data.annihilated :=
    Submodule.subset_span (Set.mem_range_self _)
  exact (Submodule.mem_orthogonal'.mp remainder.property)
    (finiteKernelNamedVector operator data.vector data.annihilated mode) hNamed

/-- The Gårding inequality kills every kernel vector orthogonal to the named
span. -/
theorem FiniteKernelNamedModeNoHiddenData.remainder_eq_zero
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeNoHiddenData operator ZeroMode)
    (remainder :
      (finiteKernelNamedKernelSpan operator data.vector data.annihilated)ᗮ) :
    remainder = 0 := by
  let ambient : E := ((remainder.1 : operator.ker) : E)
  have hKernel : operator ambient = 0 :=
    LinearMap.mem_ker.mp remainder.1.property
  have hEstimate := data.garding ambient
  have hDefect :
      (∑ mode : ZeroMode,
        ⟪ambient, data.vector mode, Real⟫ ^ 2) = 0 := by
    simp [ambient, data.remainder_inner_named_eq_zero remainder]
  rw [hKernel, inner_zero_right, hDefect, mul_zero, add_zero] at hEstimate
  have hNorm : ‖ambient‖ = 0 := by
    nlinarith [data.constant_pos, norm_nonneg ambient]
  apply Subtype.ext
  apply Subtype.ext
  exact norm_eq_zero.mp hNorm

/-- Coercivity excludes hidden zero modes, so the named family spans the full
kernel. -/
theorem FiniteKernelNamedModeNoHiddenData.span_eq_top
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeNoHiddenData operator ZeroMode) :
    finiteKernelNamedKernelSpan operator data.vector data.annihilated = ⊤ := by
  apply top_unique
  intro zeroMode _
  obtain ⟨projected, remainder, hSplit⟩ := data.kernel_split zeroMode
  have hRemainder : remainder = 0 := data.remainder_eq_zero remainder
  have hZeroMode : zeroMode = projected.1 := by
    simpa [hRemainder] using hSplit
  rw [hZeroMode]
  exact projected.property

/-- Build the earlier named spanning Gårding packet without a supplied
`span = ker` proof. -/
def FiniteKernelNamedModeNoHiddenData.toNamedGarding
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeNoHiddenData operator ZeroMode) :
    FiniteKernelNamedModeGardingData operator ZeroMode where
  spanning :=
    { vector := data.vector
      annihilated := data.annihilated
      linearIndependent := data.linearIndependent
      span_eq_top := data.span_eq_top }
  constant := data.constant
  constant_pos := data.constant_pos
  defectConstant := data.defectConstant
  defectConstant_nonneg := data.defectConstant_nonneg
  garding := data.garding

/-- Public no-hidden-mode checkpoint. -/
theorem finite_kernel_named_mode_no_hidden_gate
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeNoHiddenData operator ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  finite_kernel_named_mode_garding_gate
    (hSelfAdjoint := hSelfAdjoint) data.toNamedGarding

end
end P0EFTJanusProgramPFiniteKernelNamedModeNoHidden4D
end JanusFormal
