import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D

/-!
# Orthogonal named zero modes and global Gårding coercivity

When physical zero modes arise from distinct symmetry sectors, their most
natural certificate is often pairwise orthogonality rather than a separate
linear-independence proof.  Nonzero pairwise orthogonal vectors are linearly
independent.  Combined with the canonical finite-span orthogonal projection and
the global Gårding estimate, this excludes hidden zero modes and constructs the
full actual-kernel basis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelOrthogonalNamedModeGarding4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
open P0EFTJanusProgramPFiniteKernelNamedModeAutomaticSplit4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Concrete orthogonal physical zero modes and one global Gårding estimate. -/
structure FiniteKernelOrthogonalNamedModeGardingData
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  nonzero : ∀ mode, vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    ⟪vector first, vector second⟫_Real = 0
  constant : Real
  constant_pos : 0 < constant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  garding : ∀ current : E,
    constant * ‖current‖ ^ 2 ≤
      ⟪current, operator current⟫_Real +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, vector mode⟫_Real ^ 2

/-- Orthogonality and nonvanishing imply independence in the genuine kernel
subtype. -/
theorem FiniteKernelOrthogonalNamedModeGardingData.linearIndependent
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelOrthogonalNamedModeGardingData operator ZeroMode) :
    LinearIndependent Real
      (finiteKernelNamedVector operator data.vector data.annihilated) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro mode hZero
    apply data.nonzero mode
    exact congrArg Subtype.val hZero
  · intro first second hNe
    exact data.orthogonal hNe

/-- Build the independent named-mode packet; orthogonal splitting and exact
kernel spanning are then derived by the preceding gate. -/
def FiniteKernelOrthogonalNamedModeGardingData.toAutomaticSplit
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelOrthogonalNamedModeGardingData operator ZeroMode) :
    FiniteKernelNamedModeAutomaticSplitData operator ZeroMode where
  vector := data.vector
  annihilated := data.annihilated
  linearIndependent := data.linearIndependent
  constant := data.constant
  constant_pos := data.constant_pos
  defectConstant := data.defectConstant
  defectConstant_nonneg := data.defectConstant_nonneg
  garding := data.garding

/-- Public orthogonal-mode checkpoint. -/
theorem finite_kernel_orthogonal_named_mode_garding_gate
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelOrthogonalNamedModeGardingData operator ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapData operator hSelfAdjoint) ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  finite_kernel_named_mode_automatic_split_gate
    (hSelfAdjoint := hSelfAdjoint) data.toAutomaticSplit

end
end P0EFTJanusProgramPFiniteKernelOrthogonalNamedModeGarding4D
end JanusFormal
