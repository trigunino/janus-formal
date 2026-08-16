import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelBasisCoercivity4D

/-!
# Named kernel generators and a global Gårding estimate

The previous terminal packet accepted a basis of `ker H` and a coercivity
estimate already restricted to `(ker H)ᗮ`.  Elliptic analysis more naturally
produces two concrete statements:

* finitely many ambient vectors are annihilated by `H`, are linearly
  independent, and span the full kernel;
* a global Gårding inequality holds modulo the squared coefficients along
  those named vectors.

On `(ker H)ᗮ` every defect coefficient vanishes, so the global estimate becomes
the exact quadratic coercivity required by the actual-kernel Green theorem.
This file performs that reduction without introducing a projector,
parametrix, quotient or auxiliary zero-mode space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModeGarding4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPSelfAdjointKernelBasisCoercivity4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- One named ambient zero mode, regarded in the genuine kernel subtype. -/
def finiteKernelNamedVector
    (operator : E →L[Real] E)
    {ZeroMode : Type*}
    (vector : ZeroMode → E)
    (annihilated : ∀ mode, operator (vector mode) = 0)
    (mode : ZeroMode) : operator.ker :=
  ⟨vector mode, LinearMap.mem_ker.mpr (annihilated mode)⟩

/-- Concrete generation data for the actual kernel.  No coordinate
isomorphism is supplied: it is reconstructed from independence and spanning. -/
structure FiniteKernelNamedSpanningData
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] where
  vector : ZeroMode → E
  annihilated : ∀ mode, operator (vector mode) = 0
  linearIndependent : LinearIndependent Real
    (finiteKernelNamedVector operator vector annihilated)
  span_eq_top : Submodule.span Real
    (Set.range (finiteKernelNamedVector operator vector annihilated)) = ⊤

/-- The named spanning family canonically determines a basis of the genuine
kernel. -/
noncomputable def FiniteKernelNamedSpanningData.toBasis
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedSpanningData operator ZeroMode) :
    Module.Basis ZeroMode Real operator.ker :=
  Module.Basis.mk data.linearIndependent (by
    rw [data.span_eq_top])

/-- The actual kernel is finite dimensional because it has the displayed
finite named basis. -/
def FiniteKernelNamedSpanningData.kernelFinite
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedSpanningData operator ZeroMode) :
    FiniteDimensional Real operator.ker :=
  data.toBasis.finiteDimensional_of_finite

/-- Exact zero-mode count attached to the concrete named spanning family. -/
theorem FiniteKernelNamedSpanningData.kernel_finrank_eq_card
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedSpanningData operator ZeroMode) :
    Module.finrank Real operator.ker = Fintype.card ZeroMode := by
  letI : FiniteDimensional Real operator.ker := data.kernelFinite
  exact Module.finrank_eq_card_basis data.toBasis

/-- A global Gårding inequality whose finite-dimensional defect is written
explicitly in the named zero-mode coefficients. -/
structure FiniteKernelNamedModeGardingData
    (operator : E →L[Real] E)
    (ZeroMode : Type*) [Fintype ZeroMode] where
  spanning : FiniteKernelNamedSpanningData operator ZeroMode
  constant : Real
  constant_pos : 0 < constant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  garding : ∀ vector : E,
    constant * ‖vector‖ ^ 2 ≤
      ⟪vector, operator vector⟫_Real +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪vector, spanning.vector mode⟫_Real ^ 2

/-- Every named defect coefficient vanishes on the orthogonal complement of
the actual kernel. -/
theorem FiniteKernelNamedModeGardingData.inner_named_eq_zero
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeGardingData operator ZeroMode)
    (vector : SelfAdjointKernelComplement operator)
    (mode : ZeroMode) :
    ⟪(vector : E), data.spanning.vector mode⟫_Real = 0 := by
  have hKernel : data.spanning.vector mode ∈ operator.ker :=
    LinearMap.mem_ker.mpr (data.spanning.annihilated mode)
  have hOrthogonal := vector.property
  rw [Submodule.mem_orthogonal'] at hOrthogonal
  exact hOrthogonal (data.spanning.vector mode) hKernel

/-- The global Gårding estimate restricts to genuine coercivity on
`(ker H)ᗮ`. -/
theorem FiniteKernelNamedModeGardingData.coercive
    {operator : E →L[Real] E}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeGardingData operator ZeroMode)
    (vector : SelfAdjointKernelComplement operator) :
    data.constant * ‖(vector : E)‖ ^ 2 ≤
      ⟪(vector : E), operator (vector : E)⟫_Real := by
  simpa [data.inner_named_eq_zero vector] using data.garding (vector : E)

/-- Convert the concrete named-mode Gårding packet to the basis/coercivity
packet consumed by the existing actual-kernel reduction. -/
def FiniteKernelNamedModeGardingData.toBasisCoercivity
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeGardingData operator ZeroMode) :
    SelfAdjointKernelBasisCoercivityData operator hSelfAdjoint ZeroMode where
  basis := data.spanning.toBasis
  constant := data.constant
  constant_pos := data.constant_pos
  coercive := data.coercive

/-- Direct conversion to the norm-gap packet used by the Fredholm, Green and
resolvent gates. -/
def FiniteKernelNamedModeGardingData.toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeGardingData operator ZeroMode) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  (data.toBasisCoercivity
    (hSelfAdjoint := hSelfAdjoint)).toGapData

/-- Public checkpoint: named ambient modes plus one global Gårding inequality
produce the actual-kernel gap and the exact zero-mode count. -/
theorem finite_kernel_named_mode_garding_gate
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (data : FiniteKernelNamedModeGardingData operator ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapData operator hSelfAdjoint) ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  ⟨⟨data.toGapData (hSelfAdjoint := hSelfAdjoint)⟩,
    data.spanning.kernel_finrank_eq_card⟩

end
end P0EFTJanusProgramPFiniteKernelNamedModeGarding4D
end JanusFormal
