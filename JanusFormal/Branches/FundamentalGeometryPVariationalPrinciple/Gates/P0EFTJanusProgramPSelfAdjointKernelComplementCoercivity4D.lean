import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModes4D

/-!
# From quadratic coercivity to the actual-kernel spectral gap

For PDE applications the natural estimate is usually a quadratic coercivity
bound on the orthogonal complement of the true zero modes,

`c * ||x||^2 <= <x, H x>`.

The H12 reduction, by contrast, consumes the norm estimate

`c * ||x|| <= ||H x||`.

For a real Hilbert space the second estimate follows immediately from the
first by Cauchy--Schwarz.  This file performs that conversion and therefore
lets the actual-kernel Green, resolvent, Fredholm and stability gates consume
the standard Gårding/coercivity conclusion directly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPSelfAdjointKernelComplementCoercivity4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPFiniteKernelModel4D
open P0EFTJanusProgramPFiniteKernelNamedModes4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Quadratic coercivity on the exact orthogonal complement of the actual
kernel, with an explicit finite family of named zero modes. -/
structure SelfAdjointKernelComplementCoercivityWithNamedModes
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode] where
  family : FiniteKernelNamedModeFamily operator ZeroMode
  coercivity : Real
  coercivity_pos : 0 < coercivity
  quadraticLowerBound : ∀ vector : SelfAdjointKernelComplement operator,
    coercivity * ‖vector‖ ^ 2 ≤
      inner Real (vector : E)
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector : E)

/-- Cauchy--Schwarz converts the quadratic estimate into the norm gap used by
all subsequent actual-kernel gates. -/
theorem SelfAdjointKernelComplementCoercivityWithNamedModes.lowerBound
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementCoercivityWithNamedModes operator
      hSelfAdjoint ZeroMode)
    (vector : SelfAdjointKernelComplement operator) :
    data.coercivity * ‖vector‖ ≤
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖ := by
  let image :=
    selfAdjointKernelComplementOperator operator hSelfAdjoint vector
  have hCauchy :
      |inner Real (vector : E) (image : E)| ≤ ‖vector‖ * ‖image‖ := by
    simpa [image] using
      (abs_real_inner_le_norm (vector : E) (image : E))
  have hProduct :
      data.coercivity * ‖vector‖ ^ 2 ≤ ‖vector‖ * ‖image‖ := by
    calc
      data.coercivity * ‖vector‖ ^ 2 ≤
          inner Real (vector : E) (image : E) := by
        simpa [image] using data.quadraticLowerBound vector
      _ ≤ |inner Real (vector : E) (image : E)| :=
        le_abs_self _
      _ ≤ ‖vector‖ * ‖image‖ := hCauchy
  by_cases hVector : ‖vector‖ = 0
  · simp [hVector]
  · have hVectorPos : 0 < ‖vector‖ :=
      lt_of_le_of_ne (norm_nonneg vector) (Ne.symm hVector)
    nlinarith

/-- The quadratic packet canonically supplies the named-mode gap packet. -/
def SelfAdjointKernelComplementCoercivityWithNamedModes.toGapWithNamedModes
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementCoercivityWithNamedModes operator
      hSelfAdjoint ZeroMode) :
    SelfAdjointKernelComplementGapWithNamedModes operator hSelfAdjoint
      ZeroMode where
  family := data.family
  gap := data.coercivity
  gap_pos := data.coercivity_pos
  lowerBound := data.lowerBound

/-- Compatibility conversion to the pre-existing anonymous finite-kernel gap
packet. -/
def SelfAdjointKernelComplementCoercivityWithNamedModes.toGapWithModel
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementCoercivityWithNamedModes operator
      hSelfAdjoint ZeroMode) :
    SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint :=
  data.toGapWithNamedModes.toGapWithModel

/-- Public PDE-to-spectral conversion checkpoint. -/
theorem selfAdjoint_named_kernel_coercivity_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementCoercivityWithNamedModes operator
      hSelfAdjoint ZeroMode) :
    Nonempty (SelfAdjointKernelComplementGapWithNamedModes operator hSelfAdjoint
        ZeroMode) ∧
      Nonempty (SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint) ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode := by
  exact ⟨⟨data.toGapWithNamedModes⟩,
    ⟨data.toGapWithModel⟩,
    data.family.kernel_finrank_eq_card⟩

end
end P0EFTJanusProgramPSelfAdjointKernelComplementCoercivity4D
end JanusFormal
