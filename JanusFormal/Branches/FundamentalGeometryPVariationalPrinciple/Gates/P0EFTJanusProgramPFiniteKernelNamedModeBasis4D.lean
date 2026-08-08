import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementCoercivity4D

/-!
# Named zero-mode data from an actual finite basis of the kernel

A physical classification is often obtained by writing down a finite basis of
solutions of the linearized equations.  Such a basis already contains all the
coordinate information required by `FiniteKernelNamedModeFamily`.

This file converts a basis of the true kernel into the named-mode packet using
`Basis.equivFun`.  It also packages the common PDE input consisting of that
basis and a quadratic coercivity estimate on its orthogonal complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModeBasis4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPFiniteKernelNamedModes4D
open P0EFTJanusProgramPSelfAdjointKernelComplementCoercivity4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
variable {operator : E →L[Real] E}
variable {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]

/-- The named physical family canonically associated with a finite basis of the
actual kernel. -/
def finiteKernelNamedModeFamilyOfBasis
    (basis : Basis ZeroMode Real operator.ker) :
    FiniteKernelNamedModeFamily operator ZeroMode where
  vector := fun index => (basis index).1
  vector_mem_kernel := fun index => (basis index).2
  coordinates := basis.equivFun.symm
  coordinates_unit := by
    intro index
    have hBasis :
        basis.equivFun.symm (finiteCoordinateUnit index) = basis index := by
      apply basis.equivFun.injective
      simp [finiteCoordinateUnit]
    exact congrArg Subtype.val hBasis

/-- Coordinate synthesis from the constructed family is the inverse basis
coordinate map. -/
@[simp]
theorem finiteKernelNamedModeFamilyOfBasis_synthesize
    (basis : Basis ZeroMode Real operator.ker)
    (coefficient : ZeroMode → Real) :
    (finiteKernelNamedModeFamilyOfBasis basis).synthesize coefficient =
      (basis.equivFun.symm coefficient).1 :=
  rfl

/-- Each named vector is the corresponding basis vector in the ambient space. -/
@[simp]
theorem finiteKernelNamedModeFamilyOfBasis_vector
    (basis : Basis ZeroMode Real operator.ker)
    (index : ZeroMode) :
    (finiteKernelNamedModeFamilyOfBasis basis).vector index = (basis index).1 :=
  rfl

/-- The basis cardinality is the exact kernel dimension. -/
theorem finiteKernelNamedModeFamilyOfBasis_finrank
    (basis : Basis ZeroMode Real operator.ker) :
    Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  (finiteKernelNamedModeFamilyOfBasis basis).kernel_finrank_eq_card

section Coercivity

variable [InnerProductSpace Real E] [CompleteSpace E]

/-- The minimal PDE packet: an actual finite basis of zero modes and a
quadratic coercivity estimate on the true kernel complement. -/
structure SelfAdjointKernelComplementCoercivityWithBasis
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode] : Prop where
  basis : Basis ZeroMode Real operator.ker
  coercivity : Real
  coercivity_pos : 0 < coercivity
  quadraticLowerBound : ∀ vector : SelfAdjointKernelComplement operator,
    coercivity * ‖vector‖ ^ 2 ≤
      inner Real (vector : E)
        (selfAdjointKernelComplementOperator operator hSelfAdjoint vector : E)

/-- Convert the basis-level PDE packet into the named-mode coercivity packet. -/
def SelfAdjointKernelComplementCoercivityWithBasis.toNamedModes
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementCoercivityWithBasis operator hSelfAdjoint
      ZeroMode) :
    SelfAdjointKernelComplementCoercivityWithNamedModes operator hSelfAdjoint
      ZeroMode where
  family := finiteKernelNamedModeFamilyOfBasis data.basis
  coercivity := data.coercivity
  coercivity_pos := data.coercivity_pos
  quadraticLowerBound := data.quadraticLowerBound

/-- Direct conversion from a physical kernel basis and quadratic coercivity to
the existing actual-kernel gap packet. -/
def SelfAdjointKernelComplementCoercivityWithBasis.toGapWithModel
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementCoercivityWithBasis operator hSelfAdjoint
      ZeroMode) :=
  data.toNamedModes.toGapWithModel

/-- Public finite-basis coercivity checkpoint. -/
theorem selfAdjoint_kernel_basis_coercivity_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (ZeroMode : Type*) [Fintype ZeroMode] [DecidableEq ZeroMode]
    (data : SelfAdjointKernelComplementCoercivityWithBasis operator hSelfAdjoint
      ZeroMode) :
    SelfAdjointKernelComplementCoercivityWithNamedModes operator hSelfAdjoint
        ZeroMode ∧
      SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode := by
  exact ⟨data.toNamedModes,
    data.toGapWithModel,
    finiteKernelNamedModeFamilyOfBasis_finrank data.basis⟩

end Coercivity

end
end P0EFTJanusProgramPFiniteKernelNamedModeBasis4D
end JanusFormal
