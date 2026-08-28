import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelNamedModes4D

/-!
# Synthesis operator of named physical zero modes

The named kernel family is upgraded here to an actual finite-rank synthesis
operator into the ambient Hilbert space.  Its image is proved to be exactly the
kernel of the displayed operator.  This gives downstream spectral and
finite-defect constructions a canonical map from physical zero-mode
coordinates, rather than only an abstract finite-dimensionality witness.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelNamedModeOperators4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteKernelModel4D
open P0EFTJanusProgramPFiniteKernelNamedModes4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
variable {operator : E →L[Real] E}
variable {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]

/-- Linear synthesis from finite physical coordinates into the ambient space. -/
def finiteKernelNamedModeSynthesisLinearMap
    (family : FiniteKernelNamedModeFamily operator ZeroMode) :
    (ZeroMode → Real) →ₗ[Real] E :=
  (Submodule.subtype operator.ker).comp family.coordinates.toLinearMap

@[simp]
theorem finiteKernelNamedModeSynthesisLinearMap_apply
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (coefficient : ZeroMode → Real) :
    finiteKernelNamedModeSynthesisLinearMap family coefficient =
      family.synthesize coefficient :=
  rfl

/-- Synthesis is injective because the coordinate equivalence and the kernel
inclusion are both injective. -/
theorem finiteKernelNamedModeSynthesisLinearMap_injective
    (family : FiniteKernelNamedModeFamily operator ZeroMode) :
    Function.Injective (finiteKernelNamedModeSynthesisLinearMap family) :=
  (Submodule.subtype operator.ker).injective.comp family.coordinates.injective

/-- The image of physical zero-mode synthesis is exactly the actual operator
kernel. -/
theorem finiteKernelNamedModeSynthesisLinearMap_range
    (family : FiniteKernelNamedModeFamily operator ZeroMode) :
    (finiteKernelNamedModeSynthesisLinearMap family).range = operator.ker := by
  apply le_antisymm
  · rintro vector ⟨coefficient, rfl⟩
    exact (family.coordinates coefficient).2
  · intro vector hVector
    let zeroMode : operator.ker := ⟨vector, hVector⟩
    refine ⟨family.coordinates.symm zeroMode, ?_⟩
    change (family.coordinates (family.coordinates.symm zeroMode)).1 = vector
    rw [family.coordinates.apply_symm_apply]

/-- Every actual zero mode has unique finite physical coordinates. -/
theorem finiteKernelNamedModeSynthesis_existsUnique
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (vector : E) (hVector : vector ∈ operator.ker) :
    ∃! coefficient : ZeroMode → Real,
      finiteKernelNamedModeSynthesisLinearMap family coefficient = vector := by
  let zeroMode : operator.ker := ⟨vector, hVector⟩
  refine ⟨family.coordinates.symm zeroMode, ?_, ?_⟩
  · change (family.coordinates (family.coordinates.symm zeroMode)).1 = vector
    rw [family.coordinates.apply_symm_apply]
  · intro coefficient hCoefficient
    apply finiteKernelNamedModeSynthesisLinearMap_injective family
    rw [hCoefficient]
    change vector =
      finiteKernelNamedModeSynthesisLinearMap family
        (family.coordinates.symm zeroMode)
    symm
    change (family.coordinates (family.coordinates.symm zeroMode)).1 = vector
    rw [family.coordinates.apply_symm_apply]

/-- The named synthesis map sends each coordinate axis to the corresponding
physical vector. -/
@[simp]
theorem finiteKernelNamedModeSynthesisLinearMap_coordinateUnit
    (family : FiniteKernelNamedModeFamily operator ZeroMode)
    (index : ZeroMode) :
    finiteKernelNamedModeSynthesisLinearMap family
        (finiteCoordinateUnit index) =
      family.vector index :=
  family.synthesize_coordinateUnit index

/-- The actual kernel is finite-dimensional for the explicit reason that it is
the image of the finite coordinate space. -/
theorem finiteKernelNamedModeSynthesis_range_finiteDimensional
    (family : FiniteKernelNamedModeFamily operator ZeroMode) :
    FiniteDimensional Real
      (finiteKernelNamedModeSynthesisLinearMap family).range := by
  rw [finiteKernelNamedModeSynthesisLinearMap_range family]
  exact family.toFiniteKernelModel.kernelFiniteDimensional

/-- Public exact-synthesis checkpoint. -/
theorem finite_kernel_named_mode_synthesis_gate
    (family : FiniteKernelNamedModeFamily operator ZeroMode) :
    Function.Injective (finiteKernelNamedModeSynthesisLinearMap family) ∧
      (finiteKernelNamedModeSynthesisLinearMap family).range = operator.ker ∧
      Module.finrank Real operator.ker = Fintype.card ZeroMode :=
  ⟨finiteKernelNamedModeSynthesisLinearMap_injective family,
    finiteKernelNamedModeSynthesisLinearMap_range family,
    family.kernel_finrank_eq_card⟩

end
end P0EFTJanusProgramPFiniteKernelNamedModeOperators4D
end JanusFormal
