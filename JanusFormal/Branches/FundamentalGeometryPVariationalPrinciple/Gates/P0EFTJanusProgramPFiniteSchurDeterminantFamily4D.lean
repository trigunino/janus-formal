import Mathlib.Topology.Instances.Matrix
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurDeterminant4D

/-!
# Continuous families of finite Schur determinants

For a continuous family of finite Schur operators, the determinant is a
continuous real function.  Its nonzero locus is therefore open.  Since
nonvanishing of the determinant is exactly the zero-mode-free condition, the
nondegenerate Hessian stratum is stable under sufficiently small parameter
variations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteSchurDeterminantFamily4D

set_option autoImplicit false
noncomputable section

open Set Filter Topology
open P0EFTJanusProgramPFiniteModeSchurDeterminant4D

variable {Parameter Mode : Type*}
  [TopologicalSpace Parameter]
  [Fintype Mode] [DecidableEq Mode]

/-- Continuous family of finite Schur operators in standard coordinates. -/
structure FiniteSchurDeterminantFamily where
  schur : Parameter → ((Mode → Real) →ₗ[Real] (Mode → Real))
  continuous_matrix : Continuous fun parameter =>
    LinearMap.toMatrix' (schur parameter)

/-- Finite Schur discriminant. -/
def FiniteSchurDeterminantFamily.determinant
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode))
    (parameter : Parameter) : Real :=
  (LinearMap.toMatrix' (family.schur parameter)).det

/-- Continuity of the finite Schur discriminant. -/
theorem FiniteSchurDeterminantFamily.continuous_determinant
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode)) :
    Continuous family.determinant := by
  exact family.continuous_matrix.matrix_det

/-- The zero-mode-free parameter locus. -/
def FiniteSchurDeterminantFamily.nondegenerateSet
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode)) : Set Parameter :=
  {parameter | family.determinant parameter ≠ 0}

/-- Nondegeneracy is an open condition. -/
theorem FiniteSchurDeterminantFamily.isOpen_nondegenerateSet
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode)) :
    IsOpen family.nondegenerateSet := by
  have hOpen : IsOpen (({0} : Set Real)ᶜ) := isClosed_singleton.isOpen_compl
  have hPreimage :
      family.nondegenerateSet =
        family.determinant ⁻¹' (({0} : Set Real)ᶜ) := by
    ext parameter
    simp [FiniteSchurDeterminantFamily.nondegenerateSet]
  rw [hPreimage]
  exact hOpen.preimage family.continuous_determinant

/-- A nondegenerate parameter has a whole neighborhood of nondegenerate
parameters. -/
theorem FiniteSchurDeterminantFamily.eventually_nondegenerate
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode))
    {parameter : Parameter}
    (hNondegenerate : parameter ∈ family.nondegenerateSet) :
    ∀ᶠ nearby in 𝓝 parameter,
      nearby ∈ family.nondegenerateSet :=
  family.isOpen_nondegenerateSet.mem_nhds hNondegenerate

/-- Equivalent neighborhood statement written directly as determinant
nonvanishing. -/
theorem FiniteSchurDeterminantFamily.eventually_determinant_ne_zero
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode))
    {parameter : Parameter}
    (hNondegenerate : family.determinant parameter ≠ 0) :
    ∀ᶠ nearby in 𝓝 parameter,
      family.determinant nearby ≠ 0 := by
  exact family.eventually_nondegenerate hNondegenerate

/-- The degeneracy locus is closed. -/
theorem FiniteSchurDeterminantFamily.isClosed_degenerateSet
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode)) :
    IsClosed {parameter | family.determinant parameter = 0} := by
  exact isClosed_singleton.preimage family.continuous_determinant

/-- Public stability checkpoint for the finite Schur discriminant. -/
theorem finite_schur_determinant_family_gate
    (family : FiniteSchurDeterminantFamily
      (Parameter := Parameter) (Mode := Mode)) :
    IsOpen family.nondegenerateSet ∧
      IsClosed {parameter | family.determinant parameter = 0} ∧
      (∀ parameter, family.determinant parameter ≠ 0 →
        ∀ᶠ nearby in 𝓝 parameter,
          family.determinant nearby ≠ 0) :=
  ⟨family.isOpen_nondegenerateSet,
    family.isClosed_degenerateSet,
    family.eventually_determinant_ne_zero⟩

end
end P0EFTJanusProgramPFiniteSchurDeterminantFamily4D
end JanusFormal
