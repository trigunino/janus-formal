import Mathlib.Analysis.SpecialFunctions.Log.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphMaslovIntersection4D

/-!
# Fredholm determinant interface for infinite-dimensional scalar boundaries

For the physical throat L2 space, the finite-dimensional determinant is not
available.  A trace-class/Fredholm regularization must instead be proved
analytically.  This file records the exact interface such a construction must
satisfy.

A regularized determinant is required to vanish exactly when the boundary Schur
operator has nontrivial kernel.  Consequently its zero set is exactly the set of
nonzero homogeneous Robin bulk modes, or equivalently nontrivial intersections
of the Cauchy and Robin Lagrangians.  The logarithmic one-loop action is defined
away from those crossings.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryFredholmDeterminant4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
open P0EFTJanusMappingTorusScalarGraphMaslovIntersection4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Regularized Fredholm determinant for a boundary Schur family.  Analyticity,
trace-class hypotheses and normalization are all explicit data of the future
construction. -/
structure CanonicalScalarGraphBoundaryFredholmDeterminantData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace) where
  determinant : ∀ spectralParameter : Real,
    spectralParameter ∈ parameters → Real
  zero_iff_kernel : ∀ spectralParameter : Real,
    ∀ hParameter : spectralParameter ∈ parameters,
      determinant spectralParameter hParameter = 0 ↔
        LinearMap.ker
          (family.schur robin spectralParameter hParameter).toLinearMap ≠ ⊥
  continuousOn : ContinuousOn
    (fun spectralParameter : parameters =>
      determinant spectralParameter.1 spectralParameter.2) Set.univ
  normalizationParameter : Real
  normalization_mem : normalizationParameter ∈ parameters
  normalization_ne_zero :
    determinant normalizationParameter normalization_mem ≠ 0

namespace CanonicalScalarGraphBoundaryFredholmDeterminantData

/-- Regular parameter for the Fredholm determinant. -/
def Regular
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) : Prop :=
  determinantData.determinant spectralParameter hParameter ≠ 0

/-- Singular parameter. -/
def Singular
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) : Prop :=
  determinantData.determinant spectralParameter hParameter = 0

/-- Regularized one-loop boundary action, undefined at singular parameters. -/
noncomputable def oneLoop
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Option Real :=
  if hRegular : determinantData.Regular spectralParameter hParameter then
    some ((1 / 2 : Real) * Real.log
      |determinantData.determinant spectralParameter hParameter|)
  else none

/-- Singularity is exactly nontrivial Schur kernel. -/
theorem singular_iff_schurKernel
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    determinantData.Singular spectralParameter hParameter ↔
      LinearMap.ker
        (family.schur robin spectralParameter hParameter).toLinearMap ≠ ⊥ :=
  determinantData.zero_iff_kernel spectralParameter hParameter

/-- Singularity is exactly existence of a nonzero homogeneous Robin bulk mode. -/
theorem singular_iff_bulkMode
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    determinantData.Singular spectralParameter hParameter ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  rw [determinantData.singular_iff_schurKernel,
    Submodule.ne_bot_iff]
  exact (canonicalScalarGraphRobin_hasNonzeroSolution_iff_schurKernel
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter) robin).symm

/-- Singularity is exactly a nontrivial Cauchy/Robin Lagrangian intersection. -/
theorem singular_iff_lagrangianIntersection
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    determinantData.Singular spectralParameter hParameter ↔
      canonicalScalarGraphCauchyRobinIntersection
        data traceBound spectralParameter
          (family.poissonData spectralParameter hParameter) robin ≠ ⊥ := by
  rw [determinantData.singular_iff_bulkMode]
  exact (canonicalScalarGraphCauchyRobinIntersection_ne_bot_iff_bulkMode
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter) robin).symm

/-- The one-loop action is defined exactly at regular parameters. -/
theorem oneLoop_isSome_iff
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    (determinantData.oneLoop spectralParameter hParameter).isSome ↔
      determinantData.Regular spectralParameter hParameter := by
  unfold oneLoop
  split_ifs with hRegular
  · simp [hRegular]
  · simp [hRegular]

/-- The one-loop action is undefined exactly when a nonzero bulk mode appears. -/
theorem oneLoop_eq_none_iff_bulkMode
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    determinantData.oneLoop spectralParameter hParameter = none ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  unfold oneLoop Regular
  split_ifs with hRegular
  · simp [hRegular]
  · simp [hRegular, determinantData.singular_iff_bulkMode
      spectralParameter hParameter]

/-- Value of the one-loop action at a regular point. -/
theorem oneLoop_eq_some
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (hRegular : determinantData.Regular spectralParameter hParameter) :
    determinantData.oneLoop spectralParameter hParameter =
      some ((1 / 2 : Real) * Real.log
        |determinantData.determinant spectralParameter hParameter|) := by
  unfold oneLoop
  split_ifs with h
  · rfl
  · exact False.elim (h hRegular)

/-- The normalization point is regular. -/
theorem normalization_regular
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin) :
    determinantData.Regular determinantData.normalizationParameter
      determinantData.normalization_mem :=
  determinantData.normalization_ne_zero

/-- Fredholm determinant closure certificate. -/
theorem certificate
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin) :
    (∀ spectralParameter : Real,
      ∀ hParameter : spectralParameter ∈ parameters,
        determinantData.Singular spectralParameter hParameter ↔
          ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
            data traceBound spectralParameter robin, field ≠ 0) ∧
      (∀ spectralParameter : Real,
        ∀ hParameter : spectralParameter ∈ parameters,
          determinantData.oneLoop spectralParameter hParameter = none ↔
            ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
              data traceBound spectralParameter robin, field ≠ 0) :=
  ⟨determinantData.singular_iff_bulkMode,
    determinantData.oneLoop_eq_none_iff_bulkMode⟩

end CanonicalScalarGraphBoundaryFredholmDeterminantData

end
end P0EFTJanusMappingTorusScalarGraphBoundaryFredholmDeterminant4D
end JanusFormal
