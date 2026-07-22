import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

/-!
# Density of every completed Lagrangian domain

The zero-Cauchy minimal smooth core lies in every linear boundary condition,
because every boundary submodule contains zero.  Therefore density of the
minimal ambient inclusion implies density of the ambient inclusion of every
completed Lagrangian realization.

This removes domain density as a separate analytic assumption for Dirichlet,
Neumann, Robin and arbitrary closed Lagrangian boundary conditions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable
  {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Smooth zero-Cauchy core embedded in any completed Lagrangian domain. -/
def minimalCoreToLagrangianDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    minimalDomainSubmodule core →ₗ[Real]
      triple.lagrangianDomainSubmodule condition where
  toFun test :=
    ⟨canonicalScalarGreenCoreToGraph core test.1, by
      change canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound
          (canonicalScalarGreenCoreToGraph core test.1) ∈ condition.subspace
      rw [canonicalScalarGreenCoreCompletedBoundaryTrace_smooth]
      have hZero : core.boundaryTrace test.1 = 0 :=
        LinearMap.mem_ker.mp test.2
      rw [hZero]
      exact condition.subspace.zero_mem⟩
  map_add' first second := by
    apply Subtype.ext
    simp
  map_smul' scalar test := by
    apply Subtype.ext
    simp

/-- The Lagrangian ambient inclusion agrees with the minimal smooth inclusion. -/
theorem lagrangianInclusion_minimalCore
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (test : minimalDomainSubmodule core) :
    triple.lagrangianInclusion condition
        (minimalCoreToLagrangianDomain triple condition test) =
      minimalInclusion core test :=
  rfl

/-- The range of the minimal inclusion is contained in every Lagrangian
realization range. -/
theorem range_minimalInclusion_subset_lagrangianInclusion
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set.range (minimalInclusion core) ⊆
      Set.range (triple.lagrangianInclusion condition) := by
  rintro value ⟨test, rfl⟩
  exact ⟨minimalCoreToLagrangianDomain triple condition test,
    lagrangianInclusion_minimalCore triple condition test⟩

/-- Density of the minimal smooth core implies density of every completed
Lagrangian realization. -/
theorem lagrangianInclusion_denseRange_of_minimalCore
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hDense : MinimalCoreDense core) :
    DenseRange (triple.lagrangianInclusion condition) := by
  intro value
  exact closure_mono
    (range_minimalInclusion_subset_lagrangianInclusion triple condition)
    (hDense value)

/-- Simultaneous density certificate for all closed Lagrangian boundary
conditions. -/
theorem allLagrangianDomains_dense
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (hDense : MinimalCoreDense core) :
    ∀ condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace,
      DenseRange (triple.lagrangianInclusion condition) :=
  fun condition =>
    lagrangianInclusion_denseRange_of_minimalCore triple condition hDense

/-- Lagrangian-density certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (hDense : MinimalCoreDense core)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set.range (minimalInclusion core) ⊆
        Set.range (triple.lagrangianInclusion condition) ∧
      DenseRange (triple.lagrangianInclusion condition) :=
  ⟨range_minimalInclusion_subset_lagrangianInclusion triple condition,
    lagrangianInclusion_denseRange_of_minimalCore triple condition hDense⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
end JanusFormal
