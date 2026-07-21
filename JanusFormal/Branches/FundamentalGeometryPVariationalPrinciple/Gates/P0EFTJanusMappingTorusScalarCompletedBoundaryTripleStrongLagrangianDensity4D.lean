import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

/-!
# Density transfer to the strong closed presentation

The corrected completed boundary triple has a direct Lagrangian submodule inside
the maximal graph.  The compatibility bridge then regards that maximal graph as
the algebraic domain of a strong Green system and closes it once more for reuse
of the legacy spectral machinery.

Every direct Lagrangian vector maps canonically to the strong closed Lagrangian
domain, with identical ambient inclusion and operator value.  Therefore density
of the minimal smooth core transfers to the strong closed domain automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongLagrangianDensity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {TestDomain : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [AddCommGroup TestDomain] [Module Real TestDomain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Direct Lagrangian domain mapped into the strong closed Lagrangian domain. -/
noncomputable def directToStrongClosedLagrangianDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    triple.lagrangianDomainSubmodule condition →ₗ[Real]
      canonicalScalarClosedLagrangianDomainSubmodule
        triple.toStrongSystem
        (triple.toStrongSystem_closable testCore)
        triple.toStrongSystemBoundaryGraphBound
        condition where
  toFun field := by
    let graphField := canonicalScalarSmoothToOperatorGraphLinearMap
      triple.toStrongSystem field.1
    let closedField := canonicalScalarGraphToClosedDomainEquiv
      triple.toStrongSystem
      (triple.toStrongSystem_closable testCore) graphField
    refine ⟨closedField, ?_⟩
    change canonicalScalarClosedBoundaryTrace
        triple.toStrongSystem
        (triple.toStrongSystem_closable testCore)
        triple.toStrongSystemBoundaryGraphBound closedField ∈
      condition.subspace
    rw [canonicalScalarClosedBoundaryTrace_equiv,
      canonicalScalarCompletedBoundaryTrace_agrees_on_smooth]
    exact field.2
  map_add' first second := by
    apply Subtype.ext
    apply Subtype.ext
    simp [canonicalScalarGraphToClosedDomainEquiv]
  map_smul' scalar field := by
    apply Subtype.ext
    apply Subtype.ext
    simp [canonicalScalarGraphToClosedDomainEquiv]

/-- Ambient inclusion agrees under the direct-to-strong domain map. -/
theorem strongClosedInclusion_direct
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : triple.lagrangianDomainSubmodule condition) :
    canonicalScalarClosedLagrangianDomainInclusion
        triple.toStrongSystem
        (triple.toStrongSystem_closable testCore)
        triple.toStrongSystemBoundaryGraphBound
        condition
        (triple.directToStrongClosedLagrangianDomain testCore condition field) =
      triple.lagrangianInclusion condition field :=
  rfl

/-- Operator value agrees under the direct-to-strong domain map. -/
theorem strongClosedOperator_direct
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : triple.lagrangianDomainSubmodule condition) :
    canonicalScalarClosedLagrangianDomainOperator
        triple.toStrongSystem
        (triple.toStrongSystem_closable testCore)
        triple.toStrongSystemBoundaryGraphBound
        condition
        (triple.directToStrongClosedLagrangianDomain testCore condition field) =
      triple.lagrangianOperator condition field :=
  rfl

/-- The direct realization range is contained in the strong closed realization
range. -/
theorem range_direct_subset_strongClosed
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set.range (triple.lagrangianInclusion condition) ⊆
      Set.range
        (canonicalScalarClosedLagrangianDomainInclusion
          triple.toStrongSystem
          (triple.toStrongSystem_closable testCore)
          triple.toStrongSystemBoundaryGraphBound
          condition) := by
  rintro value ⟨field, rfl⟩
  exact ⟨triple.directToStrongClosedLagrangianDomain
      testCore condition field,
    triple.strongClosedInclusion_direct testCore condition field⟩

/-- Density of the direct Lagrangian realization transfers to the strong closed
domain. -/
theorem strongClosedLagrangianInclusion_denseRange
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        triple.toStrongSystem
        (triple.toStrongSystem_closable testCore)
        triple.toStrongSystemBoundaryGraphBound
        condition) := by
  intro value
  exact closure_mono
    (triple.range_direct_subset_strongClosed testCore condition)
    (hDense value)

/-- Minimal-core density gives strong closed-domain density for every condition. -/
theorem strongClosedLagrangianInclusion_denseRange_of_minimalCore
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hMinimalDense : core.MinimalCoreDense) :
    DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        triple.toStrongSystem
        (triple.toStrongSystem_closable testCore)
        triple.toStrongSystemBoundaryGraphBound
        condition) :=
  triple.strongClosedLagrangianInclusion_denseRange
    testCore condition
    (triple.lagrangianInclusion_denseRange_of_minimalCore
      condition hMinimalDense)

/-- Strong-density transfer certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hMinimalDense : core.MinimalCoreDense) :
    Set.range (triple.lagrangianInclusion condition) ⊆
        Set.range
          (canonicalScalarClosedLagrangianDomainInclusion
            triple.toStrongSystem
            (triple.toStrongSystem_closable testCore)
            triple.toStrongSystemBoundaryGraphBound
            condition) ∧
      DenseRange
        (canonicalScalarClosedLagrangianDomainInclusion
          triple.toStrongSystem
          (triple.toStrongSystem_closable testCore)
          triple.toStrongSystemBoundaryGraphBound
          condition) :=
  ⟨triple.range_direct_subset_strongClosed testCore condition,
    triple.strongClosedLagrangianInclusion_denseRange_of_minimalCore
      testCore condition hMinimalDense⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongLagrangianDensity4D
end JanusFormal
