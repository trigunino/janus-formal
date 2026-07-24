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
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D.CanonicalScalarCompletedBoundaryTripleData

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

variable
  {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Direct Lagrangian domain mapped into the strong closed Lagrangian domain. -/
noncomputable def directToStrongClosedLagrangianDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : StrongAdjointTestCore triple
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    triple.lagrangianDomainSubmodule condition →ₗ[Real]
      canonicalScalarClosedLagrangianDomainSubmodule
        (toStrongSystem triple)
        (toStrongSystem_closable triple testCore)
        (toStrongSystemBoundaryGraphBound triple)
        condition where
  toFun field := by
    let graphField := canonicalScalarSmoothToOperatorGraphLinearMap
      (toStrongSystem triple) field.1
    let closedField := canonicalScalarGraphToClosedDomainEquiv
      (toStrongSystem triple)
      (toStrongSystem_closable triple testCore) graphField
    refine ⟨closedField, ?_⟩
    change canonicalScalarClosedBoundaryTrace
        (toStrongSystem triple)
        (toStrongSystem_closable triple testCore)
        (toStrongSystemBoundaryGraphBound triple) closedField ∈
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
    (testCore : StrongAdjointTestCore triple
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : triple.lagrangianDomainSubmodule condition) :
    canonicalScalarClosedLagrangianDomainInclusion
        (toStrongSystem triple)
        (toStrongSystem_closable triple testCore)
        (toStrongSystemBoundaryGraphBound triple)
        condition
        (directToStrongClosedLagrangianDomain triple testCore condition field) =
      triple.lagrangianInclusion condition field :=
  rfl

/-- Operator value agrees under the direct-to-strong domain map. -/
theorem strongClosedOperator_direct
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : StrongAdjointTestCore triple
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : triple.lagrangianDomainSubmodule condition) :
    canonicalScalarClosedLagrangianDomainOperator
        (toStrongSystem triple)
        (toStrongSystem_closable triple testCore)
        (toStrongSystemBoundaryGraphBound triple)
        condition
        (directToStrongClosedLagrangianDomain triple testCore condition field) =
      triple.lagrangianOperator condition field :=
  by
    change canonicalScalarClosedOperator
        (toStrongSystem triple)
        (toStrongSystem_closable triple testCore)
        (canonicalScalarGraphToClosedDomainEquiv
          (toStrongSystem triple)
          (toStrongSystem_closable triple testCore)
          (canonicalScalarSmoothToOperatorGraphLinearMap
            (toStrongSystem triple) field.1)) = _
    rw [canonicalScalarClosedOperator_equiv]
    rfl

/-- The direct realization range is contained in the strong closed realization
range. -/
theorem range_direct_subset_strongClosed
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : StrongAdjointTestCore triple
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set.range (triple.lagrangianInclusion condition) ⊆
      Set.range
        (canonicalScalarClosedLagrangianDomainInclusion
          (toStrongSystem triple)
          (toStrongSystem_closable triple testCore)
          (toStrongSystemBoundaryGraphBound triple)
          condition) := by
  rintro value ⟨field, rfl⟩
  exact ⟨directToStrongClosedLagrangianDomain triple
      testCore condition field,
    strongClosedInclusion_direct triple testCore condition field⟩

/-- Density of the direct Lagrangian realization transfers to the strong closed
domain. -/
theorem strongClosedLagrangianInclusion_denseRange
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : StrongAdjointTestCore triple
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        (toStrongSystem triple)
        (toStrongSystem_closable triple testCore)
        (toStrongSystemBoundaryGraphBound triple)
        condition) := by
  intro value
  exact closure_mono
    (range_direct_subset_strongClosed triple testCore condition)
    (hDense value)

/-- Minimal-core density gives strong closed-domain density for every condition. -/
theorem strongClosedLagrangianInclusion_denseRange_of_minimalCore
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : StrongAdjointTestCore triple
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hMinimalDense : MinimalCoreDense core) :
    DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        (toStrongSystem triple)
        (toStrongSystem_closable triple testCore)
        (toStrongSystemBoundaryGraphBound triple)
        condition) :=
  strongClosedLagrangianInclusion_denseRange triple
    testCore condition
    (lagrangianInclusion_denseRange_of_minimalCore
      triple condition hMinimalDense)

/-- Strong-density transfer certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : StrongAdjointTestCore triple
      (TestDomain := TestDomain))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (hMinimalDense : MinimalCoreDense core) :
    Set.range (triple.lagrangianInclusion condition) ⊆
        Set.range
          (canonicalScalarClosedLagrangianDomainInclusion
            (toStrongSystem triple)
            (toStrongSystem_closable triple testCore)
            (toStrongSystemBoundaryGraphBound triple)
            condition) ∧
      DenseRange
        (canonicalScalarClosedLagrangianDomainInclusion
          (toStrongSystem triple)
          (toStrongSystem_closable triple testCore)
          (toStrongSystemBoundaryGraphBound triple)
          condition) :=
  ⟨range_direct_subset_strongClosed triple testCore condition,
    strongClosedLagrangianInclusion_denseRange_of_minimalCore
      triple testCore condition hMinimalDense⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongLagrangianDensity4D
end JanusFormal
