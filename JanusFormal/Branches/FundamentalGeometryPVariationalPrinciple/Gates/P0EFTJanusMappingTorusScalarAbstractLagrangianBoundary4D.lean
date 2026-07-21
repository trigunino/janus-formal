import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarClosedRobinGraphRealization4D

/-!
# Abstract Lagrangian scalar boundary conditions

Separated conditions and operator-valued Robin graphs are instances of one
boundary-triple principle: a closed Lagrangian subspace of the paired Hilbert
trace space determines a closed symmetric domain whose boundary-adjoint domain
is maximal.

This file packages that principle once and for all.  It supplies both:

* the completed graph-domain realization, where closedness follows from the
  continuous completed trace;
* the genuine single-valued closed-operator realization, under the explicit
  closability hypothesis.

Dirichlet, Neumann, scalar Robin, variable separated data and bounded symmetric
operator-valued Robin graphs are constructors of the same abstract boundary
condition.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
open P0EFTJanusMappingTorusScalarClosedRobinGraphRealization4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- A closed Lagrangian subspace of paired scalar boundary traces. -/
structure CanonicalScalarHilbertLagrangianBoundaryCondition
    (Trace : Type w)
    [NormedAddCommGroup Trace] [InnerProductSpace Real Trace] where
  subspace : Submodule Real
    (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))
  isClosed : IsClosed
    (subspace : Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)))
  lagrangian :
    canonicalScalarHilbertBoundarySymplecticOrthogonal subspace = subspace

namespace CanonicalScalarHilbertLagrangianBoundaryCondition

/-- Every nondegenerate separated scalar trace condition is Lagrangian. -/
noncomputable def separated
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    CanonicalScalarHilbertLagrangianBoundaryCondition Trace where
  subspace := canonicalScalarHilbertSeparatedBoundarySubmodule
    (Trace := Trace) a b
  isClosed := canonicalScalarHilbertSeparatedBoundarySubmodule_isClosed
    (Trace := Trace) a b
  lagrangian := canonicalScalarHilbertSeparatedBoundarySubmodule_orthogonal_eq
    (Trace := Trace) a b hNondegenerate

/-- Dirichlet Lagrangian boundary condition. -/
noncomputable def dirichlet :
    CanonicalScalarHilbertLagrangianBoundaryCondition Trace :=
  separated (Trace := Trace) 1 0 (Or.inl one_ne_zero)

/-- Neumann Lagrangian boundary condition. -/
noncomputable def neumann :
    CanonicalScalarHilbertLagrangianBoundaryCondition Trace :=
  separated (Trace := Trace) 0 1 (Or.inr one_ne_zero)

/-- Constant scalar Robin Lagrangian boundary condition. -/
noncomputable def scalarRobin (coefficient : Real) :
    CanonicalScalarHilbertLagrangianBoundaryCondition Trace :=
  separated (Trace := Trace) (-coefficient) 1 (Or.inr one_ne_zero)

/-- Every bounded symmetric operator-valued Robin graph is Lagrangian. -/
noncomputable def robinGraph
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    CanonicalScalarHilbertLagrangianBoundaryCondition Trace where
  subspace := canonicalScalarHilbertRobinGraphSubmodule robin
  isClosed := canonicalScalarHilbertRobinGraphSubmodule_isClosed robin
  lagrangian := canonicalScalarHilbertRobinGraphSubmodule_orthogonal_eq
    robin hRobin

end CanonicalScalarHilbertLagrangianBoundaryCondition

/-! ## Completed graph realization -/

/-- Pullback of an abstract Lagrangian boundary condition to the completed
operator graph. -/
def canonicalScalarCompletedLagrangianDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Submodule Real (CanonicalScalarOperatorGraphSpace data) :=
  condition.subspace.comap
    (canonicalScalarCompletedBoundaryTrace data traceBound).toLinearMap

@[simp] theorem mem_canonicalScalarCompletedLagrangianDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : CanonicalScalarOperatorGraphSpace data) :
    field ∈ canonicalScalarCompletedLagrangianDomainSubmodule
        data traceBound condition ↔
      canonicalScalarCompletedBoundaryTrace data traceBound field ∈
        condition.subspace :=
  Iff.rfl

/-- Every abstract completed Lagrangian graph domain is closed. -/
theorem canonicalScalarCompletedLagrangianDomainSubmodule_isClosed
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    IsClosed
      (canonicalScalarCompletedLagrangianDomainSubmodule
        data traceBound condition : Set (CanonicalScalarOperatorGraphSpace data)) := by
  change IsClosed
    ((canonicalScalarCompletedBoundaryTrace data traceBound) ⁻¹'
      (condition.subspace :
        Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))))
  exact condition.isClosed.preimage
    (canonicalScalarCompletedBoundaryTrace data traceBound).continuous

/-- Ambient inclusion restricted to a completed abstract Lagrangian domain. -/
def canonicalScalarCompletedLagrangianDomainInclusion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarCompletedLagrangianDomainSubmodule
        data traceBound condition →L[Real] Ambient :=
  (canonicalScalarOperatorGraphInclusion data).comp
    (canonicalScalarCompletedLagrangianDomainSubmodule
      data traceBound condition).subtypeL

/-- Graph operator restricted to a completed abstract Lagrangian domain. -/
def canonicalScalarCompletedLagrangianDomainOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarCompletedLagrangianDomainSubmodule
        data traceBound condition →L[Real] Ambient :=
  (canonicalScalarOperatorGraphOperator data).comp
    (canonicalScalarCompletedLagrangianDomainSubmodule
      data traceBound condition).subtypeL

/-- Isotropy of every abstract Lagrangian condition. -/
theorem CanonicalScalarHilbertLagrangianBoundaryCondition.pairing_eq_zero
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second : CanonicalScalarHilbertBoundaryDatum (Trace := Trace))
    (hFirst : first ∈ condition.subspace)
    (hSecond : second ∈ condition.subspace) :
    canonicalScalarHilbertBoundarySymplecticForm first second = 0 := by
  have hFirstOrthogonal :
      first ∈ canonicalScalarHilbertBoundarySymplecticOrthogonal
        condition.subspace := by
    rw [condition.lagrangian]
    exact hFirst
  exact hFirstOrthogonal second hSecond

/-- Every completed abstract Lagrangian realization is symmetric. -/
theorem canonicalScalarCompletedLagrangianDomainOperator_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second : canonicalScalarCompletedLagrangianDomainSubmodule
      data traceBound condition) :
    inner Real
        (canonicalScalarCompletedLagrangianDomainOperator
          data traceBound condition first)
        (canonicalScalarCompletedLagrangianDomainInclusion
          data traceBound condition second) =
      inner Real
        (canonicalScalarCompletedLagrangianDomainInclusion
          data traceBound condition first)
        (canonicalScalarCompletedLagrangianDomainOperator
          data traceBound condition second) := by
  have hBoundary := condition.pairing_eq_zero
    (canonicalScalarCompletedBoundaryTrace data traceBound first.1)
    (canonicalScalarCompletedBoundaryTrace data traceBound second.1)
    first.2 second.2
  have hGreen := canonicalScalarCompletedGreenIdentity
    data traceBound first.1 second.1
  unfold canonicalScalarCompletedBoundaryGreenPairing at hGreen
  rw [hBoundary] at hGreen
  change inner Real
      (canonicalScalarOperatorGraphOperator data first.1)
      (canonicalScalarOperatorGraphInclusion data second.1) =
    inner Real
      (canonicalScalarOperatorGraphInclusion data first.1)
      (canonicalScalarOperatorGraphOperator data second.1)
  linarith

/-- Boundary-adjoint test on the completed graph for an abstract Lagrangian
condition. -/
def canonicalScalarCompletedLagrangianAdjointAdmissible
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (candidate : CanonicalScalarOperatorGraphSpace data) : Prop :=
  ∀ test : canonicalScalarCompletedLagrangianDomainSubmodule
      data traceBound condition,
    canonicalScalarHilbertBoundarySymplecticForm
      (canonicalScalarCompletedBoundaryTrace data traceBound candidate)
      (canonicalScalarCompletedBoundaryTrace data traceBound test.1) = 0

/-- Completed abstract Lagrangian boundary-adjoint domain. -/
def canonicalScalarCompletedLagrangianAdjointDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set (CanonicalScalarOperatorGraphSpace data) :=
  {candidate |
    canonicalScalarCompletedLagrangianAdjointAdmissible
      data traceBound condition candidate}

/-- Maximality of every completed abstract Lagrangian boundary condition. -/
theorem canonicalScalarCompletedLagrangianAdjointAdmissible_iff_mem
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (candidate : CanonicalScalarOperatorGraphSpace data) :
    canonicalScalarCompletedLagrangianAdjointAdmissible
        data traceBound condition candidate ↔
      candidate ∈ canonicalScalarCompletedLagrangianDomainSubmodule
        data traceBound condition := by
  constructor
  · intro hCandidate
    have hOrthogonal :
        canonicalScalarCompletedBoundaryTrace data traceBound candidate ∈
          canonicalScalarHilbertBoundarySymplecticOrthogonal
            condition.subspace := by
      intro testBoundary hTestBoundary
      obtain ⟨test, hTrace⟩ :=
        canonicalScalarCompletedBoundaryTrace_surjective
          data traceBound testBoundary
      have hTestDomain : test ∈
          canonicalScalarCompletedLagrangianDomainSubmodule
            data traceBound condition := by
        change canonicalScalarCompletedBoundaryTrace data traceBound test ∈
          condition.subspace
        rw [hTrace]
        exact hTestBoundary
      have hApplied := hCandidate ⟨test, hTestDomain⟩
      rw [hTrace] at hApplied
      exact hApplied
    simpa [condition.lagrangian] using hOrthogonal
  · intro hCandidate test
    have hCandidateOrthogonal :
        canonicalScalarCompletedBoundaryTrace data traceBound candidate ∈
          canonicalScalarHilbertBoundarySymplecticOrthogonal
            condition.subspace := by
      rw [condition.lagrangian]
      exact hCandidate
    exact hCandidateOrthogonal
      (canonicalScalarCompletedBoundaryTrace data traceBound test.1) test.2

/-- Completed abstract Lagrangian domain equals its boundary-adjoint domain. -/
theorem canonicalScalarCompletedLagrangianAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarCompletedLagrangianAdjointDomain
        data traceBound condition =
      (canonicalScalarCompletedLagrangianDomainSubmodule
        data traceBound condition : Set (CanonicalScalarOperatorGraphSpace data)) := by
  ext candidate
  exact canonicalScalarCompletedLagrangianAdjointAdmissible_iff_mem
    data traceBound condition candidate

/-! ## Genuine single-valued closed-operator realization -/

/-- Pullback of an abstract Lagrangian condition to the genuine closed-operator
domain. -/
def canonicalScalarClosedLagrangianDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Submodule Real (canonicalScalarClosedOperatorDomain data) :=
  condition.subspace.comap
    (canonicalScalarClosedBoundaryTrace data hClosable traceBound)

@[simp] theorem mem_canonicalScalarClosedLagrangianDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (field : canonicalScalarClosedOperatorDomain data) :
    field ∈ canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition ↔
      canonicalScalarClosedBoundaryTrace data hClosable traceBound field ∈
        condition.subspace :=
  Iff.rfl

/-- Ambient inclusion restricted to an actual abstract Lagrangian domain. -/
def canonicalScalarClosedLagrangianDomainInclusion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition →ₗ[Real] Ambient :=
  (canonicalScalarClosedOperatorInclusion data).comp
    (canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition).subtype

/-- Actual closed operator restricted to an abstract Lagrangian domain. -/
noncomputable def canonicalScalarClosedLagrangianDomainOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition →ₗ[Real] Ambient :=
  (canonicalScalarClosedOperator data hClosable).comp
    (canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition).subtype

/-- Every genuine closed abstract Lagrangian realization is symmetric. -/
theorem canonicalScalarClosedLagrangianDomainOperator_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (first second : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    inner Real
        (canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition first)
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition second) =
      inner Real
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition first)
        (canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition second) := by
  have hBoundary := condition.pairing_eq_zero
    (canonicalScalarClosedBoundaryTrace data hClosable traceBound first.1)
    (canonicalScalarClosedBoundaryTrace data hClosable traceBound second.1)
    first.2 second.2
  have hGreen := canonicalScalarClosedGreenIdentity
    data hClosable traceBound first.1 second.1
  rw [hBoundary] at hGreen
  change inner Real
      (canonicalScalarClosedOperator data hClosable first.1)
      (canonicalScalarClosedOperatorInclusion data second.1) =
    inner Real
      (canonicalScalarClosedOperatorInclusion data first.1)
      (canonicalScalarClosedOperator data hClosable second.1)
  linarith

/-- Boundary-adjoint admissibility on the genuine closed domain for an abstract
Lagrangian condition. -/
def canonicalScalarClosedLagrangianAdjointAdmissible
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (candidate : canonicalScalarClosedOperatorDomain data) : Prop :=
  ∀ test : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition,
    canonicalScalarHilbertBoundarySymplecticForm
      (canonicalScalarClosedBoundaryTrace data hClosable traceBound candidate)
      (canonicalScalarClosedBoundaryTrace data hClosable traceBound test.1) = 0

/-- Actual abstract Lagrangian boundary-adjoint domain. -/
def canonicalScalarClosedLagrangianAdjointDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set (canonicalScalarClosedOperatorDomain data) :=
  {candidate |
    canonicalScalarClosedLagrangianAdjointAdmissible
      data hClosable traceBound condition candidate}

/-- Maximality of every genuine closed abstract Lagrangian domain. -/
theorem canonicalScalarClosedLagrangianAdjointAdmissible_iff_mem
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (candidate : canonicalScalarClosedOperatorDomain data) :
    canonicalScalarClosedLagrangianAdjointAdmissible
        data hClosable traceBound condition candidate ↔
      candidate ∈ canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition := by
  constructor
  · intro hCandidate
    have hOrthogonal :
        canonicalScalarClosedBoundaryTrace data hClosable traceBound candidate ∈
          canonicalScalarHilbertBoundarySymplecticOrthogonal
            condition.subspace := by
      intro testBoundary hTestBoundary
      obtain ⟨test, hTrace⟩ :=
        canonicalScalarClosedBoundaryTrace_surjective
          data hClosable traceBound testBoundary
      have hTestDomain : test ∈
          canonicalScalarClosedLagrangianDomainSubmodule
            data hClosable traceBound condition := by
        change canonicalScalarClosedBoundaryTrace
          data hClosable traceBound test ∈ condition.subspace
        rw [hTrace]
        exact hTestBoundary
      have hApplied := hCandidate ⟨test, hTestDomain⟩
      rw [hTrace] at hApplied
      exact hApplied
    simpa [condition.lagrangian] using hOrthogonal
  · intro hCandidate test
    have hCandidateOrthogonal :
        canonicalScalarClosedBoundaryTrace data hClosable traceBound candidate ∈
          canonicalScalarHilbertBoundarySymplecticOrthogonal
            condition.subspace := by
      rw [condition.lagrangian]
      exact hCandidate
    exact hCandidateOrthogonal
      (canonicalScalarClosedBoundaryTrace data hClosable traceBound test.1)
      test.2

/-- Genuine closed abstract Lagrangian domain equals its boundary-adjoint
domain. -/
theorem canonicalScalarClosedLagrangianAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarClosedLagrangianAdjointDomain
        data hClosable traceBound condition =
      (canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  ext candidate
  exact canonicalScalarClosedLagrangianAdjointAdmissible_iff_mem
    data hClosable traceBound condition candidate

/-- The abstract separated constructor recovers the existing completed
separated domain. -/
theorem canonicalScalarCompletedLagrangianDomainSubmodule_separated_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    canonicalScalarCompletedLagrangianDomainSubmodule data traceBound
        (CanonicalScalarHilbertLagrangianBoundaryCondition.separated
          (Trace := Trace) a b hNondegenerate) =
      canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b :=
  rfl

/-- The abstract separated constructor recovers the existing actual closed
separated domain. -/
theorem canonicalScalarClosedLagrangianDomainSubmodule_separated_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    canonicalScalarClosedLagrangianDomainSubmodule data hClosable traceBound
        (CanonicalScalarHilbertLagrangianBoundaryCondition.separated
          (Trace := Trace) a b hNondegenerate) =
      canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b :=
  rfl

/-- The abstract Robin-graph constructor recovers the existing actual Robin
graph domain. -/
theorem canonicalScalarClosedLagrangianDomainSubmodule_robinGraph_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    canonicalScalarClosedLagrangianDomainSubmodule data hClosable traceBound
        (CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph
          robin hRobin) =
      canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin :=
  rfl

/-- Unified closure certificate for an arbitrary closed Lagrangian scalar
boundary condition. -/
theorem canonicalScalarAbstractLagrangianBoundary_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    IsClosed
        (canonicalScalarCompletedLagrangianDomainSubmodule
          data traceBound condition : Set (CanonicalScalarOperatorGraphSpace data)) ∧
      (∀ first second : canonicalScalarClosedLagrangianDomainSubmodule
          data hClosable traceBound condition,
        inner Real
            (canonicalScalarClosedLagrangianDomainOperator
              data hClosable traceBound condition first)
            (canonicalScalarClosedLagrangianDomainInclusion
              data hClosable traceBound condition second) =
          inner Real
            (canonicalScalarClosedLagrangianDomainInclusion
              data hClosable traceBound condition first)
            (canonicalScalarClosedLagrangianDomainOperator
              data hClosable traceBound condition second)) ∧
      canonicalScalarClosedLagrangianAdjointDomain
          data hClosable traceBound condition =
        (canonicalScalarClosedLagrangianDomainSubmodule
          data hClosable traceBound condition :
            Set (canonicalScalarClosedOperatorDomain data)) :=
  ⟨canonicalScalarCompletedLagrangianDomainSubmodule_isClosed
      data traceBound condition,
    canonicalScalarClosedLagrangianDomainOperator_symmetric
      data hClosable traceBound condition,
    canonicalScalarClosedLagrangianAdjointDomain_eq
      data hClosable traceBound condition⟩

end
end P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
end JanusFormal
