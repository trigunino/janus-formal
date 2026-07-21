import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertRobinGraph4D

/-!
# Operator-valued Robin domains for the genuine closed scalar operator

This file pulls a bounded symmetric Robin graph on the Hilbert trace space back
to the actual closed scalar operator domain.  It proves symmetry, maximal
boundary-adjointness, the Neumann specialization, and exact agreement with the
constant scalar Robin domains built earlier.

The result is the natural boundary-triple realization for variable or
operator-valued Robin couplings.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarClosedRobinGraphRealization4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Pullback of an operator-valued Robin graph to the actual closed-operator
domain. -/
def canonicalScalarClosedRobinGraphDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace) :
    Submodule Real (canonicalScalarClosedOperatorDomain data) :=
  (canonicalScalarHilbertRobinGraphSubmodule robin).comap
    (canonicalScalarClosedBoundaryTrace data hClosable traceBound)

@[simp] theorem mem_canonicalScalarClosedRobinGraphDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (field : canonicalScalarClosedOperatorDomain data) :
    field ∈ canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin ↔
      (canonicalScalarClosedBoundaryTrace
          data hClosable traceBound field).2 =
        robin (canonicalScalarClosedBoundaryTrace
          data hClosable traceBound field).1 := by
  rfl

/-- Ambient inclusion restricted to an operator-valued Robin domain. -/
def canonicalScalarClosedRobinGraphDomainInclusion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin →ₗ[Real] Ambient :=
  (canonicalScalarClosedOperatorInclusion data).comp
    (canonicalScalarClosedRobinGraphDomainSubmodule
      data hClosable traceBound robin).subtype

/-- Closed operator restricted to an operator-valued Robin domain. -/
noncomputable def canonicalScalarClosedRobinGraphDomainOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin →ₗ[Real] Ambient :=
  (canonicalScalarClosedOperator data hClosable).comp
    (canonicalScalarClosedRobinGraphDomainSubmodule
      data hClosable traceBound robin).subtype

/-- The trace of a vector in the pulled-back Robin domain lies on the Hilbert
Robin graph. -/
theorem canonicalScalarClosedBoundaryTrace_mem_robinGraph
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (field : canonicalScalarClosedOperatorDomain data)
    (hField : field ∈ canonicalScalarClosedRobinGraphDomainSubmodule
      data hClosable traceBound robin) :
    canonicalScalarClosedBoundaryTrace data hClosable traceBound field ∈
      canonicalScalarHilbertRobinGraphSubmodule robin :=
  hField

/-- A bounded symmetric operator-valued Robin condition gives a symmetric
closed realization. -/
theorem canonicalScalarClosedRobinGraphDomainOperator_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (first second : canonicalScalarClosedRobinGraphDomainSubmodule
      data hClosable traceBound robin) :
    inner Real
        (canonicalScalarClosedRobinGraphDomainOperator
          data hClosable traceBound robin first)
        (canonicalScalarClosedRobinGraphDomainInclusion
          data hClosable traceBound robin second) =
      inner Real
        (canonicalScalarClosedRobinGraphDomainInclusion
          data hClosable traceBound robin first)
        (canonicalScalarClosedRobinGraphDomainOperator
          data hClosable traceBound robin second) := by
  have hBoundary :
      canonicalScalarHilbertBoundarySymplecticForm
          (canonicalScalarClosedBoundaryTrace
            data hClosable traceBound first.1)
          (canonicalScalarClosedBoundaryTrace
            data hClosable traceBound second.1) = 0 :=
    canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_robinGraph
      robin hRobin
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound first.1)
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound second.1)
      (canonicalScalarClosedBoundaryTrace_mem_robinGraph
        data hClosable traceBound robin first.1 first.2)
      (canonicalScalarClosedBoundaryTrace_mem_robinGraph
        data hClosable traceBound robin second.1 second.2)
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

/-- Boundary-adjoint test for an operator-valued Robin realization. -/
def canonicalScalarClosedRobinGraphAdjointAdmissible
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (candidate : canonicalScalarClosedOperatorDomain data) : Prop :=
  ∀ test : canonicalScalarClosedRobinGraphDomainSubmodule
      data hClosable traceBound robin,
    canonicalScalarHilbertBoundarySymplecticForm
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound candidate)
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound test.1) = 0

/-- Boundary-adjoint domain for an operator-valued Robin realization. -/
def canonicalScalarClosedRobinGraphAdjointDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace) :
    Set (canonicalScalarClosedOperatorDomain data) :=
  {candidate |
    canonicalScalarClosedRobinGraphAdjointAdmissible
      data hClosable traceBound robin candidate}

/-- Surjective trace and Hilbert Lagrangian maximality identify the Robin
boundary-adjoint candidates exactly with the Robin domain. -/
theorem canonicalScalarClosedRobinGraphAdjointAdmissible_iff_mem
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (candidate : canonicalScalarClosedOperatorDomain data) :
    canonicalScalarClosedRobinGraphAdjointAdmissible
        data hClosable traceBound robin candidate ↔
      candidate ∈ canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin := by
  constructor
  · intro hCandidate
    have hOrthogonal :
        canonicalScalarClosedBoundaryTrace
            data hClosable traceBound candidate ∈
          canonicalScalarHilbertBoundarySymplecticOrthogonal
            (canonicalScalarHilbertRobinGraphSubmodule robin) := by
      intro testBoundary hTestBoundary
      obtain ⟨test, hTrace⟩ :=
        canonicalScalarClosedBoundaryTrace_surjective
          data hClosable traceBound testBoundary
      have hTestDomain : test ∈
          canonicalScalarClosedRobinGraphDomainSubmodule
            data hClosable traceBound robin := by
        change canonicalScalarClosedBoundaryTrace
          data hClosable traceBound test ∈
            canonicalScalarHilbertRobinGraphSubmodule robin
        rw [hTrace]
        exact hTestBoundary
      have hApplied := hCandidate ⟨test, hTestDomain⟩
      rw [hTrace] at hApplied
      exact hApplied
    have hGraph :
        canonicalScalarClosedBoundaryTrace
            data hClosable traceBound candidate ∈
          canonicalScalarHilbertRobinGraphSubmodule robin := by
      rw [← canonicalScalarHilbertRobinGraphSubmodule_orthogonal_eq
        robin hRobin]
      exact hOrthogonal
    exact hGraph
  · intro hCandidate test
    exact canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_robinGraph
      robin hRobin
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound candidate)
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound test.1)
      (canonicalScalarClosedBoundaryTrace_mem_robinGraph
        data hClosable traceBound robin candidate hCandidate)
      (canonicalScalarClosedBoundaryTrace_mem_robinGraph
        data hClosable traceBound robin test.1 test.2)

/-- A bounded symmetric Robin graph equals its closed boundary-adjoint domain. -/
theorem canonicalScalarClosedRobinGraphAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    canonicalScalarClosedRobinGraphAdjointDomain
        data hClosable traceBound robin =
      (canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  ext candidate
  exact canonicalScalarClosedRobinGraphAdjointAdmissible_iff_mem
    data hClosable traceBound robin hRobin candidate

/-- Zero operator-valued Robin data recover the closed Neumann domain. -/
theorem canonicalScalarClosedRobinGraphDomainSubmodule_zero_eq_neumann
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound (0 : Trace →L[Real] Trace) =
      canonicalScalarClosedNeumannDomainSubmodule
        data hClosable traceBound := by
  ext field
  rw [mem_canonicalScalarClosedRobinGraphDomainSubmodule,
    mem_canonicalScalarClosedNeumannDomainSubmodule]
  simp

/-- Scalar multiplication Robin data recover the earlier constant Robin domain. -/
theorem canonicalScalarClosedRobinGraphDomainSubmodule_scalar_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real) :
    canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound
          (canonicalScalarHilbertScalarRobinOperator
            (Trace := Trace) coefficient) =
      canonicalScalarClosedRobinDomainSubmodule
        data hClosable traceBound coefficient := by
  ext field
  rw [mem_canonicalScalarClosedRobinGraphDomainSubmodule,
    mem_canonicalScalarClosedRobinDomainSubmodule]
  rfl

/-- Analytic Hilbert-adjoint characterization for an operator-valued Robin
domain. -/
structure CanonicalScalarClosedRobinGraphAdjointCharacterization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace) where
  adjointDomain : Set (canonicalScalarClosedOperatorDomain data)
  mem_adjointDomain_iff : ∀ candidate,
    candidate ∈ adjointDomain ↔
      canonicalScalarClosedRobinGraphAdjointAdmissible
        data hClosable traceBound robin candidate

/-- Once the genuine adjoint is identified by the Robin boundary test, its
domain is the original Robin graph domain. -/
theorem CanonicalScalarClosedRobinGraphAdjointCharacterization.adjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (characterization : CanonicalScalarClosedRobinGraphAdjointCharacterization
      data hClosable traceBound robin) :
    characterization.adjointDomain =
      (canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  ext candidate
  rw [characterization.mem_adjointDomain_iff]
  exact canonicalScalarClosedRobinGraphAdjointAdmissible_iff_mem
    data hClosable traceBound robin hRobin candidate

/-- Complete operator-valued Robin closure certificate. -/
theorem canonicalScalarClosedRobinGraphRealization_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    (∀ first second : canonicalScalarClosedRobinGraphDomainSubmodule
        data hClosable traceBound robin,
      inner Real
          (canonicalScalarClosedRobinGraphDomainOperator
            data hClosable traceBound robin first)
          (canonicalScalarClosedRobinGraphDomainInclusion
            data hClosable traceBound robin second) =
        inner Real
          (canonicalScalarClosedRobinGraphDomainInclusion
            data hClosable traceBound robin first)
          (canonicalScalarClosedRobinGraphDomainOperator
            data hClosable traceBound robin second)) ∧
      canonicalScalarClosedRobinGraphAdjointDomain
          data hClosable traceBound robin =
        (canonicalScalarClosedRobinGraphDomainSubmodule
          data hClosable traceBound robin :
            Set (canonicalScalarClosedOperatorDomain data)) :=
  ⟨canonicalScalarClosedRobinGraphDomainOperator_symmetric
      data hClosable traceBound robin hRobin,
    canonicalScalarClosedRobinGraphAdjointDomain_eq
      data hClosable traceBound robin hRobin⟩

end
end P0EFTJanusMappingTorusScalarClosedRobinGraphRealization4D
end JanusFormal
