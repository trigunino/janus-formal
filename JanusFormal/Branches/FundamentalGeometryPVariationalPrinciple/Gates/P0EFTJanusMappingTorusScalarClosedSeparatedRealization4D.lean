import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarClosedGraphRealization4D

/-!
# Separated domains on the genuine closed scalar operator

The graph realization is single-valued under the explicit closability
hypothesis.  This file imposes Dirichlet, Neumann and constant real Robin
conditions directly on that actual operator domain.

The completed paired trace remains surjective, so every nondegenerate separated
trace subspace is again maximally isotropic.  Consequently the restricted
closed operator is symmetric and its boundary-adjoint domain equals the
original separated domain.

A final structure records the remaining analytic datum needed for a genuine
unbounded self-adjoint realization: density of the restricted ambient inclusion
and identification of the actual Hilbert adjoint domain with the displayed
boundary test.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Pullback of a separated Hilbert trace space to the genuine closed-operator
domain. -/
def canonicalScalarClosedSeparatedDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    Submodule Real (canonicalScalarClosedOperatorDomain data) :=
  (canonicalScalarHilbertSeparatedBoundarySubmodule
    (Trace := Trace) a b).comap
      (canonicalScalarClosedBoundaryTrace data hClosable traceBound)

@[simp] theorem mem_canonicalScalarClosedSeparatedDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (field : canonicalScalarClosedOperatorDomain data) :
    field ∈ canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b ↔
      a • (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound field).1 +
        b • (canonicalScalarClosedBoundaryTrace
          data hClosable traceBound field).2 = 0 := by
  rfl

/-- Closed Dirichlet domain. -/
def canonicalScalarClosedDirichletDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Submodule Real (canonicalScalarClosedOperatorDomain data) :=
  canonicalScalarClosedSeparatedDomainSubmodule
    data hClosable traceBound 1 0

/-- Closed Neumann domain. -/
def canonicalScalarClosedNeumannDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Submodule Real (canonicalScalarClosedOperatorDomain data) :=
  canonicalScalarClosedSeparatedDomainSubmodule
    data hClosable traceBound 0 1

/-- Closed constant real Robin domain `normal = coefficient • value`. -/
def canonicalScalarClosedRobinDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real) :
    Submodule Real (canonicalScalarClosedOperatorDomain data) :=
  canonicalScalarClosedSeparatedDomainSubmodule
    data hClosable traceBound (-coefficient) 1

@[simp] theorem mem_canonicalScalarClosedDirichletDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : canonicalScalarClosedOperatorDomain data) :
    field ∈ canonicalScalarClosedDirichletDomainSubmodule
        data hClosable traceBound ↔
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound field).1 = 0 := by
  unfold canonicalScalarClosedDirichletDomainSubmodule
  rw [mem_canonicalScalarClosedSeparatedDomainSubmodule]
  simp

@[simp] theorem mem_canonicalScalarClosedNeumannDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : canonicalScalarClosedOperatorDomain data) :
    field ∈ canonicalScalarClosedNeumannDomainSubmodule
        data hClosable traceBound ↔
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound field).2 = 0 := by
  unfold canonicalScalarClosedNeumannDomainSubmodule
  rw [mem_canonicalScalarClosedSeparatedDomainSubmodule]
  simp

@[simp] theorem mem_canonicalScalarClosedRobinDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real)
    (field : canonicalScalarClosedOperatorDomain data) :
    field ∈ canonicalScalarClosedRobinDomainSubmodule
        data hClosable traceBound coefficient ↔
      (canonicalScalarClosedBoundaryTrace
          data hClosable traceBound field).2 =
        coefficient • (canonicalScalarClosedBoundaryTrace
          data hClosable traceBound field).1 := by
  unfold canonicalScalarClosedRobinDomainSubmodule
  rw [mem_canonicalScalarClosedSeparatedDomainSubmodule]
  simp only [one_smul]
  constructor
  · intro h
    have hSub :
        (canonicalScalarClosedBoundaryTrace
            data hClosable traceBound field).2 -
          coefficient • (canonicalScalarClosedBoundaryTrace
            data hClosable traceBound field).1 = 0 := by
      calc
        (canonicalScalarClosedBoundaryTrace
              data hClosable traceBound field).2 -
            coefficient • (canonicalScalarClosedBoundaryTrace
              data hClosable traceBound field).1 =
          (-coefficient) • (canonicalScalarClosedBoundaryTrace
              data hClosable traceBound field).1 +
            (canonicalScalarClosedBoundaryTrace
              data hClosable traceBound field).2 := by module
        _ = 0 := h
    exact sub_eq_zero.mp hSub
  · intro h
    rw [h]
    module

/-- Ambient inclusion restricted to a closed separated domain. -/
def canonicalScalarClosedSeparatedDomainInclusion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b →ₗ[Real] Ambient :=
  (canonicalScalarClosedOperatorInclusion data).comp
    (canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b).subtype

/-- Closed operator restricted to a separated boundary domain. -/
noncomputable def canonicalScalarClosedSeparatedDomainOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b →ₗ[Real] Ambient :=
  (canonicalScalarClosedOperator data hClosable).comp
    (canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b).subtype

/-- The trace of every vector in a closed separated domain lies in the
corresponding Lagrangian trace subspace. -/
theorem canonicalScalarClosedBoundaryTrace_mem_separated
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (field : canonicalScalarClosedOperatorDomain data)
    (hField : field ∈ canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b) :
    canonicalScalarClosedBoundaryTrace data hClosable traceBound field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := Trace) a b :=
  hField

/-- Every nondegenerate closed separated realization is symmetric. -/
theorem canonicalScalarClosedSeparatedDomainOperator_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (first second : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b) :
    inner Real
        (canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b first)
        (canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b second) =
      inner Real
        (canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b first)
        (canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b second) := by
  have hBoundary :
      canonicalScalarHilbertBoundarySymplecticForm
          (canonicalScalarClosedBoundaryTrace
            data hClosable traceBound first.1)
          (canonicalScalarClosedBoundaryTrace
            data hClosable traceBound second.1) = 0 :=
    canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_separated
      (Trace := Trace) a b hNondegenerate
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound first.1)
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound second.1)
      (canonicalScalarClosedBoundaryTrace_mem_separated
        data hClosable traceBound a b first.1 first.2)
      (canonicalScalarClosedBoundaryTrace_mem_separated
        data hClosable traceBound a b second.1 second.2)
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

/-- Boundary test defining candidates for the adjoint of a closed separated
realization. -/
def canonicalScalarClosedBoundaryAdjointAdmissible
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (candidate : canonicalScalarClosedOperatorDomain data) : Prop :=
  ∀ test : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b,
    canonicalScalarHilbertBoundarySymplecticForm
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound candidate)
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound test.1) = 0

/-- Closed boundary-adjoint domain. -/
def canonicalScalarClosedBoundaryAdjointDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) : Set (canonicalScalarClosedOperatorDomain data) :=
  {candidate |
    canonicalScalarClosedBoundaryAdjointAdmissible
      data hClosable traceBound a b candidate}

/-- Surjectivity of the actual closed trace and Lagrangian maximality identify
boundary-adjoint candidates with the original separated domain. -/
theorem canonicalScalarClosedBoundaryAdjointAdmissible_iff_mem
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (candidate : canonicalScalarClosedOperatorDomain data) :
    canonicalScalarClosedBoundaryAdjointAdmissible
        data hClosable traceBound a b candidate ↔
      candidate ∈ canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b := by
  constructor
  · intro hCandidate
    have hOrthogonal :
        canonicalScalarClosedBoundaryTrace
            data hClosable traceBound candidate ∈
          canonicalScalarHilbertBoundarySymplecticOrthogonal
            (canonicalScalarHilbertSeparatedBoundarySubmodule
              (Trace := Trace) a b) := by
      intro testBoundary hTestBoundary
      obtain ⟨test, hTrace⟩ :=
        canonicalScalarClosedBoundaryTrace_surjective
          data hClosable traceBound testBoundary
      have hTestDomain : test ∈
          canonicalScalarClosedSeparatedDomainSubmodule
            data hClosable traceBound a b := by
        change canonicalScalarClosedBoundaryTrace
          data hClosable traceBound test ∈
            canonicalScalarHilbertSeparatedBoundarySubmodule
              (Trace := Trace) a b
        rw [hTrace]
        exact hTestBoundary
      have hApplied := hCandidate ⟨test, hTestDomain⟩
      rw [hTrace] at hApplied
      exact hApplied
    have hSeparated :
        canonicalScalarClosedBoundaryTrace
            data hClosable traceBound candidate ∈
          canonicalScalarHilbertSeparatedBoundarySubmodule
            (Trace := Trace) a b := by
      rw [← canonicalScalarHilbertSeparatedBoundarySubmodule_orthogonal_eq
        (Trace := Trace) a b hNondegenerate]
      exact hOrthogonal
    exact hSeparated
  · intro hCandidate test
    exact canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_separated
      (Trace := Trace) a b hNondegenerate
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound candidate)
      (canonicalScalarClosedBoundaryTrace
        data hClosable traceBound test.1)
      (canonicalScalarClosedBoundaryTrace_mem_separated
        data hClosable traceBound a b candidate hCandidate)
      (canonicalScalarClosedBoundaryTrace_mem_separated
        data hClosable traceBound a b test.1 test.2)

/-- A closed separated domain equals its boundary-adjoint domain. -/
theorem canonicalScalarClosedBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    canonicalScalarClosedBoundaryAdjointDomain
        data hClosable traceBound a b =
      (canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  ext candidate
  exact canonicalScalarClosedBoundaryAdjointAdmissible_iff_mem
    data hClosable traceBound a b hNondegenerate candidate

/-- Analytic identification of a genuine Hilbert-adjoint domain with the closed
boundary test. -/
structure CanonicalScalarClosedAdjointBoundaryCharacterization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) where
  adjointDomain : Set (canonicalScalarClosedOperatorDomain data)
  mem_adjointDomain_iff : ∀ candidate,
    candidate ∈ adjointDomain ↔
      canonicalScalarClosedBoundaryAdjointAdmissible
        data hClosable traceBound a b candidate

/-- Once the analytic adjoint is characterized by the boundary test, its domain
is exactly the original nondegenerate separated domain. -/
theorem CanonicalScalarClosedAdjointBoundaryCharacterization.adjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (characterization : CanonicalScalarClosedAdjointBoundaryCharacterization
      data hClosable traceBound a b) :
    characterization.adjointDomain =
      (canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  ext candidate
  rw [characterization.mem_adjointDomain_iff]
  exact canonicalScalarClosedBoundaryAdjointAdmissible_iff_mem
    data hClosable traceBound a b hNondegenerate candidate

/-- Complete analytic input package for a genuine self-adjoint separated
realization.  Density and the actual-adjoint characterization are kept explicit. -/
structure CanonicalScalarClosedSelfAdjointBoundaryData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) where
  nondegenerate : a ≠ 0 ∨ b ≠ 0
  dense_inclusion : DenseRange
    (canonicalScalarClosedSeparatedDomainInclusion
      data hClosable traceBound a b)
  adjointCharacterization :
    CanonicalScalarClosedAdjointBoundaryCharacterization
      data hClosable traceBound a b

/-- Self-adjoint-boundary certificate: dense domain, symmetry, and equality of
actual adjoint and original domains. -/
theorem canonicalScalarClosedSelfAdjointBoundary_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real)
    (selfAdjointData : CanonicalScalarClosedSelfAdjointBoundaryData
      data hClosable traceBound a b) :
    DenseRange (canonicalScalarClosedSeparatedDomainInclusion
      data hClosable traceBound a b) ∧
      (∀ first second : canonicalScalarClosedSeparatedDomainSubmodule
          data hClosable traceBound a b,
        inner Real
            (canonicalScalarClosedSeparatedDomainOperator
              data hClosable traceBound a b first)
            (canonicalScalarClosedSeparatedDomainInclusion
              data hClosable traceBound a b second) =
          inner Real
            (canonicalScalarClosedSeparatedDomainInclusion
              data hClosable traceBound a b first)
            (canonicalScalarClosedSeparatedDomainOperator
              data hClosable traceBound a b second)) ∧
      selfAdjointData.adjointCharacterization.adjointDomain =
        (canonicalScalarClosedSeparatedDomainSubmodule
          data hClosable traceBound a b :
            Set (canonicalScalarClosedOperatorDomain data)) := by
  exact ⟨selfAdjointData.dense_inclusion,
    canonicalScalarClosedSeparatedDomainOperator_symmetric
      data hClosable traceBound a b selfAdjointData.nondegenerate,
    selfAdjointData.adjointCharacterization.adjointDomain_eq
      data hClosable traceBound a b selfAdjointData.nondegenerate⟩

/-- Dirichlet boundary-adjoint maximality on the genuine closed operator. -/
theorem canonicalScalarClosedDirichletBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    canonicalScalarClosedBoundaryAdjointDomain
        data hClosable traceBound 1 0 =
      (canonicalScalarClosedDirichletDomainSubmodule
        data hClosable traceBound :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  exact canonicalScalarClosedBoundaryAdjointDomain_eq
    data hClosable traceBound 1 0 (Or.inl one_ne_zero)

/-- Neumann boundary-adjoint maximality on the genuine closed operator. -/
theorem canonicalScalarClosedNeumannBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    canonicalScalarClosedBoundaryAdjointDomain
        data hClosable traceBound 0 1 =
      (canonicalScalarClosedNeumannDomainSubmodule
        data hClosable traceBound :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  exact canonicalScalarClosedBoundaryAdjointDomain_eq
    data hClosable traceBound 0 1 (Or.inr one_ne_zero)

/-- Constant real Robin boundary-adjoint maximality on the genuine closed
operator. -/
theorem canonicalScalarClosedRobinBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real) :
    canonicalScalarClosedBoundaryAdjointDomain
        data hClosable traceBound (-coefficient) 1 =
      (canonicalScalarClosedRobinDomainSubmodule
        data hClosable traceBound coefficient :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  exact canonicalScalarClosedBoundaryAdjointDomain_eq
    data hClosable traceBound (-coefficient) 1 (Or.inr one_ne_zero)

end
end P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D
end JanusFormal
