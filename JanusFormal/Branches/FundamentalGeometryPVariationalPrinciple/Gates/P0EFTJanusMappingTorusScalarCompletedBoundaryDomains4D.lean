import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D

/-!
# Closed completed scalar boundary domains

The graph completion from the preceding file carries a continuous, surjective
paired Hilbert trace.  This file pulls the closed Lagrangian separated trace
spaces back to closed graph domains.

For Dirichlet, Neumann and constant real Robin data it proves:

* closedness of the completed graph domain;
* agreement with the algebraic condition on the dense core;
* vanishing of the completed Green boundary form;
* symmetry of the restricted graph operator;
* equality with the completed boundary-adjoint domain.

The final adjoint theorem remains an exact interface: an actual unbounded
Hilbert adjoint must still be identified with the displayed boundary test.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Pullback of a completed separated Hilbert trace subspace to the closed
operator graph. -/
def canonicalScalarCompletedSeparatedDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    Submodule Real (CanonicalScalarOperatorGraphSpace data) :=
  LinearMap.ker
    ((canonicalScalarHilbertBoundaryConstraint (Trace := Trace) a b).comp
      (canonicalScalarCompletedBoundaryTrace data traceBound)).toLinearMap

@[simp] theorem mem_canonicalScalarCompletedSeparatedDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (field : CanonicalScalarOperatorGraphSpace data) :
    field ∈ canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b ↔
      a • (canonicalScalarCompletedBoundaryTrace data traceBound field).1 +
        b • (canonicalScalarCompletedBoundaryTrace data traceBound field).2 = 0 := by
  rfl

/-- Every completed separated graph domain is closed. -/
theorem canonicalScalarCompletedSeparatedDomainSubmodule_isClosed
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    IsClosed
      (canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b : Set (CanonicalScalarOperatorGraphSpace data)) := by
  let constraint :=
    (canonicalScalarHilbertBoundaryConstraint (Trace := Trace) a b).comp
      (canonicalScalarCompletedBoundaryTrace data traceBound)
  change IsClosed {field | constraint field = 0}
  exact isClosed_singleton.preimage constraint.continuous

/-- On the dense algebraic core, completed separated membership is exactly the
original Hilbert trace equation. -/
theorem canonicalScalarSmooth_mem_completedSeparated_iff
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (field : Domain) :
    canonicalScalarSmoothToOperatorGraphLinearMap data field ∈
        canonicalScalarCompletedSeparatedDomainSubmodule data traceBound a b ↔
      a • (data.boundaryTrace field).1 + b • (data.boundaryTrace field).2 = 0 := by
  rw [mem_canonicalScalarCompletedSeparatedDomainSubmodule,
    canonicalScalarCompletedBoundaryTrace_agrees_on_smooth]

/-- Completed Dirichlet graph domain. -/
def canonicalScalarCompletedDirichletDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Submodule Real (CanonicalScalarOperatorGraphSpace data) :=
  canonicalScalarCompletedSeparatedDomainSubmodule data traceBound 1 0

/-- Completed Neumann graph domain. -/
def canonicalScalarCompletedNeumannDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Submodule Real (CanonicalScalarOperatorGraphSpace data) :=
  canonicalScalarCompletedSeparatedDomainSubmodule data traceBound 0 1

/-- Completed constant real Robin graph domain. -/
def canonicalScalarCompletedRobinDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real) :
    Submodule Real (CanonicalScalarOperatorGraphSpace data) :=
  canonicalScalarCompletedSeparatedDomainSubmodule
    data traceBound (-coefficient) 1

@[simp] theorem mem_canonicalScalarCompletedDirichletDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    field ∈ canonicalScalarCompletedDirichletDomainSubmodule data traceBound ↔
      canonicalScalarCompletedValueTrace data traceBound field = 0 := by
  unfold canonicalScalarCompletedDirichletDomainSubmodule
  rw [mem_canonicalScalarCompletedSeparatedDomainSubmodule]
  change
    (1 : Real) • (canonicalScalarCompletedBoundaryTrace data traceBound field).1 +
          (0 : Real) • (canonicalScalarCompletedBoundaryTrace data traceBound field).2 = 0 ↔
      (canonicalScalarCompletedBoundaryTrace data traceBound field).1 = 0
  simp

@[simp] theorem mem_canonicalScalarCompletedNeumannDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    field ∈ canonicalScalarCompletedNeumannDomainSubmodule data traceBound ↔
      canonicalScalarCompletedNormalTrace data traceBound field = 0 := by
  unfold canonicalScalarCompletedNeumannDomainSubmodule
  rw [mem_canonicalScalarCompletedSeparatedDomainSubmodule]
  change
    (0 : Real) • (canonicalScalarCompletedBoundaryTrace data traceBound field).1 +
          (1 : Real) • (canonicalScalarCompletedBoundaryTrace data traceBound field).2 = 0 ↔
      (canonicalScalarCompletedBoundaryTrace data traceBound field).2 = 0
  simp

@[simp] theorem mem_canonicalScalarCompletedRobinDomainSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real) (field : CanonicalScalarOperatorGraphSpace data) :
    field ∈ canonicalScalarCompletedRobinDomainSubmodule
        data traceBound coefficient ↔
      canonicalScalarCompletedNormalTrace data traceBound field =
        coefficient • canonicalScalarCompletedValueTrace data traceBound field := by
  unfold canonicalScalarCompletedRobinDomainSubmodule
  rw [mem_canonicalScalarCompletedSeparatedDomainSubmodule]
  change
    (-coefficient) • (canonicalScalarCompletedBoundaryTrace data traceBound field).1 +
          (1 : Real) • (canonicalScalarCompletedBoundaryTrace data traceBound field).2 = 0 ↔
      (canonicalScalarCompletedBoundaryTrace data traceBound field).2 =
        coefficient • (canonicalScalarCompletedBoundaryTrace data traceBound field).1
  simp only [one_smul]
  constructor
  · intro h
    have hSub :
        (canonicalScalarCompletedBoundaryTrace data traceBound field).2 -
            coefficient •
              (canonicalScalarCompletedBoundaryTrace data traceBound field).1 = 0 := by
      calc
        (canonicalScalarCompletedBoundaryTrace data traceBound field).2 -
              coefficient •
                (canonicalScalarCompletedBoundaryTrace data traceBound field).1 =
            (-coefficient) •
                (canonicalScalarCompletedBoundaryTrace data traceBound field).1 +
              (canonicalScalarCompletedBoundaryTrace data traceBound field).2 := by
                module
        _ = 0 := h
    exact sub_eq_zero.mp hSub
  · intro h
    rw [h]
    module

/-- The completed trace of a completed separated-domain vector lies in the
corresponding closed Lagrangian trace subspace. -/
theorem canonicalScalarCompletedBoundaryTrace_mem_separated
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (field : CanonicalScalarOperatorGraphSpace data)
    (hField : field ∈ canonicalScalarCompletedSeparatedDomainSubmodule
      data traceBound a b) :
    canonicalScalarCompletedBoundaryTrace data traceBound field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := Trace) a b := by
  exact hField

/-- The completed boundary Green pairing vanishes on every common separated
domain. -/
theorem canonicalScalarCompletedBoundaryGreenPairing_eq_zero_of_separated
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (first second : CanonicalScalarOperatorGraphSpace data)
    (hFirst : first ∈ canonicalScalarCompletedSeparatedDomainSubmodule
      data traceBound a b)
    (hSecond : second ∈ canonicalScalarCompletedSeparatedDomainSubmodule
      data traceBound a b) :
    canonicalScalarCompletedBoundaryGreenPairing
      data traceBound first second = 0 := by
  unfold canonicalScalarCompletedBoundaryGreenPairing
  rw [canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_separated
    (Trace := Trace) a b hNondegenerate
      (canonicalScalarCompletedBoundaryTrace data traceBound first)
      (canonicalScalarCompletedBoundaryTrace data traceBound second)
      (canonicalScalarCompletedBoundaryTrace_mem_separated
        data traceBound a b first hFirst)
      (canonicalScalarCompletedBoundaryTrace_mem_separated
        data traceBound a b second hSecond)]
  ring

/-- Inclusion restricted to a completed separated domain. -/
def canonicalScalarCompletedSeparatedDomainInclusion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b →L[Real] Ambient :=
  (canonicalScalarOperatorGraphInclusion data).comp
    (canonicalScalarCompletedSeparatedDomainSubmodule
      data traceBound a b).subtypeL

/-- Operator restricted to a completed separated domain. -/
def canonicalScalarCompletedSeparatedDomainOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) :
    canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b →L[Real] Ambient :=
  (canonicalScalarOperatorGraphOperator data).comp
    (canonicalScalarCompletedSeparatedDomainSubmodule
      data traceBound a b).subtypeL

/-- Every completed nondegenerate separated domain is symmetric. -/
theorem canonicalScalarCompletedSeparatedDomainOperator_symmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (first second : canonicalScalarCompletedSeparatedDomainSubmodule
      data traceBound a b) :
    inner Real
        (canonicalScalarCompletedSeparatedDomainOperator
          data traceBound a b first)
        (canonicalScalarCompletedSeparatedDomainInclusion
          data traceBound a b second) =
      inner Real
        (canonicalScalarCompletedSeparatedDomainInclusion
          data traceBound a b first)
        (canonicalScalarCompletedSeparatedDomainOperator
          data traceBound a b second) := by
  have hBoundary :=
    canonicalScalarCompletedBoundaryGreenPairing_eq_zero_of_separated
      data traceBound a b hNondegenerate first.1 second.1 first.2 second.2
  have hGreen := canonicalScalarCompletedGreenIdentity
    data traceBound first.1 second.1
  rw [hBoundary] at hGreen
  change inner Real
      (canonicalScalarOperatorGraphOperator data first.1)
      (canonicalScalarOperatorGraphInclusion data second.1) =
    inner Real
      (canonicalScalarOperatorGraphInclusion data first.1)
      (canonicalScalarOperatorGraphOperator data second.1)
  linarith

/-- Completed boundary-adjoint admissibility against a separated graph domain. -/
def canonicalScalarCompletedBoundaryAdjointAdmissible
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (candidate : CanonicalScalarOperatorGraphSpace data) : Prop :=
  ∀ test : canonicalScalarCompletedSeparatedDomainSubmodule
      data traceBound a b,
    canonicalScalarHilbertBoundarySymplecticForm
      (canonicalScalarCompletedBoundaryTrace data traceBound candidate)
      (canonicalScalarCompletedBoundaryTrace data traceBound test.1) = 0

/-- Completed formal boundary-adjoint domain. -/
def canonicalScalarCompletedBoundaryAdjointDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) : Set (CanonicalScalarOperatorGraphSpace data) :=
  {candidate |
    canonicalScalarCompletedBoundaryAdjointAdmissible
      data traceBound a b candidate}

/-- Surjectivity of the completed trace and Hilbert Lagrangian maximality identify
completed boundary-adjoint candidates exactly with the separated domain. -/
theorem canonicalScalarCompletedBoundaryAdjointAdmissible_iff_mem
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (candidate : CanonicalScalarOperatorGraphSpace data) :
    canonicalScalarCompletedBoundaryAdjointAdmissible
        data traceBound a b candidate ↔
      candidate ∈ canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b := by
  constructor
  · intro hCandidate
    have hOrthogonal :
        canonicalScalarCompletedBoundaryTrace data traceBound candidate ∈
          canonicalScalarHilbertBoundarySymplecticOrthogonal
            (canonicalScalarHilbertSeparatedBoundarySubmodule
              (Trace := Trace) a b) := by
      intro testBoundary hTestBoundary
      obtain ⟨test, hTrace⟩ :=
        canonicalScalarCompletedBoundaryTrace_surjective
          data traceBound testBoundary
      have hTestDomain : test ∈
          canonicalScalarCompletedSeparatedDomainSubmodule
            data traceBound a b := by
        change canonicalScalarHilbertBoundaryConstraint
          (Trace := Trace) a b
          (canonicalScalarCompletedBoundaryTrace data traceBound test) = 0
        rw [hTrace]
        exact hTestBoundary
      have hApplied := hCandidate ⟨test, hTestDomain⟩
      rw [hTrace] at hApplied
      exact hApplied
    have hSeparated :
        canonicalScalarCompletedBoundaryTrace data traceBound candidate ∈
          canonicalScalarHilbertSeparatedBoundarySubmodule
            (Trace := Trace) a b := by
      rw [← canonicalScalarHilbertSeparatedBoundarySubmodule_orthogonal_eq
        (Trace := Trace) a b hNondegenerate]
      exact hOrthogonal
    exact hSeparated
  · intro hCandidate test
    exact canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_separated
      (Trace := Trace) a b hNondegenerate
      (canonicalScalarCompletedBoundaryTrace data traceBound candidate)
      (canonicalScalarCompletedBoundaryTrace data traceBound test.1)
      (canonicalScalarCompletedBoundaryTrace_mem_separated
        data traceBound a b candidate hCandidate)
      (canonicalScalarCompletedBoundaryTrace_mem_separated
        data traceBound a b test.1 test.2)

/-- Completed separated domain equals its boundary-adjoint domain. -/
theorem canonicalScalarCompletedBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    canonicalScalarCompletedBoundaryAdjointDomain data traceBound a b =
      (canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b : Set (CanonicalScalarOperatorGraphSpace data)) := by
  ext candidate
  exact canonicalScalarCompletedBoundaryAdjointAdmissible_iff_mem
    data traceBound a b hNondegenerate candidate

/-- Analytic interface identifying a future actual Hilbert adjoint domain with
the completed Green boundary test. -/
structure CanonicalScalarCompletedAdjointBoundaryCharacterization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) where
  adjointDomain : Set (CanonicalScalarOperatorGraphSpace data)
  mem_adjointDomain_iff : ∀ candidate,
    candidate ∈ adjointDomain ↔
      canonicalScalarCompletedBoundaryAdjointAdmissible
        data traceBound a b candidate

/-- Once the genuine Hilbert adjoint is characterized by the completed boundary
test, maximal Lagrangianity gives equality of adjoint and original domains. -/
theorem CanonicalScalarCompletedAdjointBoundaryCharacterization.adjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (characterization : CanonicalScalarCompletedAdjointBoundaryCharacterization
      data traceBound a b) :
    characterization.adjointDomain =
      (canonicalScalarCompletedSeparatedDomainSubmodule
        data traceBound a b : Set (CanonicalScalarOperatorGraphSpace data)) := by
  ext candidate
  rw [characterization.mem_adjointDomain_iff]
  exact canonicalScalarCompletedBoundaryAdjointAdmissible_iff_mem
    data traceBound a b hNondegenerate candidate

/-- Dirichlet completed boundary-adjoint maximality. -/
theorem canonicalScalarCompletedDirichletBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    canonicalScalarCompletedBoundaryAdjointDomain data traceBound 1 0 =
      (canonicalScalarCompletedDirichletDomainSubmodule data traceBound :
        Set (CanonicalScalarOperatorGraphSpace data)) := by
  exact canonicalScalarCompletedBoundaryAdjointDomain_eq
    data traceBound 1 0 (Or.inl one_ne_zero)

/-- Neumann completed boundary-adjoint maximality. -/
theorem canonicalScalarCompletedNeumannBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    canonicalScalarCompletedBoundaryAdjointDomain data traceBound 0 1 =
      (canonicalScalarCompletedNeumannDomainSubmodule data traceBound :
        Set (CanonicalScalarOperatorGraphSpace data)) := by
  exact canonicalScalarCompletedBoundaryAdjointDomain_eq
    data traceBound 0 1 (Or.inr one_ne_zero)

/-- Constant real Robin completed boundary-adjoint maximality. -/
theorem canonicalScalarCompletedRobinBoundaryAdjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real) :
    canonicalScalarCompletedBoundaryAdjointDomain
        data traceBound (-coefficient) 1 =
      (canonicalScalarCompletedRobinDomainSubmodule
        data traceBound coefficient :
          Set (CanonicalScalarOperatorGraphSpace data)) := by
  exact canonicalScalarCompletedBoundaryAdjointDomain_eq
    data traceBound (-coefficient) 1 (Or.inr one_ne_zero)

/-- Full completed-domain closure certificate. -/
theorem canonicalScalarCompletedBoundaryDomains_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    IsClosed
        (canonicalScalarCompletedSeparatedDomainSubmodule
          data traceBound a b : Set (CanonicalScalarOperatorGraphSpace data)) ∧
      (∀ first second : canonicalScalarCompletedSeparatedDomainSubmodule
          data traceBound a b,
        inner Real
            (canonicalScalarCompletedSeparatedDomainOperator
              data traceBound a b first)
            (canonicalScalarCompletedSeparatedDomainInclusion
              data traceBound a b second) =
          inner Real
            (canonicalScalarCompletedSeparatedDomainInclusion
              data traceBound a b first)
            (canonicalScalarCompletedSeparatedDomainOperator
              data traceBound a b second)) ∧
      canonicalScalarCompletedBoundaryAdjointDomain data traceBound a b =
        (canonicalScalarCompletedSeparatedDomainSubmodule
          data traceBound a b : Set (CanonicalScalarOperatorGraphSpace data)) := by
  exact ⟨canonicalScalarCompletedSeparatedDomainSubmodule_isClosed
      data traceBound a b,
    canonicalScalarCompletedSeparatedDomainOperator_symmetric
      data traceBound a b hNondegenerate,
    canonicalScalarCompletedBoundaryAdjointDomain_eq
      data traceBound a b hNondegenerate⟩

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D
end JanusFormal
