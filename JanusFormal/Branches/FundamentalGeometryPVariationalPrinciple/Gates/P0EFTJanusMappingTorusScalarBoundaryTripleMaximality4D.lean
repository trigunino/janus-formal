import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarSeparatedBoundaryLagrangian4D

/-!
# Boundary-triple maximality for separated scalar domains

This file isolates the exact abstract step needed after the global Green--Stokes
theorem and the Lagrangian classification of separated boundary lines.

A `CanonicalScalarGlobalGreenSystem` consists of a linear operator on an
algebraic domain, its inclusion into a real inner-product ambient space, a
surjective boundary trace, and the exact Green identity. Restricting the
operator to a nondegenerate separated boundary section gives symmetry and
maximality with respect to the boundary-adjoint test.

The final adjoint statement remains an interface theorem. It does not
manufacture closedness, density or an unbounded Hilbert adjoint.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarBoundaryTripleMaximality4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusScalarBoundarySymplecticPlane4D
open P0EFTJanusMappingTorusScalarSeparatedBoundaryLagrangian4D

variable (period : Real)

universe u v

variable {Domain : Type u} {Ambient : Type v}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]

/-- Abstract global Green system with the exact canonical scalar boundary
pairing. Surjectivity means that every boundary section can be tested by a
domain element. -/
structure CanonicalScalarGlobalGreenSystem where
  inclusion : Domain →ₗ[Real] Ambient
  operator : Domain →ₗ[Real] Ambient
  boundary : Domain →ₗ[Real] CanonicalScalarBoundarySection
  boundary_surjective : Function.Surjective boundary
  green_identity : ∀ first second : Domain,
    inner Real (operator first) (inclusion second) -
        inner Real (inclusion first) (operator second) =
      canonicalScalarGlobalBoundarySectionGreenPairing period
        (boundary first) (boundary second)

/-- Pullback of a separated Lagrangian boundary-section space to the operator
domain. -/
def canonicalScalarSeparatedGreenDomainSubmodule
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    Submodule Real Domain :=
  (canonicalScalarSeparatedBoundarySectionSubmodule
    valueCoefficient normalCoefficient).comap system.boundary

@[simp] theorem mem_canonicalScalarSeparatedGreenDomainSubmodule
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (field : Domain) :
    field ∈ canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient ↔
      system.boundary field ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient :=
  Iff.rfl

/-- Ambient inclusion restricted to a separated Green domain. -/
def canonicalScalarSeparatedGreenDomainInclusion
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient →ₗ[Real] Ambient :=
  system.inclusion.comp
    (canonicalScalarSeparatedGreenDomainSubmodule
      system valueCoefficient normalCoefficient).subtype

/-- Operator restricted to a separated Green domain. -/
def canonicalScalarSeparatedGreenDomainOperator
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient →ₗ[Real] Ambient :=
  system.operator.comp
    (canonicalScalarSeparatedGreenDomainSubmodule
      system valueCoefficient normalCoefficient).subtype

/-- Every nondegenerate separated Lagrangian boundary condition makes the
restricted Green operator symmetric. -/
theorem canonicalScalarSeparatedGreenDomainOperator_symmetric
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0)
    (first second : canonicalScalarSeparatedGreenDomainSubmodule
      system valueCoefficient normalCoefficient) :
    inner Real
        (canonicalScalarSeparatedGreenDomainOperator
          system valueCoefficient normalCoefficient first)
        (canonicalScalarSeparatedGreenDomainInclusion
          system valueCoefficient normalCoefficient second) =
      inner Real
        (canonicalScalarSeparatedGreenDomainInclusion
          system valueCoefficient normalCoefficient first)
        (canonicalScalarSeparatedGreenDomainOperator
          system valueCoefficient normalCoefficient second) := by
  have hFirstBoundary :
      system.boundary first.1 ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient := first.2
  have hSecondBoundary :
      system.boundary second.1 ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient := second.2
  have hBoundary :
      canonicalScalarGlobalBoundarySectionGreenPairing period
          (system.boundary first.1) (system.boundary second.1) = 0 :=
    canonicalScalarGlobalBoundarySectionGreenPairing_eq_zero_of_mem_separated
      period valueCoefficient normalCoefficient hNondegenerate
        (system.boundary first.1) (system.boundary second.1)
          hFirstBoundary hSecondBoundary
  have hGreen := system.green_identity first.1 second.1
  rw [hBoundary] at hGreen
  change inner Real (system.operator first.1) (system.inclusion second.1) =
    inner Real (system.inclusion first.1) (system.operator second.1)
  linarith

/-- Pointwise boundary condition defining candidates for the adjoint domain of a
separated Green restriction. -/
def canonicalScalarSeparatedBoundaryAdjointAdmissible
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (candidate : Domain) : Prop :=
  ∀ test : canonicalScalarSeparatedGreenDomainSubmodule
      system valueCoefficient normalCoefficient,
    ∀ base : CanonicalLatitudeBase,
      canonicalScalarBoundarySymplecticForm
        (system.boundary candidate base)
        (system.boundary test.1 base) = 0

/-- Formal boundary-adjoint domain as a set of original domain vectors. -/
def canonicalScalarSeparatedBoundaryAdjointDomain
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    Set Domain :=
  {candidate |
    canonicalScalarSeparatedBoundaryAdjointAdmissible
      system valueCoefficient normalCoefficient candidate}

/-- Surjectivity of the boundary trace plus Lagrangian maximality identifies the
boundary-adjoint candidates exactly with the separated domain. -/
theorem canonicalScalarSeparatedBoundaryAdjointAdmissible_iff_mem
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0)
    (candidate : Domain) :
    canonicalScalarSeparatedBoundaryAdjointAdmissible
        system valueCoefficient normalCoefficient candidate ↔
      candidate ∈ canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient := by
  constructor
  · intro hCandidate
    apply (mem_canonicalScalarSeparatedGreenDomainSubmodule
      (period := period) system valueCoefficient normalCoefficient candidate).2
    apply (mem_canonicalScalarSeparatedBoundarySectionSubmodule
      valueCoefficient normalCoefficient (system.boundary candidate)).2
    intro base
    let generator : CanonicalScalarBoundarySection := fun currentBase =>
      canonicalScalarSeparatedBoundaryGenerator
        (valueCoefficient currentBase) (normalCoefficient currentBase)
    have hGenerator : generator ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient := by
      apply (mem_canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient generator).2
      intro currentBase
      change valueCoefficient currentBase * normalCoefficient currentBase +
        normalCoefficient currentBase * (-valueCoefficient currentBase) = 0
      ring
    obtain ⟨test, hTrace⟩ := system.boundary_surjective generator
    have hTestDomain : test ∈ canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient := by
      apply (mem_canonicalScalarSeparatedGreenDomainSubmodule
        (period := period) system valueCoefficient normalCoefficient test).2
      rw [hTrace]
      exact hGenerator
    have hAt := hCandidate ⟨test, hTestDomain⟩ base
    rw [hTrace] at hAt
    change valueCoefficient base * (system.boundary candidate base).1 +
      normalCoefficient base * (system.boundary candidate base).2 = 0
    dsimp [generator, canonicalScalarSeparatedBoundaryGenerator] at hAt
    unfold canonicalScalarBoundarySymplecticForm at hAt
    linarith
  · intro hCandidate test base
    have hCandidateBoundary : system.boundary candidate ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient :=
      (mem_canonicalScalarSeparatedGreenDomainSubmodule
        (period := period) system valueCoefficient normalCoefficient candidate).1
          hCandidate
    have hTestBoundary : system.boundary test.1 ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient :=
      (mem_canonicalScalarSeparatedGreenDomainSubmodule
        (period := period) system valueCoefficient normalCoefficient test.1).1
          test.2
    have hCandidateBase :=
      (mem_canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient (system.boundary candidate)).1
          hCandidateBoundary base
    have hTestBase :=
      (mem_canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient (system.boundary test.1)).1
          hTestBoundary base
    exact canonicalScalarBoundarySymplecticForm_eq_zero_of_mem_separated
      (valueCoefficient base) (normalCoefficient base) (hNondegenerate base)
        (system.boundary candidate base) (system.boundary test.1 base)
        ((mem_canonicalScalarSeparatedBoundaryLine
          (valueCoefficient base) (normalCoefficient base)
            (system.boundary candidate base)).2 hCandidateBase)
        ((mem_canonicalScalarSeparatedBoundaryLine
          (valueCoefficient base) (normalCoefficient base)
            (system.boundary test.1 base)).2 hTestBase)

/-- The separated domain equals its boundary-adjoint domain. -/
theorem canonicalScalarSeparatedBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0) :
    canonicalScalarSeparatedBoundaryAdjointDomain
        system valueCoefficient normalCoefficient =
      (canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient : Set Domain) := by
  ext candidate
  exact canonicalScalarSeparatedBoundaryAdjointAdmissible_iff_mem
    (period := period) system valueCoefficient normalCoefficient
      hNondegenerate candidate

/-- Analytic interface for a future closed unbounded realization. -/
structure CanonicalScalarAdjointBoundaryCharacterization
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) where
  adjointDomain : Set Domain
  mem_adjointDomain_iff : ∀ candidate : Domain,
    candidate ∈ adjointDomain ↔
      canonicalScalarSeparatedBoundaryAdjointAdmissible
        system valueCoefficient normalCoefficient candidate

/-- Once an analytic operator proves the adjoint characterization, maximal
Lagrangianity gives equality of adjoint and original domains. -/
theorem CanonicalScalarAdjointBoundaryCharacterization.adjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0)
    (characterization : CanonicalScalarAdjointBoundaryCharacterization
      period system valueCoefficient normalCoefficient) :
    characterization.adjointDomain =
      (canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient : Set Domain) := by
  ext candidate
  rw [characterization.mem_adjointDomain_iff]
  exact canonicalScalarSeparatedBoundaryAdjointAdmissible_iff_mem
    (period := period) system valueCoefficient normalCoefficient
      hNondegenerate candidate

/-- Dirichlet specialization of boundary-adjoint maximality. -/
theorem canonicalScalarDirichletBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient)) :
    canonicalScalarSeparatedBoundaryAdjointDomain system
        (fun _ => 1) (fun _ => 0) =
      (canonicalScalarSeparatedGreenDomainSubmodule system
        (fun _ => 1) (fun _ => 0) : Set Domain) := by
  apply canonicalScalarSeparatedBoundaryAdjointDomain_eq (period := period)
  intro base
  exact Or.inl one_ne_zero

/-- Neumann specialization of boundary-adjoint maximality. -/
theorem canonicalScalarNeumannBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient)) :
    canonicalScalarSeparatedBoundaryAdjointDomain system
        (fun _ => 0) (fun _ => 1) =
      (canonicalScalarSeparatedGreenDomainSubmodule system
        (fun _ => 0) (fun _ => 1) : Set Domain) := by
  apply canonicalScalarSeparatedBoundaryAdjointDomain_eq (period := period)
  intro base
  exact Or.inr one_ne_zero

/-- Arbitrary real variable Robin specialization. -/
theorem canonicalScalarRobinBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (coefficient : CanonicalLatitudeBase → Real) :
    canonicalScalarSeparatedBoundaryAdjointDomain system
        (fun base => -coefficient base) (fun _ => 1) =
      (canonicalScalarSeparatedGreenDomainSubmodule system
        (fun base => -coefficient base) (fun _ => 1) : Set Domain) := by
  apply canonicalScalarSeparatedBoundaryAdjointDomain_eq (period := period)
  intro base
  exact Or.inr one_ne_zero

/-- Full abstract closure certificate: symmetry and boundary-adjoint maximality
of every nondegenerate separated scalar boundary condition. -/
theorem canonicalScalarSeparatedGreenDomain_maximalSymmetry_certificate
    (system : CanonicalScalarGlobalGreenSystem period
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0) :
    (∀ first second : canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient,
      inner Real
          (canonicalScalarSeparatedGreenDomainOperator
            system valueCoefficient normalCoefficient first)
          (canonicalScalarSeparatedGreenDomainInclusion
            system valueCoefficient normalCoefficient second) =
        inner Real
          (canonicalScalarSeparatedGreenDomainInclusion
            system valueCoefficient normalCoefficient first)
          (canonicalScalarSeparatedGreenDomainOperator
            system valueCoefficient normalCoefficient second)) ∧
      canonicalScalarSeparatedBoundaryAdjointDomain
          system valueCoefficient normalCoefficient =
        (canonicalScalarSeparatedGreenDomainSubmodule
          system valueCoefficient normalCoefficient : Set Domain) := by
  exact ⟨canonicalScalarSeparatedGreenDomainOperator_symmetric
      (period := period) system valueCoefficient normalCoefficient hNondegenerate,
    canonicalScalarSeparatedBoundaryAdjointDomain_eq
      (period := period) system valueCoefficient normalCoefficient hNondegenerate⟩

end
end P0EFTJanusMappingTorusScalarBoundaryTripleMaximality4D
end JanusFormal
