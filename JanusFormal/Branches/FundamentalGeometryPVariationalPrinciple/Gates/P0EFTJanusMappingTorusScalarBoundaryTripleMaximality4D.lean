import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarSeparatedBoundaryLagrangian4D

/-!
# Boundary-triple maximality for separated scalar domains

This file isolates the exact abstract step needed after the global Green--Stokes
theorem and the Lagrangian classification of separated boundary lines.

A `CanonicalScalarGlobalGreenSystem` consists of a linear operator on an
algebraic domain, its inclusion into a real inner-product ambient space, a
surjective boundary trace, and the exact Green identity.  Restricting the
operator to a nondegenerate separated boundary section gives:

* symmetry of the restricted operator;
* equality of the separated domain with its pointwise boundary-adjoint domain;
* an immediate self-adjoint-domain conclusion for any future analytic adjoint
  characterization whose boundary term is the one supplied here.

The last item is intentionally an interface theorem.  It does not manufacture
closedness, density or an unbounded Hilbert adjoint.  Once such an analytic
realization identifies its adjoint domain by the displayed Green boundary
condition, maximal Lagrangianity closes the domain equality automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarBoundaryTripleMaximality4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusScalarBoundarySymplecticPlane4D
open P0EFTJanusMappingTorusScalarSeparatedBoundaryLagrangian4D

variable (period : Real) (hPeriod : period ≠ 0)
include hPeriod

universe u v

variable {Domain : Type u} {Ambient : Type v}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]

/-- Abstract global Green system with the exact canonical scalar boundary
pairing.  Surjectivity is the boundary-triple hypothesis that every boundary
section can be tested by a domain element. -/
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

/-- Pullback of a separated Lagrangian boundary section space to the operator
domain. -/
def canonicalScalarSeparatedGreenDomainSubmodule
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    Submodule Real Domain :=
  (canonicalScalarSeparatedBoundarySectionSubmodule
    valueCoefficient normalCoefficient).comap system.boundary

@[simp] theorem mem_canonicalScalarSeparatedGreenDomainSubmodule
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
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
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient →ₗ[Real] Ambient :=
  system.inclusion.comp
    (canonicalScalarSeparatedGreenDomainSubmodule
      system valueCoefficient normalCoefficient).subtype

/-- Operator restricted to a separated Green domain. -/
def canonicalScalarSeparatedGreenDomainOperator
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
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
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
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
          valueCoefficient normalCoefficient := by
    exact first.2
  have hSecondBoundary :
      system.boundary second.1 ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient := by
    exact second.2
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
separated Green restriction.  This is exactly the boundary term left after
testing against every vector in the restricted domain. -/
def canonicalScalarSeparatedBoundaryAdjointAdmissible
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (candidate : Domain) : Prop :=
  ∀ test : canonicalScalarSeparatedGreenDomainSubmodule
      system valueCoefficient normalCoefficient,
    ∀ base : CanonicalLatitudeBase,
      canonicalScalarBoundarySymplecticForm
        (system.boundary candidate base)
        (system.boundary test.1 base) = 0

/-- The formal boundary-adjoint domain as a concrete set of original domain
vectors. -/
def canonicalScalarSeparatedBoundaryAdjointDomain
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) :
    Set Domain :=
  {candidate |
    canonicalScalarSeparatedBoundaryAdjointAdmissible
      system valueCoefficient normalCoefficient candidate}

/-- Surjectivity of the boundary trace plus maximal Lagrangianity identifies the
boundary-adjoint candidates exactly with the separated domain. -/
theorem canonicalScalarSeparatedBoundaryAdjointAdmissible_iff_mem
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
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
    change (∀ test : canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient,
      ∀ base : CanonicalLatitudeBase,
        canonicalScalarBoundarySymplecticForm
          (system.boundary candidate base)
          (system.boundary test.1 base) = 0) at hCandidate
    change system.boundary candidate ∈
      canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient
    apply canonicalScalarBoundarySectionPointwiseOrthogonal_le_separated
      valueCoefficient normalCoefficient
    intro testSection hTestSection base
    obtain ⟨test, hTrace⟩ := system.boundary_surjective testSection
    have hTestDomain : test ∈ canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient := by
      change system.boundary test ∈
        canonicalScalarSeparatedBoundarySectionSubmodule
          valueCoefficient normalCoefficient
      rw [hTrace]
      exact hTestSection
    have hApplied := hCandidate ⟨test, hTestDomain⟩ base
    rw [hTrace] at hApplied
    exact hApplied
  · intro hCandidate
    change system.boundary candidate ∈
      canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient at hCandidate
    change ∀ test : canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient,
      ∀ base : CanonicalLatitudeBase,
        canonicalScalarBoundarySymplecticForm
          (system.boundary candidate base)
          (system.boundary test.1 base) = 0
    intro test base
    have hTestBoundary :
        system.boundary test.1 ∈
          canonicalScalarSeparatedBoundarySectionSubmodule
            valueCoefficient normalCoefficient := by
      exact test.2
    have hCandidateBase :=
      (mem_canonicalScalarSeparatedBoundarySectionSubmodule
        valueCoefficient normalCoefficient (system.boundary candidate)).1
          hCandidate base
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

/-- The separated domain equals its boundary-adjoint domain.  This is the exact
maximal formal-symmetry statement supplied by the boundary triple. -/
theorem canonicalScalarSeparatedBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
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
    period hPeriod system valueCoefficient normalCoefficient
      hNondegenerate candidate

/-- Analytic interface for a future closed unbounded realization.  Its actual
adjoint domain must be characterized by the canonical boundary-adjoint test.
No such characterization is silently assumed by the algebraic Green system. -/
structure CanonicalScalarAdjointBoundaryCharacterization
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) where
  adjointDomain : Set Domain
  mem_adjointDomain_iff : ∀ candidate : Domain,
    candidate ∈ adjointDomain ↔
      canonicalScalarSeparatedBoundaryAdjointAdmissible
        system valueCoefficient normalCoefficient candidate

/-- Once an analytic operator proves the preceding adjoint characterization,
maximal Lagrangianity gives equality of its adjoint and original domains. -/
theorem CanonicalScalarAdjointBoundaryCharacterization.adjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient))
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : ∀ base,
      valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0)
    (characterization : CanonicalScalarAdjointBoundaryCharacterization
      period hPeriod system valueCoefficient normalCoefficient) :
    characterization.adjointDomain =
      (canonicalScalarSeparatedGreenDomainSubmodule
        system valueCoefficient normalCoefficient : Set Domain) := by
  ext candidate
  rw [characterization.mem_adjointDomain_iff]
  exact canonicalScalarSeparatedBoundaryAdjointAdmissible_iff_mem
    period hPeriod system valueCoefficient normalCoefficient
      hNondegenerate candidate

/-- Dirichlet specialization of boundary-adjoint maximality. -/
theorem canonicalScalarDirichletBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient)) :
    canonicalScalarSeparatedBoundaryAdjointDomain system
        (fun _ => 1) (fun _ => 0) =
      (canonicalScalarSeparatedGreenDomainSubmodule system
        (fun _ => 1) (fun _ => 0) : Set Domain) := by
  apply canonicalScalarSeparatedBoundaryAdjointDomain_eq
  intro base
  exact Or.inl one_ne_zero

/-- Neumann specialization of boundary-adjoint maximality. -/
theorem canonicalScalarNeumannBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient)) :
    canonicalScalarSeparatedBoundaryAdjointDomain system
        (fun _ => 0) (fun _ => 1) =
      (canonicalScalarSeparatedGreenDomainSubmodule system
        (fun _ => 0) (fun _ => 1) : Set Domain) := by
  apply canonicalScalarSeparatedBoundaryAdjointDomain_eq
  intro base
  exact Or.inr one_ne_zero

/-- Arbitrary real variable Robin specialization of boundary-adjoint maximality. -/
theorem canonicalScalarRobinBoundaryAdjointDomain_eq
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
      (Domain := Domain) (Ambient := Ambient))
    (coefficient : CanonicalLatitudeBase → Real) :
    canonicalScalarSeparatedBoundaryAdjointDomain system
        (fun base => -coefficient base) (fun _ => 1) =
      (canonicalScalarSeparatedGreenDomainSubmodule system
        (fun base => -coefficient base) (fun _ => 1) : Set Domain) := by
  apply canonicalScalarSeparatedBoundaryAdjointDomain_eq
  intro base
  exact Or.inr one_ne_zero

/-- Full abstract closure certificate: symmetry and boundary-adjoint maximality
of every nondegenerate separated scalar boundary condition. -/
theorem canonicalScalarSeparatedGreenDomain_maximalSymmetry_certificate
    (system : CanonicalScalarGlobalGreenSystem period hPeriod
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
      period hPeriod system valueCoefficient normalCoefficient hNondegenerate,
    canonicalScalarSeparatedBoundaryAdjointDomain_eq
      period hPeriod system valueCoefficient normalCoefficient hNondegenerate⟩

end
end P0EFTJanusMappingTorusScalarBoundaryTripleMaximality4D
end JanusFormal