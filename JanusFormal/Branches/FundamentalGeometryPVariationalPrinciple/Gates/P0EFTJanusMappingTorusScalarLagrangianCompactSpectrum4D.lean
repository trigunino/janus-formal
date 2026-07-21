import Mathlib.Analysis.InnerProductSpace.Spectrum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianResolvent4D

/-!
# Compact spectral theory for arbitrary scalar Lagrangian boundaries

This gate applies compact self-adjoint spectral theory to the bounded ambient
resolvent of an arbitrary closed Lagrangian boundary realization.  It includes
Dirichlet, Neumann, all nondegenerate separated conditions, and every bounded
symmetric operator-valued Robin graph.

The analytic compactness input can be supplied directly or derived from a
compact embedding of the Lagrangian operator domain together with the coercive
inverse estimate constructed in the preceding gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Compact bounded resolvent for an arbitrary Lagrangian boundary condition. -/
structure CanonicalScalarClosedLagrangianCompactResolventAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
    data hClosable traceBound condition spectralParameter
  compact_ambient : IsCompactOperator
    (bounded.ambientResolvent
      data hClosable traceBound condition spectralParameter)

/-- Symmetry of a compact Lagrangian ambient resolvent. -/
theorem CanonicalScalarClosedLagrangianCompactResolventAt.ambient_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition spectralParameter) :
    (compact.bounded.ambientResolvent
      data hClosable traceBound condition spectralParameter).toLinearMap.IsSymmetric :=
  canonicalScalarClosedLagrangianAmbientResolvent_isSymmetric
    data hClosable traceBound condition spectralParameter compact.bounded

/-- Fredholm alternative for the compact ambient resolvent. -/
theorem CanonicalScalarClosedLagrangianCompactResolventAt.fredholmAlternative
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0) :
    HasEigenvalue
        ((compact.bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter :
            Ambient →L[Real] Ambient) : Module.End Real Ambient)
        eigenvalue ∨
      eigenvalue ∈ resolventSet Real
        (compact.bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter) :=
  compact.compact_ambient.hasEigenvalue_or_mem_resolventSet hEigenvalue

/-- Nonzero eigenspaces of a compact Lagrangian ambient resolvent are finite
dimensional. -/
theorem CanonicalScalarClosedLagrangianCompactResolventAt.finiteDimensional_eigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0) :
    FiniteDimensional Real
      (Module.End.eigenspace
        (compact.bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter).toLinearMap
        eigenvalue) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    compact.compact_ambient eigenvalue hEigenvalue

/-- Spectral completeness of the compact symmetric ambient resolvent. -/
theorem CanonicalScalarClosedLagrangianCompactResolventAt.spectral_complete
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition spectralParameter) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        (compact.bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter).toLinearMap
        eigenvalue)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    compact.compact_ambient
    (compact.ambient_isSymmetric
      data hClosable traceBound condition spectralParameter)

/-- A nonzero ambient resolvent eigenvector reconstructs an eigenfield of the
original Lagrangian closed operator. -/
theorem canonicalScalarClosedLagrangianResolvent_eigenvector_transfer
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (bounded : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0)
    (vector : Ambient)
    (hVector :
      bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter vector =
        eigenvalue • vector) :
    let field : canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :=
      eigenvalue⁻¹ • bounded.resolvent vector
    canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field = vector ∧
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        (spectralParameter + eigenvalue⁻¹) • vector := by
  let field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition :=
    eigenvalue⁻¹ • bounded.resolvent vector
  have hInclusion :
      canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field = vector := by
    dsimp [field]
    rw [map_smul]
    change eigenvalue⁻¹ •
        (bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter vector) = vector
    rw [hVector, smul_smul]
    simp [hEigenvalue]
  have hShifted :
      canonicalScalarClosedLagrangianShiftedOperator
          data hClosable traceBound condition spectralParameter field =
        eigenvalue⁻¹ • vector := by
    change canonicalScalarClosedLagrangianShiftedOperator
        data hClosable traceBound condition spectralParameter
          (eigenvalue⁻¹ • bounded.resolvent vector) = _
    rw [map_smul, bounded.left_inverse]
  refine ⟨hInclusion, ?_⟩
  have hExpanded := canonicalScalarClosedLagrangianShiftedOperator_apply
    data hClosable traceBound condition spectralParameter field
  rw [hShifted, hInclusion] at hExpanded
  change eigenvalue⁻¹ • vector =
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field -
        spectralParameter • vector at hExpanded
  have hAdded := congrArg (fun value => value + spectralParameter • vector)
    hExpanded
  simpa [field, map_smul, add_smul, add_assoc, add_comm, add_left_comm,
    hInclusion] using hAdded.symm

/-- Compact embedding plus coercive-surjective inverse data. -/
structure CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  coercive : CanonicalScalarClosedLagrangianCoerciveSurjectiveAt
    data hClosable traceBound condition spectralParameter
  compact_inclusion : IsCompactOperator
    (canonicalScalarClosedLagrangianDomainInclusionCLM
      data hClosable traceBound condition)

/-- The coercively constructed ambient resolvent is compact whenever the domain
inclusion is compact. -/
theorem CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt.compact_ambientResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compactData : CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt
      data hClosable traceBound condition spectralParameter) :
    IsCompactOperator
      ((compactData.coercive.boundedResolvent
        data hClosable traceBound condition spectralParameter).ambientResolvent
          data hClosable traceBound condition spectralParameter) := by
  change IsCompactOperator
    ((canonicalScalarClosedLagrangianDomainInclusionCLM
      data hClosable traceBound condition).comp
      (compactData.coercive.boundedResolvent
        data hClosable traceBound condition spectralParameter).resolvent)
  exact compactData.compact_inclusion.comp_clm
    (compactData.coercive.boundedResolvent
      data hClosable traceBound condition spectralParameter).resolvent

/-- Canonical compact-resolvent package derived from coercivity and compact
embedding. -/
noncomputable def CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt.compactResolvent
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compactData : CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt
      data hClosable traceBound condition spectralParameter) :
    CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition spectralParameter where
  bounded := compactData.coercive.boundedResolvent
    data hClosable traceBound condition spectralParameter
  compact_ambient := compactData.compact_ambientResolvent
    data hClosable traceBound condition spectralParameter

/-- Full abstract Lagrangian compact-spectrum certificate. -/
theorem canonicalScalarLagrangianCompactSpectrum_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : CanonicalScalarClosedLagrangianCompactResolventAt
      data hClosable traceBound condition spectralParameter) :
    (compact.bounded.ambientResolvent
        data hClosable traceBound condition spectralParameter).toLinearMap.IsSymmetric ∧
      IsCompactOperator
        (compact.bounded.ambientResolvent
          data hClosable traceBound condition spectralParameter) ∧
      (∀ eigenvalue : Real, eigenvalue ≠ 0 →
        FiniteDimensional Real
          (Module.End.eigenspace
            (compact.bounded.ambientResolvent
              data hClosable traceBound condition spectralParameter).toLinearMap
            eigenvalue)) ∧
      (⨆ eigenvalue : Real,
        Module.End.eigenspace
          (compact.bounded.ambientResolvent
            data hClosable traceBound condition spectralParameter).toLinearMap
          eigenvalue)ᗮ = ⊥ := by
  exact ⟨compact.ambient_isSymmetric
      data hClosable traceBound condition spectralParameter,
    compact.compact_ambient,
    compact.finiteDimensional_eigenspace
      data hClosable traceBound condition spectralParameter,
    CanonicalScalarClosedLagrangianCompactResolventAt.spectral_complete
      data hClosable traceBound condition spectralParameter compact⟩

end
end P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
end JanusFormal
