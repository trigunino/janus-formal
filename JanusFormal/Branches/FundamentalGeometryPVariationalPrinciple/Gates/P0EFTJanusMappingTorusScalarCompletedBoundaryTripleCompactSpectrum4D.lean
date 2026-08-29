import Mathlib.Analysis.InnerProductSpace.Spectrum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

/-!
# Compact spectrum directly on a completed scalar boundary triple

A compact ambient resolvent of the direct completed Lagrangian realization is a
compact symmetric endomorphism of the physical Hilbert space.  The standard
compact spectral theorem therefore applies without passing through a second
closed-graph presentation.

Compactness may be supplied directly or obtained by composing the bounded
resolvent with a compact inclusion of the completed Lagrangian domain.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Compact bounded direct resolvent. -/
structure LagrangianCompactResolventAt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  bounded : triple.LagrangianBoundedResolventAt
    condition spectralParameter
  compact_ambient : IsCompactOperator
    (bounded.ambientResolvent triple condition spectralParameter)

/-- Symmetry of the compact ambient resolvent. -/
theorem LagrangianCompactResolventAt.ambient_isSymmetric
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition spectralParameter) :
    (compact.bounded.ambientResolvent
      triple condition spectralParameter).toLinearMap.IsSymmetric :=
  compact.bounded.ambient_isSymmetric triple condition spectralParameter

/-- Fredholm alternative for the direct compact ambient resolvent. -/
theorem LagrangianCompactResolventAt.fredholmAlternative
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0) :
    HasEigenvalue
        ((compact.bounded.ambientResolvent
          triple condition spectralParameter : Ambient →L[Real] Ambient) :
          Module.End Real Ambient)
        eigenvalue ∨
      eigenvalue ∈ resolventSet Real
        (compact.bounded.ambientResolvent
          triple condition spectralParameter) :=
  compact.compact_ambient.hasEigenvalue_or_mem_resolventSet hEigenvalue

/-- Nonzero resolvent eigenspaces are finite dimensional. -/
theorem LagrangianCompactResolventAt.finiteDimensional_eigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0) :
    FiniteDimensional Real
      (Module.End.eigenspace
        (compact.bounded.ambientResolvent
          triple condition spectralParameter).toLinearMap eigenvalue) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    compact.compact_ambient eigenvalue hEigenvalue

/-- Spectral completeness of the compact symmetric ambient resolvent. -/
theorem LagrangianCompactResolventAt.spectral_complete
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition spectralParameter) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        (compact.bounded.ambientResolvent
          triple condition spectralParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    compact.compact_ambient
    (compact.ambient_isSymmetric triple condition spectralParameter)

/-- Coercive direct inverse plus compact domain inclusion. -/
structure LagrangianCoerciveCompactEmbeddingAt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  coercive : triple.LagrangianCoerciveSurjectiveAt
    condition spectralParameter
  compact_inclusion : IsCompactOperator
    (triple.lagrangianInclusion condition)

/-- The coercively constructed direct ambient resolvent is compact. -/
theorem LagrangianCoerciveCompactEmbeddingAt.compact_ambientResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compactData : triple.LagrangianCoerciveCompactEmbeddingAt
      condition spectralParameter) :
    IsCompactOperator
      ((compactData.coercive.boundedResolvent
        triple condition spectralParameter).ambientResolvent
          triple condition spectralParameter) := by
  change IsCompactOperator
    ((triple.lagrangianInclusion condition).comp
      (compactData.coercive.boundedResolvent
        triple condition spectralParameter).resolvent)
  exact compactData.compact_inclusion.comp_clm
    (compactData.coercive.boundedResolvent
      triple condition spectralParameter).resolvent

/-- Compact resolvent generated by coercivity and compact inclusion. -/
noncomputable def LagrangianCoerciveCompactEmbeddingAt.compactResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compactData : triple.LagrangianCoerciveCompactEmbeddingAt
      condition spectralParameter) :
    triple.LagrangianCompactResolventAt condition spectralParameter where
  bounded := compactData.coercive.boundedResolvent
    triple condition spectralParameter
  compact_ambient := compactData.compact_ambientResolvent
    triple condition spectralParameter

/-- Direct compact-spectrum certificate. -/
theorem directLagrangianCompactSpectrum_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (compact : triple.LagrangianCompactResolventAt
      condition spectralParameter) :
    (compact.bounded.ambientResolvent
        triple condition spectralParameter).toLinearMap.IsSymmetric ∧
      IsCompactOperator
        (compact.bounded.ambientResolvent
          triple condition spectralParameter) ∧
      (⨆ eigenvalue : Real,
        Module.End.eigenspace
          (compact.bounded.ambientResolvent
            triple condition spectralParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  ⟨compact.ambient_isSymmetric triple condition spectralParameter,
    compact.compact_ambient,
    compact.spectral_complete triple condition spectralParameter⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
