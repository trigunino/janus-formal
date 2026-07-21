import Mathlib.Analysis.InnerProductSpace.Spectrum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarClosedResolvent4D

/-!
# Compact resolvent and spectral package for closed scalar realizations

A bounded inverse of `A - lambda` gives an ambient continuous linear resolvent.
For a nondegenerate separated boundary condition, symmetry of the unbounded
operator implies symmetry of this bounded ambient resolvent.

This file packages compactness of that resolvent and applies Mathlib's compact
self-adjoint spectral theory.  The resulting statements give:

* the Fredholm alternative for every nonzero resolvent eigenvalue;
* finite-dimensional nonzero eigenspaces;
* completeness of the orthogonal sum of eigenspaces;
* an explicit transfer from resolvent eigenvectors back to eigenpairs of the
  original closed operator.

Compactness and bounded inverse estimates remain explicit analytic inputs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompactResolventSpectrum4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarClosedSeparatedRealization4D
open P0EFTJanusMappingTorusScalarClosedResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- The bounded ambient resolvent of a symmetric separated realization is a
symmetric linear endomorphism of the ambient Hilbert space. -/
theorem canonicalScalarClosedAmbientResolvent_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter) :
    (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
      data hClosable traceBound a b spectralParameter bounded).toLinearMap.IsSymmetric := by
  intro source test
  let first := bounded.resolvent source
  let second := bounded.resolvent test
  have hOperatorSymmetric :=
    canonicalScalarClosedSeparatedDomainOperator_symmetric
      data hClosable traceBound a b hNondegenerate first second
  have hShiftedSymmetric :
      inner Real
          (canonicalScalarClosedSeparatedShiftedOperator
            data hClosable traceBound a b spectralParameter first)
          (canonicalScalarClosedSeparatedDomainInclusion
            data hClosable traceBound a b second) =
        inner Real
          (canonicalScalarClosedSeparatedDomainInclusion
            data hClosable traceBound a b first)
          (canonicalScalarClosedSeparatedShiftedOperator
            data hClosable traceBound a b spectralParameter second) := by
    rw [canonicalScalarClosedSeparatedShiftedOperator_apply,
      canonicalScalarClosedSeparatedShiftedOperator_apply,
      inner_sub_left, inner_sub_right, hOperatorSymmetric]
    simp only [real_inner_smul_left, real_inner_smul_right]
  rw [bounded.left_inverse source, bounded.left_inverse test] at hShiftedSymmetric
  change inner Real
      (canonicalScalarClosedSeparatedDomainInclusion
        data hClosable traceBound a b first) test =
    inner Real source
      (canonicalScalarClosedSeparatedDomainInclusion
        data hClosable traceBound a b second)
  exact hShiftedSymmetric.symm

/-- Compact bounded resolvent package for one separated scalar realization and
one real spectral parameter. -/
structure CanonicalScalarClosedCompactResolventAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real) where
  bounded : CanonicalScalarClosedBoundedResolventAt
    data hClosable traceBound a b spectralParameter
  nondegenerate : a ≠ 0 ∨ b ≠ 0
  compact_ambient : IsCompactOperator
    (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
      data hClosable traceBound a b spectralParameter bounded)

/-- The ambient resolvent in a compact package is symmetric. -/
theorem CanonicalScalarClosedCompactResolventAt.ambient_isSymmetric
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compact : CanonicalScalarClosedCompactResolventAt
      data hClosable traceBound a b spectralParameter) :
    (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
      data hClosable traceBound a b spectralParameter
        compact.bounded).toLinearMap.IsSymmetric :=
  canonicalScalarClosedAmbientResolvent_isSymmetric
    data hClosable traceBound a b spectralParameter
      compact.nondegenerate compact.bounded

/-- Fredholm alternative for the compact ambient resolvent. -/
theorem CanonicalScalarClosedCompactResolventAt.fredholmAlternative
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compact : CanonicalScalarClosedCompactResolventAt
      data hClosable traceBound a b spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0) :
    HasEigenvalue
        ((CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter compact.bounded :
            Ambient →L[Real] Ambient) : Module.End Real Ambient)
        eigenvalue ∨
      eigenvalue ∈ resolventSet Real
        (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter compact.bounded) :=
  compact.compact_ambient.hasEigenvalue_or_mem_resolventSet hEigenvalue

/-- Every nonzero eigenspace of the compact ambient resolvent is finite
dimensional. -/
theorem CanonicalScalarClosedCompactResolventAt.finiteDimensional_eigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compact : CanonicalScalarClosedCompactResolventAt
      data hClosable traceBound a b spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0) :
    FiniteDimensional Real
      (Module.End.eigenspace
        (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter
            compact.bounded).toLinearMap eigenvalue) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    compact.compact_ambient eigenvalue hEigenvalue

/-- Compact self-adjoint spectral completeness: the common orthogonal complement
of all ambient-resolvent eigenspaces is trivial. -/
theorem CanonicalScalarClosedCompactResolventAt.spectral_complete
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compact : CanonicalScalarClosedCompactResolventAt
      data hClosable traceBound a b spectralParameter) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter
            compact.bounded).toLinearMap eigenvalue)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    compact.compact_ambient
    (compact.ambient_isSymmetric
      data hClosable traceBound a b spectralParameter)

/-- A nonzero eigenvalue of the ambient resolvent produces an eigenpair of the
original closed operator.  If `R_lambda x = mu x`, then the reconstructed domain
vector has ambient value `x` and operator eigenvalue `lambda + mu⁻¹`. -/
theorem canonicalScalarClosedResolvent_eigenvector_transfer
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (bounded : CanonicalScalarClosedBoundedResolventAt
      data hClosable traceBound a b spectralParameter)
    (eigenvalue : Real) (hEigenvalue : eigenvalue ≠ 0)
    (vector : Ambient)
    (hVector :
      CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter bounded vector =
        eigenvalue • vector) :
    let field : canonicalScalarClosedSeparatedDomainSubmodule
        data hClosable traceBound a b :=
      eigenvalue⁻¹ • bounded.resolvent vector
    canonicalScalarClosedSeparatedDomainInclusion
        data hClosable traceBound a b field = vector ∧
      canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b field =
        (spectralParameter + eigenvalue⁻¹) • vector := by
  let field : canonicalScalarClosedSeparatedDomainSubmodule
      data hClosable traceBound a b :=
    eigenvalue⁻¹ • bounded.resolvent vector
  have hInclusion :
      canonicalScalarClosedSeparatedDomainInclusion
          data hClosable traceBound a b field = vector := by
    dsimp [field]
    rw [map_smul]
    change eigenvalue⁻¹ •
        (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter bounded vector) = vector
    rw [hVector, smul_smul]
    simp [hEigenvalue]
  have hShifted :
      canonicalScalarClosedSeparatedShiftedOperator
          data hClosable traceBound a b spectralParameter field =
        eigenvalue⁻¹ • vector := by
    change canonicalScalarClosedSeparatedShiftedOperator
        data hClosable traceBound a b spectralParameter
          (eigenvalue⁻¹ • bounded.resolvent vector) = _
    rw [map_smul]
    rw [bounded.left_inverse]
  refine ⟨hInclusion, ?_⟩
  have hExpanded := canonicalScalarClosedSeparatedShiftedOperator_apply
    data hClosable traceBound a b spectralParameter field
  rw [hShifted, hInclusion] at hExpanded
  change eigenvalue⁻¹ • vector =
      canonicalScalarClosedSeparatedDomainOperator
          data hClosable traceBound a b field -
        spectralParameter • vector at hExpanded
  have hAdded := congrArg (fun value => value + spectralParameter • vector) hExpanded
  simpa [field, map_smul, add_smul, add_assoc, add_comm, add_left_comm,
    hInclusion] using hAdded.symm

/-- Spectral closure certificate collecting symmetry, compactness, finite
multiplicity and completeness. -/
theorem canonicalScalarClosedCompactResolventSpectrum_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (a b spectralParameter : Real)
    (compact : CanonicalScalarClosedCompactResolventAt
      data hClosable traceBound a b spectralParameter) :
    (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
        data hClosable traceBound a b spectralParameter
          compact.bounded).toLinearMap.IsSymmetric ∧
      IsCompactOperator
        (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
          data hClosable traceBound a b spectralParameter compact.bounded) ∧
      (∀ eigenvalue : Real, eigenvalue ≠ 0 →
        FiniteDimensional Real
          (Module.End.eigenspace
            (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
              data hClosable traceBound a b spectralParameter
                compact.bounded).toLinearMap eigenvalue)) ∧
      (⨆ eigenvalue : Real,
        Module.End.eigenspace
          (CanonicalScalarClosedBoundedResolventAt.ambientResolvent
            data hClosable traceBound a b spectralParameter
              compact.bounded).toLinearMap eigenvalue)ᗮ = ⊥ := by
  exact ⟨compact.ambient_isSymmetric
      data hClosable traceBound a b spectralParameter,
    compact.compact_ambient,
    compact.finiteDimensional_eigenspace
      data hClosable traceBound a b spectralParameter,
    compact.spectral_complete
      data hClosable traceBound a b spectralParameter⟩

end
end P0EFTJanusMappingTorusScalarCompactResolventSpectrum4D
end JanusFormal
