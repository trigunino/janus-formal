import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarBoundarySymplecticCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertBoundaryDirectSum4D

/-!
# Analytic closure package for the scalar Program-P boundary problem

This leaf assembles the entire scalar boundary-to-spectrum chain developed after
the global Green--Stokes theorem.

The input package records exactly the remaining analytic facts for one concrete
Program-P scalar realization:

* single-valuedness of the closed graph;
* graph-norm boundedness and surjectivity of the paired boundary trace;
* a closed Lagrangian boundary condition;
* density of the chosen operator domain in the ambient Hilbert space;
* identification of the actual Hilbert-adjoint domain by the Green boundary
  test;
* one compact bounded resolvent;
* a lower bound on the quadratic form.

From these inputs the certificate exposes domain equality with the actual
adjoint, weak/strong variational equivalence, compact-resolvent spectral
completeness, finite multiplicity, the unbounded Fredholm alternative and the
semibounded spectral lower bound.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
open P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Actual-adjoint characterization for an arbitrary closed Lagrangian boundary
condition. -/
structure CanonicalScalarClosedLagrangianAdjointCharacterization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  adjointDomain : Set (canonicalScalarClosedOperatorDomain data)
  mem_adjointDomain_iff : ∀ candidate,
    candidate ∈ adjointDomain ↔
      canonicalScalarClosedLagrangianAdjointAdmissible
        data hClosable traceBound condition candidate

/-- Maximal Lagrangianity identifies the actual adjoint domain with the original
operator domain whenever the analytic characterization is supplied. -/
theorem CanonicalScalarClosedLagrangianAdjointCharacterization.adjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (characterization : CanonicalScalarClosedLagrangianAdjointCharacterization
      data hClosable traceBound condition) :
    characterization.adjointDomain =
      (canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :
          Set (canonicalScalarClosedOperatorDomain data)) := by
  ext candidate
  rw [characterization.mem_adjointDomain_iff]
  exact canonicalScalarClosedLagrangianAdjointAdmissible_iff_mem
    data hClosable traceBound condition candidate

/-- Complete analytic closure data for one scalar Lagrangian realization. -/
structure CanonicalScalarLagrangianAnalyticClosureData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  referenceParameter : Real
  denseDomain : DenseRange
    (canonicalScalarClosedLagrangianDomainInclusion
      data hClosable traceBound condition)
  adjointCharacterization :
    CanonicalScalarClosedLagrangianAdjointCharacterization
      data hClosable traceBound condition
  compactResolvent : CanonicalScalarClosedLagrangianCompactResolventAt
    data hClosable traceBound condition referenceParameter
  semibounded : CanonicalScalarClosedLagrangianSemiboundedData
    data hClosable traceBound condition

/-- The actual adjoint domain of a closed analytic package is the chosen
Lagrangian domain. -/
theorem CanonicalScalarLagrangianAnalyticClosureData.adjointDomain_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition) :
    closureData.adjointCharacterization.adjointDomain =
      (canonicalScalarClosedLagrangianDomainSubmodule
        data hClosable traceBound condition :
          Set (canonicalScalarClosedOperatorDomain data)) :=
  closureData.adjointCharacterization.adjointDomain_eq
    data hClosable traceBound condition

/-- Every non-reference real parameter satisfies the unbounded Fredholm
alternative. -/
theorem CanonicalScalarLagrangianAnalyticClosureData.fredholmAlternative
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ closureData.referenceParameter) :
    CanonicalScalarClosedLagrangianHasEigenvalue
        data hClosable traceBound condition spectralParameter ∨
      CanonicalScalarClosedLagrangianResolventPoint
        data hClosable traceBound condition spectralParameter :=
  canonicalScalarClosedLagrangian_fredholmAlternative
    data hClosable traceBound condition closureData.referenceParameter
      spectralParameter (sub_ne_zero.mpr hParameter)
      closureData.compactResolvent

/-- Every non-reference operator eigenspace is finite-dimensional. -/
theorem CanonicalScalarLagrangianAnalyticClosureData.finiteDimensional_eigenspace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ closureData.referenceParameter) :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        data hClosable traceBound condition eigenvalue) :=
  canonicalScalarClosedLagrangianOperatorEigenspace_finiteDimensional
    data hClosable traceBound condition closureData.referenceParameter eigenvalue
      (sub_ne_zero.mpr hEigenvalue) closureData.compactResolvent

/-- Every actual eigenvalue is bounded below by the quadratic-form lower bound. -/
theorem CanonicalScalarLagrangianAnalyticClosureData.eigenvalue_ge_lowerBound
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition)
    (eigenvalue : Real)
    (hEigenvalue : CanonicalScalarClosedLagrangianHasEigenvalue
      data hClosable traceBound condition eigenvalue) :
    closureData.semibounded.lowerBound ≤ eigenvalue := by
  rcases hEigenvalue with ⟨field, hField, hEquation⟩
  exact closureData.semibounded.eigenvalue_ge_lowerBound
    data hClosable traceBound condition eigenvalue field hField hEquation

/-- Weak constrained stationarity and the strong eigenvalue equation are
identical on the dense analytic domain. -/
theorem CanonicalScalarLagrangianAnalyticClosureData.stationary_iff_eigenfield
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition)
    (eigenvalue : Real)
    (field : canonicalScalarClosedLagrangianDomainSubmodule
      data hClosable traceBound condition) :
    CanonicalScalarClosedLagrangianStationaryAt
        data hClosable traceBound condition eigenvalue field ↔
      canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition field :=
  canonicalScalarClosedLagrangian_stationary_iff_eigenfield
    data hClosable traceBound condition eigenvalue field closureData.denseDomain

/-- The compact reference resolvent has a complete orthogonal eigenspace
decomposition. -/
theorem CanonicalScalarLagrangianAnalyticClosureData.referenceResolvent_spectral_complete
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition) :
    (⨆ eigenvalue : Real,
      LinearMap.eigenspace
        (closureData.compactResolvent.bounded.ambientResolvent
          data hClosable traceBound condition
            closureData.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  closureData.compactResolvent.spectral_complete
    data hClosable traceBound condition closureData.referenceParameter

/-- Full analytic closure certificate for the scalar Lagrangian boundary
problem. -/
theorem canonicalScalarLagrangianAnalyticClosure_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition) :
    closureData.adjointCharacterization.adjointDomain =
        (canonicalScalarClosedLagrangianDomainSubmodule
          data hClosable traceBound condition :
            Set (canonicalScalarClosedOperatorDomain data)) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ closureData.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              data hClosable traceBound condition spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              data hClosable traceBound condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        CanonicalScalarClosedLagrangianHasEigenvalue
            data hClosable traceBound condition eigenvalue →
          closureData.semibounded.lowerBound ≤ eigenvalue) ∧
      (⨆ eigenvalue : Real,
        LinearMap.eigenspace
          (closureData.compactResolvent.bounded.ambientResolvent
            data hClosable traceBound condition
              closureData.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  ⟨closureData.adjointDomain_eq data hClosable traceBound condition,
    closureData.fredholmAlternative data hClosable traceBound condition,
    closureData.eigenvalue_ge_lowerBound data hClosable traceBound condition,
    closureData.referenceResolvent_spectral_complete
      data hClosable traceBound condition⟩

end
end P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D
end JanusFormal
