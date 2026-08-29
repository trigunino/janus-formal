import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarClosedBoundaryDomains4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D

/-!
# Full first-sheet physical scalar analytic closure

This file packages the remaining closed-operator estimates for one concrete
physical first-sheet Lagrangian boundary condition:

* density of the actual operator domain;
* characterization of the genuine Hilbert adjoint by the Green boundary test;
* coercivity and surjectivity at one reference parameter;
* compactness of the domain inclusion;
* a lower quadratic-form bound.

All downstream conclusions are then automatic: actual self-adjoint domain,
bounded compact resolvent, Fredholm alternative, finite multiplicity, spectral
completeness, weak/strong variational equivalence and the lower spectral bound.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarClosedBoundaryDomains4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Complete physical analytic input for one selected first-sheet Lagrangian
condition. -/
structure CanonicalPhysicalScalarFirstSheetAnalyticData
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (maximal : green.MaximalClosureData period hPeriod) where
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  denseDomain : DenseRange
    (canonicalScalarClosedLagrangianDomainInclusion
      green.system (maximal.closable green) (maximal.graphBound green)
        condition)
  actualAdjoint : maximal.ActualHilbertAdjointCharacterization
    green condition
  referenceParameter : Real
  coerciveCompact : CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt
    green.system (maximal.closable green) (maximal.graphBound green)
      condition referenceParameter
  semibounded : CanonicalScalarClosedLagrangianSemiboundedData
    green.system (maximal.closable green) (maximal.graphBound green)
      condition

namespace CanonicalPhysicalScalarFirstSheetAnalyticData

/-- Selected actual closed physical operator domain. -/
abbrev Domain
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :=
  maximal.ClosedLagrangianDomain green analytic.condition

/-- Actual Hilbert adjoint characterization in the generic closure format. -/
def adjointCharacterization
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :
    CanonicalScalarClosedLagrangianAdjointCharacterization
      green.system (maximal.closable green) (maximal.graphBound green)
        analytic.condition where
  adjointDomain := analytic.actualAdjoint.adjointDomain
  mem_adjointDomain_iff := analytic.actualAdjoint.mem_adjointDomain_iff

/-- Bounded resolvent at the physical reference parameter. -/
noncomputable def boundedResolvent
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :
    CanonicalScalarClosedLagrangianBoundedResolventAt
      green.system (maximal.closable green) (maximal.graphBound green)
        analytic.condition analytic.referenceParameter :=
  analytic.coerciveCompact.coercive.boundedResolvent
    green.system (maximal.closable green) (maximal.graphBound green)
      analytic.condition analytic.referenceParameter

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :
    CanonicalScalarClosedLagrangianCompactResolventAt
      green.system (maximal.closable green) (maximal.graphBound green)
        analytic.condition analytic.referenceParameter :=
  analytic.coerciveCompact.compactResolvent
    green.system (maximal.closable green) (maximal.graphBound green)
      analytic.condition analytic.referenceParameter

/-- Conversion to the full generic analytic closure package. -/
noncomputable def toGenericClosureData
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :
    CanonicalScalarLagrangianAnalyticClosureData
      green.system (maximal.closable green) (maximal.graphBound green)
        analytic.condition where
  referenceParameter := analytic.referenceParameter
  denseDomain := analytic.denseDomain
  adjointCharacterization := analytic.adjointCharacterization period hPeriod
  compactResolvent := analytic.compactResolvent period hPeriod
  semibounded := analytic.semibounded

/-- Genuine Hilbert adjoint domain equals the selected physical boundary domain. -/
theorem actualAdjointDomain_eq
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :
    analytic.actualAdjoint.adjointDomain =
      (analytic.Domain : Set (maximal.ClosedDomain green)) :=
  analytic.actualAdjoint.adjointDomain_eq
    green maximal analytic.condition

/-- Physical Fredholm alternative away from the reference parameter. -/
theorem fredholmAlternative
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    CanonicalScalarClosedLagrangianHasEigenvalue
        green.system (maximal.closable green) (maximal.graphBound green)
          analytic.condition spectralParameter ∨
      CanonicalScalarClosedLagrangianResolventPoint
        green.system (maximal.closable green) (maximal.graphBound green)
          analytic.condition spectralParameter :=
  (analytic.toGenericClosureData period hPeriod).fredholmAlternative
    green.system (maximal.closable green) (maximal.graphBound green)
      analytic.condition spectralParameter hParameter

/-- Finite-dimensional physical eigenspaces away from the reference parameter. -/
theorem finiteDimensional_eigenspace
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        green.system (maximal.closable green) (maximal.graphBound green)
          analytic.condition eigenvalue) :=
  (analytic.toGenericClosureData period hPeriod).finiteDimensional_eigenspace
    green.system (maximal.closable green) (maximal.graphBound green)
      analytic.condition eigenvalue hEigenvalue

/-- Physical lower spectral bound. -/
theorem eigenvalue_ge_lowerBound
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal)
    (eigenvalue : Real)
    (hEigenvalue : CanonicalScalarClosedLagrangianHasEigenvalue
      green.system (maximal.closable green) (maximal.graphBound green)
        analytic.condition eigenvalue) :
    analytic.semibounded.lowerBound ≤ eigenvalue :=
  (analytic.toGenericClosureData period hPeriod).eigenvalue_ge_lowerBound
    green.system (maximal.closable green) (maximal.graphBound green)
      analytic.condition eigenvalue hEigenvalue

/-- Spectral completeness of the compact physical reference resolvent. -/
theorem spectral_complete
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :
    (⨆ eigenvalue : Real,
      LinearMap.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          green.system (maximal.closable green) (maximal.graphBound green)
            analytic.condition analytic.referenceParameter).toLinearMap
        eigenvalue)ᗮ = ⊥ :=
  (analytic.compactResolvent period hPeriod).spectral_complete
    green.system (maximal.closable green) (maximal.graphBound green)
      analytic.condition analytic.referenceParameter

/-- Full physical first-sheet analytic closure certificate. -/
theorem certificate
    {green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared}
    {maximal : green.MaximalClosureData period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetAnalyticData
      period hPeriod green maximal) :
    analytic.actualAdjoint.adjointDomain =
        (analytic.Domain : Set (maximal.ClosedDomain green)) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              green.system (maximal.closable green) (maximal.graphBound green)
                analytic.condition spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              green.system (maximal.closable green) (maximal.graphBound green)
                analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        CanonicalScalarClosedLagrangianHasEigenvalue
            green.system (maximal.closable green) (maximal.graphBound green)
              analytic.condition eigenvalue →
          analytic.semibounded.lowerBound ≤ eigenvalue) ∧
      (⨆ eigenvalue : Real,
        LinearMap.eigenspace
          ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
            green.system (maximal.closable green) (maximal.graphBound green)
              analytic.condition analytic.referenceParameter).toLinearMap
          eigenvalue)ᗮ = ⊥ :=
  ⟨analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_lowerBound period hPeriod,
    analytic.spectral_complete period hPeriod⟩

end CanonicalPhysicalScalarFirstSheetAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetAnalyticClosure4D
end JanusFormal
