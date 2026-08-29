import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

/-!
# Correct physical scalar compact analytic closure

This is the final physical scalar closure path built from the dense smooth Green
core rather than an impossible smooth-surjectivity hypothesis.

After completion, the strong system has a genuinely surjective boundary trace.
For a chosen closed Lagrangian condition, the remaining analytic inputs are
exactly:

* density of the actual boundary domain in bulk L2;
* characterization of the true Hilbert adjoint by the Green boundary test;
* one coercive compact resolvent;
* a lower quadratic-form bound.

The generic closure package then yields self-adjoint domain equality, Fredholm
alternative, compact spectral completeness, finite multiplicity, lower spectral
bounds and weak/strong variational equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D.CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
open P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Characterization of the genuine Hilbert adjoint domain for the corrected
strong physical system. -/
structure CanonicalPhysicalScalarStrongAdjointCharacterization
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) where
  adjointDomain : Set (canonicalScalarClosedOperatorDomain
    (strongSystem period hPeriod green inputs))
  mem_adjointDomain_iff : ∀ candidate,
    candidate ∈ adjointDomain ↔
      canonicalScalarClosedLagrangianAdjointAdmissible
        (strongSystem period hPeriod green inputs)
        (strongSystem_closable period hPeriod green inputs)
        (strongSystemGraphBound period hPeriod green inputs)
        condition candidate

namespace CanonicalPhysicalScalarStrongAdjointCharacterization

/-- Conversion to the generic actual-adjoint interface. -/
def toGeneric
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (adjoint : CanonicalPhysicalScalarStrongAdjointCharacterization
      period hPeriod green inputs condition) :
    CanonicalScalarClosedLagrangianAdjointCharacterization
      (strongSystem period hPeriod green inputs)
      (strongSystem_closable period hPeriod green inputs)
      (strongSystemGraphBound period hPeriod green inputs)
      condition where
  adjointDomain := adjoint.adjointDomain
  mem_adjointDomain_iff := adjoint.mem_adjointDomain_iff

/-- Actual Hilbert adjoint domain equals the selected physical Lagrangian
boundary domain. -/
theorem adjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (adjoint : CanonicalPhysicalScalarStrongAdjointCharacterization
      period hPeriod green inputs condition) :
    adjoint.adjointDomain =
      (canonicalScalarClosedLagrangianDomainSubmodule
        (strongSystem period hPeriod green inputs)
        (strongSystem_closable period hPeriod green inputs)
        (strongSystemGraphBound period hPeriod green inputs)
        condition :
          Set (canonicalScalarClosedOperatorDomain
            (strongSystem period hPeriod green inputs))) :=
  (CanonicalPhysicalScalarStrongAdjointCharacterization.toGeneric
    period hPeriod green inputs condition adjoint).adjointDomain_eq
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    condition

end CanonicalPhysicalScalarStrongAdjointCharacterization

/-- Full corrected physical scalar analytic inputs for one Lagrangian boundary
condition. -/
structure CanonicalPhysicalScalarFirstSheetStrongAnalyticData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) where
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  denseDomain : DenseRange
    (canonicalScalarClosedLagrangianDomainInclusion
      (strongSystem period hPeriod green inputs)
      (strongSystem_closable period hPeriod green inputs)
      (strongSystemGraphBound period hPeriod green inputs)
      condition)
  adjoint : CanonicalPhysicalScalarStrongAdjointCharacterization
    period hPeriod green inputs condition
  referenceParameter : Real
  compactResolvent : CanonicalScalarClosedLagrangianCompactResolventAt
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    condition referenceParameter
  semibounded : CanonicalScalarClosedLagrangianSemiboundedData
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    condition

namespace CanonicalPhysicalScalarFirstSheetStrongAnalyticData

/-- Conversion to the generic analytic closure package. -/
def toGeneric
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs) :
    CanonicalScalarLagrangianAnalyticClosureData
      (strongSystem period hPeriod green inputs)
      (strongSystem_closable period hPeriod green inputs)
      (strongSystemGraphBound period hPeriod green inputs)
      analytic.condition where
  referenceParameter := analytic.referenceParameter
  denseDomain := analytic.denseDomain
  adjointCharacterization :=
    CanonicalPhysicalScalarStrongAdjointCharacterization.toGeneric
      period hPeriod green inputs analytic.condition analytic.adjoint
  compactResolvent := analytic.compactResolvent
  semibounded := analytic.semibounded

/-- Actual physical self-adjoint domain equality. -/
theorem actualAdjointDomain_eq
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs) :
    analytic.adjoint.adjointDomain =
      (canonicalScalarClosedLagrangianDomainSubmodule
        (strongSystem period hPeriod green inputs)
        (strongSystem_closable period hPeriod green inputs)
        (strongSystemGraphBound period hPeriod green inputs)
        analytic.condition :
          Set (canonicalScalarClosedOperatorDomain
            (strongSystem period hPeriod green inputs))) :=
  CanonicalPhysicalScalarStrongAdjointCharacterization.adjointDomain_eq
    period hPeriod green inputs analytic.condition analytic.adjoint

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    CanonicalScalarClosedLagrangianHasEigenvalue
        (strongSystem period hPeriod green inputs)
        (strongSystem_closable period hPeriod green inputs)
        (strongSystemGraphBound period hPeriod green inputs)
        analytic.condition spectralParameter ∨
      CanonicalScalarClosedLagrangianResolventPoint
        (strongSystem period hPeriod green inputs)
        (strongSystem_closable period hPeriod green inputs)
        (strongSystemGraphBound period hPeriod green inputs)
        analytic.condition spectralParameter :=
  (analytic.toGeneric period hPeriod).fredholmAlternative
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    analytic.condition spectralParameter hParameter

/-- Finite multiplicity of physical eigenspaces. -/
theorem finiteDimensional_eigenspace
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        (strongSystem period hPeriod green inputs)
        (strongSystem_closable period hPeriod green inputs)
        (strongSystemGraphBound period hPeriod green inputs)
        analytic.condition eigenvalue) :=
  (analytic.toGeneric period hPeriod).finiteDimensional_eigenspace
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    analytic.condition eigenvalue hEigenvalue

/-- Physical spectral lower bound. -/
theorem eigenvalue_ge_lowerBound
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs)
    (eigenvalue : Real)
    (hEigenvalue : CanonicalScalarClosedLagrangianHasEigenvalue
      (strongSystem period hPeriod green inputs)
      (strongSystem_closable period hPeriod green inputs)
      (strongSystemGraphBound period hPeriod green inputs)
      analytic.condition eigenvalue) :
    analytic.semibounded.lowerBound ≤ eigenvalue :=
  (analytic.toGeneric period hPeriod).eigenvalue_ge_lowerBound
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    analytic.condition eigenvalue hEigenvalue

/-- Compact physical spectral completeness. -/
theorem spectral_complete
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        (analytic.compactResolvent.bounded.ambientResolvent
          (strongSystem period hPeriod green inputs)
          (strongSystem_closable period hPeriod green inputs)
          (strongSystemGraphBound period hPeriod green inputs)
          analytic.condition analytic.referenceParameter).toLinearMap
        eigenvalue)ᗮ = ⊥ :=
  analytic.compactResolvent.spectral_complete
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    analytic.condition analytic.referenceParameter

/-- Correct physical compact analytic closure certificate. -/
theorem certificate
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs) :
    analytic.adjoint.adjointDomain =
        (canonicalScalarClosedLagrangianDomainSubmodule
          (strongSystem period hPeriod green inputs)
          (strongSystem_closable period hPeriod green inputs)
          (strongSystemGraphBound period hPeriod green inputs)
          analytic.condition :
            Set (canonicalScalarClosedOperatorDomain
              (strongSystem period hPeriod green inputs))) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              (strongSystem period hPeriod green inputs)
              (strongSystem_closable period hPeriod green inputs)
              (strongSystemGraphBound period hPeriod green inputs)
              analytic.condition spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              (strongSystem period hPeriod green inputs)
              (strongSystem_closable period hPeriod green inputs)
              (strongSystemGraphBound period hPeriod green inputs)
              analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        CanonicalScalarClosedLagrangianHasEigenvalue
            (strongSystem period hPeriod green inputs)
            (strongSystem_closable period hPeriod green inputs)
            (strongSystemGraphBound period hPeriod green inputs)
            analytic.condition eigenvalue →
          analytic.semibounded.lowerBound ≤ eigenvalue) ∧
      (⨆ eigenvalue : Real,
        Module.End.eigenspace
          (analytic.compactResolvent.bounded.ambientResolvent
            (strongSystem period hPeriod green inputs)
            (strongSystem_closable period hPeriod green inputs)
            (strongSystemGraphBound period hPeriod green inputs)
            analytic.condition analytic.referenceParameter).toLinearMap
          eigenvalue)ᗮ = ⊥ :=
  ⟨analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_lowerBound period hPeriod,
    analytic.spectral_complete period hPeriod⟩

end CanonicalPhysicalScalarFirstSheetStrongAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D
end JanusFormal
