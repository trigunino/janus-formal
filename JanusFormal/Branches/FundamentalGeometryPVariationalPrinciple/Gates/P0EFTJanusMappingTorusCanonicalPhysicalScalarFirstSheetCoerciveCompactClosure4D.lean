import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongLagrangianDensity4D

/-!
# Physical scalar closure from coercivity and compact embedding

Minimal-core density already implies density of every physical Lagrangian domain,
both in the direct completed triple and in the strong closed presentation.
Therefore density is removed from the final analytic input.

At one reference parameter, coercivity plus surjectivity constructs the bounded
resolvent.  A Rellich compactness theorem for the domain inclusion makes that
resolvent compact.  Together with actual-adjoint regularity and a lower form
bound this installs the complete physical scalar analytic closure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCoerciveCompactClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongLagrangianDensity4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Final coercive/compact physical inputs for one boundary condition. -/
structure CanonicalPhysicalScalarFirstSheetCoerciveCompactData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) where
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjoint : CanonicalPhysicalScalarStrongAdjointCharacterization
    period hPeriod green inputs condition
  referenceParameter : Real
  coerciveCompact : CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt
    (inputs.strongSystem green)
    (inputs.strongSystem_closable green)
    (inputs.strongSystemGraphBound green)
    condition referenceParameter
  semibounded : CanonicalScalarClosedLagrangianSemiboundedData
    (inputs.strongSystem green)
    (inputs.strongSystem_closable green)
    (inputs.strongSystemGraphBound green)
    condition

namespace CanonicalPhysicalScalarFirstSheetCoerciveCompactData

/-- Domain density is automatic from the physical minimal core. -/
theorem denseDomain
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs) :
    DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        (inputs.strongSystem green)
        (inputs.strongSystem_closable green)
        (inputs.strongSystemGraphBound green)
        analytic.condition) :=
  (inputs.physicalTriple green).strongClosedLagrangianInclusion_denseRange_of_minimalCore
    (inputs.strongAdjointTestCore green)
    analytic.condition
    inputs.minimalDense

/-- Compact reference resolvent constructed from coercivity and Rellich. -/
noncomputable def compactResolvent
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs) :
    CanonicalScalarClosedLagrangianCompactResolventAt
      (inputs.strongSystem green)
      (inputs.strongSystem_closable green)
      (inputs.strongSystemGraphBound green)
      analytic.condition analytic.referenceParameter :=
  analytic.coerciveCompact.compactResolvent
    (inputs.strongSystem green)
    (inputs.strongSystem_closable green)
    (inputs.strongSystemGraphBound green)
    analytic.condition analytic.referenceParameter

/-- Conversion to the corrected physical analytic closure. -/
noncomputable def toStrongAnalyticData
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs) :
    CanonicalPhysicalScalarFirstSheetStrongAnalyticData
      period hPeriod green inputs where
  condition := analytic.condition
  denseDomain := analytic.denseDomain period hPeriod
  adjoint := analytic.adjoint
  referenceParameter := analytic.referenceParameter
  compactResolvent := analytic.compactResolvent period hPeriod
  semibounded := analytic.semibounded

/-- Actual physical adjoint domain equality. -/
theorem actualAdjointDomain_eq
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs) :
    analytic.adjoint.adjointDomain =
      (canonicalScalarClosedLagrangianDomainSubmodule
        (inputs.strongSystem green)
        (inputs.strongSystem_closable green)
        (inputs.strongSystemGraphBound green)
        analytic.condition :
          Set (canonicalScalarClosedOperatorDomain
            (inputs.strongSystem green))) :=
  (analytic.toStrongAnalyticData period hPeriod).actualAdjointDomain_eq
    period hPeriod

/-- Physical Fredholm alternative. -/
theorem fredholmAlternative
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    CanonicalScalarClosedLagrangianHasEigenvalue
        (inputs.strongSystem green)
        (inputs.strongSystem_closable green)
        (inputs.strongSystemGraphBound green)
        analytic.condition spectralParameter ∨
      CanonicalScalarClosedLagrangianResolventPoint
        (inputs.strongSystem green)
        (inputs.strongSystem_closable green)
        (inputs.strongSystemGraphBound green)
        analytic.condition spectralParameter :=
  (analytic.toStrongAnalyticData period hPeriod).fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Finite multiplicity of physical eigenspaces. -/
theorem finiteDimensional_eigenspace
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        (inputs.strongSystem green)
        (inputs.strongSystem_closable green)
        (inputs.strongSystemGraphBound green)
        analytic.condition eigenvalue) :=
  (analytic.toStrongAnalyticData period hPeriod).finiteDimensional_eigenspace
    period hPeriod eigenvalue hEigenvalue

/-- Physical spectral lower bound. -/
theorem eigenvalue_ge_lowerBound
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs)
    (eigenvalue : Real)
    (hEigenvalue : CanonicalScalarClosedLagrangianHasEigenvalue
      (inputs.strongSystem green)
      (inputs.strongSystem_closable green)
      (inputs.strongSystemGraphBound green)
      analytic.condition eigenvalue) :
    analytic.semibounded.lowerBound ≤ eigenvalue :=
  (analytic.toStrongAnalyticData period hPeriod).eigenvalue_ge_lowerBound
    period hPeriod eigenvalue hEigenvalue

/-- Coercive/compact physical closure certificate. -/
theorem certificate
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    {inputs : green.CompletedBoundaryTripleInputs period hPeriod}
    (analytic : CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green inputs) :
    DenseRange
        (canonicalScalarClosedLagrangianDomainInclusion
          (inputs.strongSystem green)
          (inputs.strongSystem_closable green)
          (inputs.strongSystemGraphBound green)
          analytic.condition) ∧
      analytic.adjoint.adjointDomain =
        (canonicalScalarClosedLagrangianDomainSubmodule
          (inputs.strongSystem green)
          (inputs.strongSystem_closable green)
          (inputs.strongSystemGraphBound green)
          analytic.condition :
            Set (canonicalScalarClosedOperatorDomain
              (inputs.strongSystem green))) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              (inputs.strongSystem green)
              (inputs.strongSystem_closable green)
              (inputs.strongSystemGraphBound green)
              analytic.condition spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              (inputs.strongSystem green)
              (inputs.strongSystem_closable green)
              (inputs.strongSystemGraphBound green)
              analytic.condition spectralParameter) :=
  ⟨analytic.denseDomain period hPeriod,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarFirstSheetCoerciveCompactData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCoerciveCompactClosure4D
end JanusFormal
