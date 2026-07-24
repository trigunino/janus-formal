import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D

/-!
# Exact remaining analytic inputs for physical scalar closure

This file is an executable frontier ledger.  It does not add assumptions to the
repository globally; it packages the named results still required to instantiate
the complete physical scalar Program-P architecture.

The input fields are:

1. comparison of the physical Euler/normal-trace pairings with the already
   constructed global Green boundary form;
2. graph-norm boundedness of the paired Cauchy trace;
3. single-valuedness/closability of the completed graph;
4. a chosen closed Lagrangian boundary condition;
5. density of that actual operator domain;
6. characterization of the actual Hilbert adjoint by the boundary test;
7. one compact bounded resolvent;
8. a lower quadratic-form bound;
9. a parameter family of Dirichlet resolvents and a continuous value-boundary
   lift, from which Poisson, Weyl, Calderon and Krein data are constructed.

Once these fields are filled, all closure, variational, spectral and boundary
reduction theorems are available without further axioms.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarRemainingAnalyticInputs4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology Module End
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D
open P0EFTJanusMappingTorusScalarGraphPoissonFromDirichletResolvent4D
open P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev PhysicalTrace := CanonicalPhysicalThroatL2 period hPeriod

/-- Core physical analytic inputs up to compact self-adjoint closure. -/
structure CanonicalPhysicalScalarCoreAnalyticInputs where
  greenBridge : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod
  graphBound : CanonicalPhysicalPairedBoundaryGraphBound period hPeriod
    (greenBridge.toSmoothGreenData period hPeriod)
  closable : CanonicalScalarGraphClosable
    (greenBridge.toHilbertGreenSystem period hPeriod)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (PhysicalTrace period hPeriod)
  referenceParameter : Real
  denseDomain : DenseRange
    (canonicalScalarClosedLagrangianDomainInclusion
      (greenBridge.toHilbertGreenSystem period hPeriod)
      closable
      (graphBound.toAbstract period hPeriod
        (greenBridge.toSmoothGreenData period hPeriod))
      condition)
  adjointCharacterization :
    CanonicalScalarClosedLagrangianAdjointCharacterization
      (greenBridge.toHilbertGreenSystem period hPeriod)
      closable
      (graphBound.toAbstract period hPeriod
        (greenBridge.toSmoothGreenData period hPeriod))
      condition
  compactResolvent : CanonicalScalarClosedLagrangianCompactResolventAt
    (greenBridge.toHilbertGreenSystem period hPeriod)
    closable
    (graphBound.toAbstract period hPeriod
      (greenBridge.toSmoothGreenData period hPeriod))
    condition referenceParameter
  semibounded : CanonicalScalarClosedLagrangianSemiboundedData
    (greenBridge.toHilbertGreenSystem period hPeriod)
    closable
    (graphBound.toAbstract period hPeriod
      (greenBridge.toSmoothGreenData period hPeriod))
    condition

namespace CanonicalPhysicalScalarCoreAnalyticInputs

/-- Underlying physical Green system. -/
def system
    (inputs : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod) :=
  inputs.greenBridge.toHilbertGreenSystem period hPeriod

/-- Underlying physical graph-bound package. -/
def abstractGraphBound
    (inputs : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod) :=
  inputs.graphBound.toAbstract period hPeriod
    (inputs.greenBridge.toSmoothGreenData period hPeriod)

/-- Conversion to the generic analytic closure package. -/
def toGenericClosureData
    (inputs : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod) :
    CanonicalScalarLagrangianAnalyticClosureData
      inputs.system inputs.closable inputs.abstractGraphBound inputs.condition where
  referenceParameter := inputs.referenceParameter
  denseDomain := inputs.denseDomain
  adjointCharacterization := inputs.adjointCharacterization
  compactResolvent := inputs.compactResolvent
  semibounded := inputs.semibounded

/-- Conversion to the physical facade already constructed. -/
def toPhysicalClosureData
    (inputs : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod) :
    CanonicalPhysicalScalarAnalyticClosureData period hPeriod where
  smoothGreen := inputs.greenBridge.toSmoothGreenData period hPeriod
  graphBound := inputs.graphBound
  closable := inputs.closable
  condition := inputs.condition
  analytic := inputs.toGenericClosureData period hPeriod

/-- Core closure certificate supplied by the frontier package. -/
theorem core_certificate
    (inputs : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod) :
    inputs.adjointCharacterization.adjointDomain =
        (canonicalScalarClosedLagrangianDomainSubmodule
          inputs.system inputs.closable inputs.abstractGraphBound inputs.condition :
            Set (canonicalScalarClosedOperatorDomain inputs.system)) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ inputs.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              inputs.system inputs.closable inputs.abstractGraphBound
                inputs.condition spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              inputs.system inputs.closable inputs.abstractGraphBound
                inputs.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        CanonicalScalarClosedLagrangianHasEigenvalue
            inputs.system inputs.closable inputs.abstractGraphBound
              inputs.condition eigenvalue →
          inputs.semibounded.lowerBound ≤ eigenvalue) := by
  have hCertificate := canonicalScalarLagrangianAnalyticClosure_certificate
    inputs.system inputs.closable inputs.abstractGraphBound inputs.condition
      (inputs.toGenericClosureData period hPeriod)
  exact ⟨hCertificate.1, hCertificate.2.1, hCertificate.2.2.1⟩

end CanonicalPhysicalScalarCoreAnalyticInputs

/-- Boundary-triple family inputs on top of the core physical closure. -/
structure CanonicalPhysicalScalarBoundaryFamilyInputs
    (core : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod) where
  parameters : Set Real
  valueLift : CanonicalScalarGraphBoundaryValueLiftData
    core.system core.abstractGraphBound
  dirichletResolvent : ∀ spectralParameter : Real,
    spectralParameter ∈ parameters →
      CanonicalScalarGraphDirichletResolventData
        core.system core.abstractGraphBound spectralParameter

namespace CanonicalPhysicalScalarBoundaryFamilyInputs

/-- Conversion to the generic boundary-triple family. -/
def toBoundaryTripleFamily
    {core : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod}
    (boundaryInputs : CanonicalPhysicalScalarBoundaryFamilyInputs
      period hPeriod core) :
    CanonicalScalarGraphBoundaryTripleFamily
      core.system core.abstractGraphBound boundaryInputs.parameters where
  valueLift := boundaryInputs.valueLift
  dirichletResolvent := boundaryInputs.dirichletResolvent

/-- Physical Poisson data derived at every admitted parameter. -/
def poissonData
    {core : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod}
    (boundaryInputs : CanonicalPhysicalScalarBoundaryFamilyInputs
      period hPeriod core)
    (spectralParameter : Real)
    (hParameter : spectralParameter ∈ boundaryInputs.parameters) :=
  (boundaryInputs.toBoundaryTripleFamily period hPeriod).poissonData
    spectralParameter hParameter

/-- Physical Weyl function derived at every admitted parameter. -/
def weyl
    {core : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod}
    (boundaryInputs : CanonicalPhysicalScalarBoundaryFamilyInputs
      period hPeriod core)
    (spectralParameter : Real)
    (hParameter : spectralParameter ∈ boundaryInputs.parameters) :=
  (boundaryInputs.toBoundaryTripleFamily period hPeriod).weyl
    spectralParameter hParameter

/-- Boundary-family certificate. -/
theorem boundary_certificate
    {core : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod}
    (boundaryInputs : CanonicalPhysicalScalarBoundaryFamilyInputs
      period hPeriod core) :
    (∀ spectralParameter : Real,
      ∀ hParameter : spectralParameter ∈ boundaryInputs.parameters,
        (boundaryInputs.weyl period hPeriod spectralParameter hParameter).toLinearMap.IsSymmetric) ∧
      (∀ spectralParameter : Real,
        ∀ hParameter : spectralParameter ∈ boundaryInputs.parameters,
        ∀ boundary : PhysicalTrace period hPeriod,
          canonicalScalarCompletedValueTrace
              core.system core.abstractGraphBound
              ((boundaryInputs.poissonData period hPeriod
                spectralParameter hParameter).poisson boundary) = boundary) := by
  constructor
  · intro spectralParameter hParameter
    exact (boundaryInputs.toBoundaryTripleFamily period hPeriod).weyl_isSymmetric
      spectralParameter hParameter
  · intro spectralParameter hParameter boundary
    exact (boundaryInputs.poissonData period hPeriod
      spectralParameter hParameter).value_trace boundary

end CanonicalPhysicalScalarBoundaryFamilyInputs

/-- Complete named frontier package: core analytic closure plus boundary family. -/
structure CanonicalPhysicalScalarFullAnalyticInputs where
  core : CanonicalPhysicalScalarCoreAnalyticInputs period hPeriod
  boundary : CanonicalPhysicalScalarBoundaryFamilyInputs
    period hPeriod core

/-- Full physical frontier certificate. -/
theorem canonicalPhysicalScalarRemainingAnalyticInputs_certificate
    (inputs : CanonicalPhysicalScalarFullAnalyticInputs period hPeriod) :
    inputs.core.adjointCharacterization.adjointDomain =
        (canonicalScalarClosedLagrangianDomainSubmodule
          inputs.core.system inputs.core.closable
            inputs.core.abstractGraphBound inputs.core.condition :
          Set (canonicalScalarClosedOperatorDomain inputs.core.system)) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ inputs.core.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              inputs.core.system inputs.core.closable
                inputs.core.abstractGraphBound inputs.core.condition
                spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              inputs.core.system inputs.core.closable
                inputs.core.abstractGraphBound inputs.core.condition
                spectralParameter) ∧
      (∀ spectralParameter : Real,
        ∀ hParameter : spectralParameter ∈ inputs.boundary.parameters,
          (inputs.boundary.weyl period hPeriod
            spectralParameter hParameter).toLinearMap.IsSymmetric) := by
  exact ⟨(inputs.core.core_certificate period hPeriod).1,
    (inputs.core.core_certificate period hPeriod).2.1,
    (inputs.boundary.boundary_certificate period hPeriod).1⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarRemainingAnalyticInputs4D
end JanusFormal
