import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

/-!
# Correct strong physical scalar system after graph completion

The corrected physical Green core is first completed.  Its completed trace is
surjective and its maximal inclusion is injective.  Only at this stage is it
converted to the strong Green-system interface used by the existing spectral
architecture.

The original smooth zero-Cauchy core remains dense in bulk L2 and supplies the
formal-adjoint test domain needed to prove closability of this strong
presentation.  Consequently all legacy closed-Lagrangian resolvent and compact
spectrum theorems apply without asserting surjectivity of the smooth L2 trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D.CanonicalScalarCompletedBoundaryTripleData
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

/-- Correct completed physical boundary triple. -/
def physicalTriple
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs.triple
    period hPeriod green inputs

/-- Strong physical system whose domain is the completed maximal graph. -/
def strongSystem
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  toStrongSystem (physicalTriple period hPeriod green inputs)

/-- Smooth minimal core mapped into the completed maximal graph. -/
def smoothMinimalToMaximalGraph
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    minimalDomainSubmodule green.core →ₗ[Real]
      (physicalTriple period hPeriod green inputs).MaximalDomain :=
  (canonicalScalarGreenCoreToGraph green.core).comp
    (minimalDomainSubmodule green.core).subtype

/-- The completed trace of a smooth minimal-core vector vanishes. -/
theorem completedTrace_smoothMinimal_zero
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (test : minimalDomainSubmodule green.core) :
    canonicalScalarGreenCoreCompletedBoundaryTrace
        green.core
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs.traceBound
          period hPeriod green inputs)
        (smoothMinimalToMaximalGraph period hPeriod green inputs test) = 0 := by
  change canonicalScalarGreenCoreCompletedBoundaryTrace
      green.core
      (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs.traceBound
        period hPeriod green inputs)
      (canonicalScalarGreenCoreToGraph green.core test.1) = 0
  rw [canonicalScalarGreenCoreCompletedBoundaryTrace_smooth]
  exact LinearMap.mem_ker.mp test.2

/-- Formal-adjoint pairing of an arbitrary completed maximal vector with a
smooth zero-Cauchy test. -/
theorem maximal_minimal_pairing
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (field : (physicalTriple period hPeriod green inputs).MaximalDomain)
    (test : minimalDomainSubmodule green.core) :
    inner Real (canonicalScalarGreenCoreGraphOperator green.core field)
        (minimalInclusion green.core test) =
      inner Real (canonicalScalarGreenCoreGraphInclusion green.core field)
        (minimalOperator green.core test) := by
  have hGreen := canonicalScalarGreenCoreCompletedGreenIdentity
    green.core
      (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs.traceBound
        period hPeriod green inputs)
      field (smoothMinimalToMaximalGraph period hPeriod green inputs test)
  unfold canonicalScalarGreenCoreCompletedBoundaryPairing at hGreen
  rw [completedTrace_smoothMinimal_zero period hPeriod green inputs test] at hGreen
  simp [canonicalScalarHilbertBoundarySymplecticForm] at hGreen
  simpa [smoothMinimalToMaximalGraph, minimalInclusion, minimalOperator,
    canonicalScalarGreenCoreGraphInclusion,
    canonicalScalarGreenCoreGraphOperator,
    canonicalScalarGreenCoreToGraph,
    canonicalScalarGreenCoreGraphLinearMap] using sub_eq_zero.mp hGreen

/-- Dense formal-adjoint test package for the strong presentation. -/
def strongAdjointTestCore
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    StrongAdjointTestCore (physicalTriple period hPeriod green inputs)
      (TestDomain := minimalDomainSubmodule green.core) where
  inclusion := minimalInclusion green.core
  operator := minimalOperator green.core
  dense := inputs.minimalDense
  pairing := maximal_minimal_pairing period hPeriod green inputs

/-- The corrected strong physical system is closable. -/
theorem strongSystem_closable
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    CanonicalScalarGraphClosable (strongSystem period hPeriod green inputs) :=
  toStrongSystem_closable (physicalTriple period hPeriod green inputs)
    (strongAdjointTestCore period hPeriod green inputs)

/-- Graph bound for the corrected strong physical system. -/
def strongSystemGraphBound
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    HasCanonicalScalarHilbertBoundaryGraphBound
      (strongSystem period hPeriod green inputs) :=
  toStrongSystemBoundaryGraphBound (physicalTriple period hPeriod green inputs)

/-- Correct closed strong-domain Lagrangian submodule. -/
def strongClosedLagrangianDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    condition

/-- Strong-system physical boundary-adjoint maximality. -/
theorem strongClosedLagrangianAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    canonicalScalarClosedLagrangianAdjointDomain
        (strongSystem period hPeriod green inputs)
        (strongSystem_closable period hPeriod green inputs)
        (strongSystemGraphBound period hPeriod green inputs)
        condition =
      (strongClosedLagrangianDomain period hPeriod green inputs condition :
        Set (canonicalScalarClosedOperatorDomain
          (strongSystem period hPeriod green inputs))) :=
  canonicalScalarClosedLagrangianAdjointDomain_eq
    (strongSystem period hPeriod green inputs)
    (strongSystem_closable period hPeriod green inputs)
    (strongSystemGraphBound period hPeriod green inputs)
    condition

/-- Correct strong physical system certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    Function.Surjective (strongSystem period hPeriod green inputs).boundaryTrace ∧
      CanonicalScalarGraphClosable (strongSystem period hPeriod green inputs) ∧
      (∀ first second : (physicalTriple period hPeriod green inputs).MaximalDomain,
        inner Real ((strongSystem period hPeriod green inputs).operator first)
              ((strongSystem period hPeriod green inputs).inclusion second) -
            inner Real ((strongSystem period hPeriod green inputs).inclusion first)
              ((strongSystem period hPeriod green inputs).operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            ((strongSystem period hPeriod green inputs).boundaryTrace first)
            ((strongSystem period hPeriod green inputs).boundaryTrace second)) :=
  strongSystem_certificate (physicalTriple period hPeriod green inputs)
    (strongAdjointTestCore period hPeriod green inputs)

end CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D
end JanusFormal
