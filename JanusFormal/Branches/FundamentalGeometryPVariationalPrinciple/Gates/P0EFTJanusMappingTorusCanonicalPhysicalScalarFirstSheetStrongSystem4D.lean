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
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

/-- Correct completed physical boundary triple. -/
def physicalTriple
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  inputs.triple green

/-- Strong physical system whose domain is the completed maximal graph. -/
def strongSystem
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  (inputs.physicalTriple green).toStrongSystem

/-- Smooth minimal core mapped into the completed maximal graph. -/
def smoothMinimalToMaximalGraph
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    green.core.minimalDomainSubmodule →ₗ[Real]
      (inputs.physicalTriple green).MaximalDomain :=
  (canonicalScalarGreenCoreToGraph green.core).comp
    green.core.minimalDomainSubmodule.subtype

/-- The completed trace of a smooth minimal-core vector vanishes. -/
theorem completedTrace_smoothMinimal_zero
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (test : green.core.minimalDomainSubmodule) :
    canonicalScalarGreenCoreCompletedBoundaryTrace
        green.core (inputs.traceBound green)
        (inputs.smoothMinimalToMaximalGraph green test) = 0 := by
  rw [canonicalScalarGreenCoreCompletedBoundaryTrace_smooth]
  exact LinearMap.mem_ker.mp test.2

/-- Formal-adjoint pairing of an arbitrary completed maximal vector with a
smooth zero-Cauchy test. -/
theorem maximal_minimal_pairing
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (field : (inputs.physicalTriple green).MaximalDomain)
    (test : green.core.minimalDomainSubmodule) :
    inner Real (canonicalScalarGreenCoreGraphOperator green.core field)
        (green.core.minimalInclusion test) =
      inner Real (canonicalScalarGreenCoreGraphInclusion green.core field)
        (green.core.minimalOperator test) := by
  have hGreen := canonicalScalarGreenCoreCompletedGreenIdentity
    green.core (inputs.traceBound green) field
      (inputs.smoothMinimalToMaximalGraph green test)
  unfold canonicalScalarGreenCoreCompletedBoundaryPairing at hGreen
  rw [inputs.completedTrace_smoothMinimal_zero green test,
    canonicalScalarHilbertBoundarySymplecticForm_zero_right] at hGreen
  linarith

/-- Dense formal-adjoint test package for the strong presentation. -/
def strongAdjointTestCore
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    (inputs.physicalTriple green).StrongAdjointTestCore
      (TestDomain := green.core.minimalDomainSubmodule) where
  inclusion := green.core.minimalInclusion
  operator := green.core.minimalOperator
  dense := inputs.minimalDense
  pairing := inputs.maximal_minimal_pairing green

/-- The corrected strong physical system is closable. -/
theorem strongSystem_closable
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    CanonicalScalarGraphClosable (inputs.strongSystem green) :=
  (inputs.physicalTriple green).toStrongSystem_closable
    (inputs.strongAdjointTestCore green)

/-- Graph bound for the corrected strong physical system. -/
def strongSystemGraphBound
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    HasCanonicalScalarHilbertBoundaryGraphBound
      (inputs.strongSystem green) :=
  (inputs.physicalTriple green).toStrongSystemBoundaryGraphBound

/-- Correct closed strong-domain Lagrangian submodule. -/
def strongClosedLagrangianDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    (inputs.strongSystem green)
    (inputs.strongSystem_closable green)
    (inputs.strongSystemGraphBound green)
    condition

/-- Strong-system physical boundary-adjoint maximality. -/
theorem strongClosedLagrangianAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    canonicalScalarClosedLagrangianAdjointDomain
        (inputs.strongSystem green)
        (inputs.strongSystem_closable green)
        (inputs.strongSystemGraphBound green)
        condition =
      (inputs.strongClosedLagrangianDomain green condition :
        Set (canonicalScalarClosedOperatorDomain
          (inputs.strongSystem green))) :=
  canonicalScalarClosedLagrangianAdjointDomain_eq
    (inputs.strongSystem green)
    (inputs.strongSystem_closable green)
    (inputs.strongSystemGraphBound green)
    condition

/-- Correct strong physical system certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    Function.Surjective (inputs.strongSystem green).boundaryTrace ∧
      CanonicalScalarGraphClosable (inputs.strongSystem green) ∧
      (∀ first second : (inputs.physicalTriple green).MaximalDomain,
        inner Real ((inputs.strongSystem green).operator first)
              ((inputs.strongSystem green).inclusion second) -
            inner Real ((inputs.strongSystem green).inclusion first)
              ((inputs.strongSystem green).operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            ((inputs.strongSystem green).boundaryTrace first)
            ((inputs.strongSystem green).boundaryTrace second)) :=
  (inputs.physicalTriple green).strongSystem_certificate
    (inputs.strongAdjointTestCore green)

end CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D
end JanusFormal
