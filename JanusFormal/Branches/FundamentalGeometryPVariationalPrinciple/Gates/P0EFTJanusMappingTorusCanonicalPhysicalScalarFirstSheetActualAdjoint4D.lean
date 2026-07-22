import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCompletedBoundaryDomains4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D

/-!
# Actual Hilbert adjoints for the physical scalar triple

Maximal regularity identifies every Hilbert adjoint pair with a vector of the
completed maximal graph.  Green's identity and Lagrangian maximality then give
self-adjointness of the selected physical boundary realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetActualAdjoint4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCompletedBoundaryDomains4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.CanonicalScalarCompletedBoundaryTripleData

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period
private abbrev BulkL2 := CanonicalPhysicalBulkL2 period hPeriod

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

/-- Actual adjoint domain in physical bulk L2. -/
def physicalActualAdjointDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) : Set (BulkL2 period hPeriod) :=
  actualAdjointDomain (inputs.triple period hPeriod green) condition

/-- Original realization domain in physical bulk L2. -/
def physicalRealizationDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) : Set (BulkL2 period hPeriod) :=
  realizationDomain (inputs.triple period hPeriod green) condition

/-- Physical maximal-adjoint regularity input. -/
abbrev PhysicalMaximalAdjointRegularity
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  MaximalAdjointRegularity (inputs.triple period hPeriod green) condition

/-- Actual Hilbert adjoint domain equals the selected realization domain. -/
theorem physicalActualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (regularity : PhysicalMaximalAdjointRegularity
      period hPeriod green inputs condition) :
    physicalActualAdjointDomain period hPeriod green inputs condition =
      physicalRealizationDomain period hPeriod green inputs condition :=
  actualAdjointDomain_eq_realizationDomain
    (inputs.triple period hPeriod green) condition regularity

/-- Physical Dirichlet self-adjointness. -/
theorem physicalDirichlet_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (regularity : PhysicalMaximalAdjointRegularity period hPeriod green inputs
      (completedPhysicalDirichletCondition period)) :
    physicalActualAdjointDomain period hPeriod green inputs
        (completedPhysicalDirichletCondition period) =
      physicalRealizationDomain period hPeriod green inputs
        (completedPhysicalDirichletCondition period) :=
  physicalActualAdjointDomain_eq period hPeriod green inputs _ regularity

/-- Physical Neumann self-adjointness. -/
theorem physicalNeumann_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (regularity : PhysicalMaximalAdjointRegularity period hPeriod green inputs
      (completedPhysicalNeumannCondition period)) :
    physicalActualAdjointDomain period hPeriod green inputs
        (completedPhysicalNeumannCondition period) =
      physicalRealizationDomain period hPeriod green inputs
        (completedPhysicalNeumannCondition period) :=
  physicalActualAdjointDomain_eq period hPeriod green inputs _ regularity

/-- Physical scalar Robin self-adjointness. -/
theorem physicalScalarRobin_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (coefficient : Real)
    (regularity : PhysicalMaximalAdjointRegularity period hPeriod green inputs
      (completedPhysicalScalarRobinCondition period coefficient)) :
    physicalActualAdjointDomain period hPeriod green inputs
        (completedPhysicalScalarRobinCondition period coefficient) =
      physicalRealizationDomain period hPeriod green inputs
        (completedPhysicalScalarRobinCondition period coefficient) :=
  physicalActualAdjointDomain_eq period hPeriod green inputs _ regularity

/-- Physical operator-valued Robin self-adjointness. -/
theorem physicalOperatorRobin_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (regularity : PhysicalMaximalAdjointRegularity period hPeriod green inputs
      (completedPhysicalOperatorRobinCondition period robin hRobin)) :
    physicalActualAdjointDomain period hPeriod green inputs
        (completedPhysicalOperatorRobinCondition period robin hRobin) =
      physicalRealizationDomain period hPeriod green inputs
        (completedPhysicalOperatorRobinCondition period robin hRobin) :=
  physicalActualAdjointDomain_eq period hPeriod green inputs _ regularity

/-- Physical actual-adjoint certificate. -/
theorem physicalActualAdjoint_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (regularity : PhysicalMaximalAdjointRegularity
      period hPeriod green inputs condition) :
    physicalActualAdjointDomain period hPeriod green inputs condition =
        physicalRealizationDomain period hPeriod green inputs condition ∧
      (inputs.triple period hPeriod green).lagrangianAdjointDomain condition =
        ((inputs.triple period hPeriod green).lagrangianDomainSubmodule condition :
          Set (inputs.MaximalDomain period hPeriod green)) :=
  actualAdjoint_certificate
    (inputs.triple period hPeriod green) condition regularity

end CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetActualAdjoint4D
end JanusFormal
