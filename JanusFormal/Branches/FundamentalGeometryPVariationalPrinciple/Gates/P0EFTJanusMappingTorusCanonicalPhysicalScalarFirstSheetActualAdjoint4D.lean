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
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D

variable (period : Real) (hPeriod : period ≠ 0)

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
  (inputs.triple green).actualAdjointDomain condition

/-- Original realization domain in physical bulk L2. -/
def physicalRealizationDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) : Set (BulkL2 period hPeriod) :=
  (inputs.triple green).realizationDomain condition

/-- Physical maximal-adjoint regularity input. -/
abbrev PhysicalMaximalAdjointRegularity
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  (inputs.triple green).MaximalAdjointRegularity condition

/-- Actual Hilbert adjoint domain equals the selected realization domain. -/
theorem physicalActualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (regularity : inputs.PhysicalMaximalAdjointRegularity green condition) :
    inputs.physicalActualAdjointDomain green condition =
      inputs.physicalRealizationDomain green condition :=
  (inputs.triple green).actualAdjointDomain_eq_realizationDomain
    condition regularity

/-- Physical Dirichlet self-adjointness. -/
theorem physicalDirichlet_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (regularity : inputs.PhysicalMaximalAdjointRegularity green
      (completedPhysicalDirichletCondition period)) :
    inputs.physicalActualAdjointDomain green
        (completedPhysicalDirichletCondition period) =
      inputs.physicalRealizationDomain green
        (completedPhysicalDirichletCondition period) :=
  inputs.physicalActualAdjointDomain_eq green _ regularity

/-- Physical Neumann self-adjointness. -/
theorem physicalNeumann_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (regularity : inputs.PhysicalMaximalAdjointRegularity green
      (completedPhysicalNeumannCondition period)) :
    inputs.physicalActualAdjointDomain green
        (completedPhysicalNeumannCondition period) =
      inputs.physicalRealizationDomain green
        (completedPhysicalNeumannCondition period) :=
  inputs.physicalActualAdjointDomain_eq green _ regularity

/-- Physical scalar Robin self-adjointness. -/
theorem physicalScalarRobin_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (coefficient : Real)
    (regularity : inputs.PhysicalMaximalAdjointRegularity green
      (completedPhysicalScalarRobinCondition period coefficient)) :
    inputs.physicalActualAdjointDomain green
        (completedPhysicalScalarRobinCondition period coefficient) =
      inputs.physicalRealizationDomain green
        (completedPhysicalScalarRobinCondition period coefficient) :=
  inputs.physicalActualAdjointDomain_eq green _ regularity

/-- Physical operator-valued Robin self-adjointness. -/
theorem physicalOperatorRobin_actualAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (regularity : inputs.PhysicalMaximalAdjointRegularity green
      (completedPhysicalOperatorRobinCondition period robin hRobin)) :
    inputs.physicalActualAdjointDomain green
        (completedPhysicalOperatorRobinCondition period robin hRobin) =
      inputs.physicalRealizationDomain green
        (completedPhysicalOperatorRobinCondition period robin hRobin) :=
  inputs.physicalActualAdjointDomain_eq green _ regularity

/-- Physical actual-adjoint certificate. -/
theorem physicalActualAdjoint_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (regularity : inputs.PhysicalMaximalAdjointRegularity green condition) :
    inputs.physicalActualAdjointDomain green condition =
        inputs.physicalRealizationDomain green condition ∧
      (inputs.triple green).lagrangianAdjointDomain condition =
        ((inputs.triple green).lagrangianDomainSubmodule condition :
          Set (inputs.MaximalDomain green)) :=
  (inputs.triple green).actualAdjoint_certificate condition regularity

end CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetActualAdjoint4D
end JanusFormal
