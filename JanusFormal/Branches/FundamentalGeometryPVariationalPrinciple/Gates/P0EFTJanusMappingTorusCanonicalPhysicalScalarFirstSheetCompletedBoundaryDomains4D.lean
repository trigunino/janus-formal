import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

/-!
# Corrected completed physical scalar boundary domains

This file specializes the corrected completed physical boundary triple directly,
without the impossible smooth-surjectivity hypothesis.

The completed maximal graph carries a surjective paired Cauchy trace.  Pulling
back Dirichlet, Neumann, constant Robin and bounded symmetric operator-Robin
Lagrangians gives closed symmetric domains.  Their boundary-adjoint domains are
exactly the original domains by Lagrangian maximality.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCompletedBoundaryDomains4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Corrected physical Dirichlet boundary condition. -/
noncomputable def completedPhysicalDirichletCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
    (Trace := BoundaryL2 period)

/-- Corrected physical Neumann boundary condition. -/
noncomputable def completedPhysicalNeumannCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
    (Trace := BoundaryL2 period)

/-- Corrected physical constant Robin condition. -/
noncomputable def completedPhysicalScalarRobinCondition
    (coefficient : Real) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
    (Trace := BoundaryL2 period) coefficient

/-- Corrected physical bounded operator-valued Robin condition. -/
noncomputable def completedPhysicalOperatorRobinCondition
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph robin hRobin

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

/-- Value component of the corrected completed physical trace. -/
def completedValueTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    inputs.MaximalDomain green →L[Real] BoundaryL2 period :=
  (ContinuousLinearMap.fst Real (BoundaryL2 period) (BoundaryL2 period)).comp
    (inputs.boundaryTrace green)

/-- Normal component of the corrected completed physical trace. -/
def completedNormalTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    inputs.MaximalDomain green →L[Real] BoundaryL2 period :=
  (ContinuousLinearMap.snd Real (BoundaryL2 period) (BoundaryL2 period)).comp
    (inputs.boundaryTrace green)

/-- Corrected completed physical domain for an arbitrary Lagrangian condition. -/
def completedLagrangianDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  (inputs.triple green).lagrangianDomainSubmodule condition

/-- Corrected completed Dirichlet domain. -/
abbrev CompletedDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  inputs.completedLagrangianDomain green
    (completedPhysicalDirichletCondition period)

/-- Corrected completed Neumann domain. -/
abbrev CompletedNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  inputs.completedLagrangianDomain green
    (completedPhysicalNeumannCondition period)

/-- Corrected completed scalar Robin domain. -/
abbrev CompletedScalarRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (coefficient : Real) :=
  inputs.completedLagrangianDomain green
    (completedPhysicalScalarRobinCondition period coefficient)

/-- Corrected completed operator-Robin domain. -/
abbrev CompletedOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric) :=
  inputs.completedLagrangianDomain green
    (completedPhysicalOperatorRobinCondition period robin hRobin)

/-- Corrected completed Dirichlet membership. -/
theorem mem_completedDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (field : inputs.MaximalDomain green) :
    field ∈ inputs.CompletedDirichletDomain green ↔
      inputs.completedValueTrace green field = 0 := by
  change inputs.boundaryTrace green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) 1 0 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp [completedValueTrace]

/-- Corrected completed Neumann membership. -/
theorem mem_completedNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (field : inputs.MaximalDomain green) :
    field ∈ inputs.CompletedNeumannDomain green ↔
      inputs.completedNormalTrace green field = 0 := by
  change inputs.boundaryTrace green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) 0 1 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp [completedNormalTrace]

/-- Corrected completed scalar Robin membership. -/
theorem mem_completedScalarRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (coefficient : Real)
    (field : inputs.MaximalDomain green) :
    field ∈ inputs.CompletedScalarRobinDomain green coefficient ↔
      inputs.completedNormalTrace green field =
        coefficient • inputs.completedValueTrace green field := by
  change inputs.boundaryTrace green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) (-coefficient) 1 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  change -coefficient • inputs.completedValueTrace green field +
      inputs.completedNormalTrace green field = 0 ↔ _
  module

/-- Corrected completed operator-Robin membership. -/
theorem mem_completedOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (field : inputs.MaximalDomain green) :
    field ∈ inputs.CompletedOperatorRobinDomain green robin hRobin ↔
      inputs.completedNormalTrace green field =
        robin (inputs.completedValueTrace green field) := by
  change inputs.boundaryTrace green field ∈
      canonicalScalarHilbertRobinGraphSubmodule robin ↔ _
  rw [mem_canonicalScalarHilbertRobinGraphSubmodule]
  rfl

/-- Corrected completed Lagrangian inclusion. -/
def completedLagrangianInclusion
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  (inputs.triple green).lagrangianInclusion condition

/-- Corrected completed Lagrangian operator. -/
def completedLagrangianOperator
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  (inputs.triple green).lagrangianOperator condition

/-- Every corrected completed Lagrangian realization is symmetric. -/
theorem completedLagrangianOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (first second : inputs.completedLagrangianDomain green condition) :
    inner Real (inputs.completedLagrangianOperator green condition first)
          (inputs.completedLagrangianInclusion green condition second) =
      inner Real (inputs.completedLagrangianInclusion green condition first)
          (inputs.completedLagrangianOperator green condition second) :=
  (inputs.triple green).lagrangianOperator_symmetric
    condition first second

/-- Corrected completed boundary-adjoint domain equality. -/
theorem completedLagrangianAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    (inputs.triple green).lagrangianAdjointDomain condition =
      (inputs.completedLagrangianDomain green condition :
        Set (inputs.MaximalDomain green)) :=
  (inputs.triple green).lagrangianAdjointDomain_eq condition

/-- Corrected standard physical boundary-domain certificate. -/
theorem completedBoundaryDomains_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    (∀ field : inputs.MaximalDomain green,
      field ∈ inputs.CompletedDirichletDomain green ↔
        inputs.completedValueTrace green field = 0) ∧
    (∀ field : inputs.MaximalDomain green,
      field ∈ inputs.CompletedNeumannDomain green ↔
        inputs.completedNormalTrace green field = 0) ∧
    (∀ coefficient field,
      field ∈ inputs.CompletedScalarRobinDomain green coefficient ↔
        inputs.completedNormalTrace green field =
          coefficient • inputs.completedValueTrace green field) :=
  ⟨inputs.mem_completedDirichletDomain green,
    inputs.mem_completedNeumannDomain green,
    inputs.mem_completedScalarRobinDomain green⟩

end CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCompletedBoundaryDomains4D
end JanusFormal
