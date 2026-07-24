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

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

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
    inputs.MaximalDomain period hPeriod green →L[Real] BoundaryL2 period :=
  (ContinuousLinearMap.fst Real (BoundaryL2 period) (BoundaryL2 period)).comp
    (inputs.boundaryTrace period hPeriod green)

/-- Normal component of the corrected completed physical trace. -/
def completedNormalTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    inputs.MaximalDomain period hPeriod green →L[Real] BoundaryL2 period :=
  (ContinuousLinearMap.snd Real (BoundaryL2 period) (BoundaryL2 period)).comp
    (inputs.boundaryTrace period hPeriod green)

/-- Corrected completed physical domain for an arbitrary Lagrangian condition. -/
def completedLagrangianDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  (inputs.triple period hPeriod green).lagrangianDomainSubmodule condition

/-- Corrected completed Dirichlet domain. -/
abbrev CompletedDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  completedLagrangianDomain period hPeriod green inputs
    (completedPhysicalDirichletCondition period)

/-- Corrected completed Neumann domain. -/
abbrev CompletedNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  completedLagrangianDomain period hPeriod green inputs
    (completedPhysicalNeumannCondition period)

/-- Corrected completed scalar Robin domain. -/
abbrev CompletedScalarRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (coefficient : Real) :=
  completedLagrangianDomain period hPeriod green inputs
    (completedPhysicalScalarRobinCondition period coefficient)

/-- Corrected completed operator-Robin domain. -/
abbrev CompletedOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric) :=
  completedLagrangianDomain period hPeriod green inputs
    (completedPhysicalOperatorRobinCondition period robin hRobin)

/-- Corrected completed Dirichlet membership. -/
theorem mem_completedDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (field : inputs.MaximalDomain period hPeriod green) :
    field ∈ CompletedDirichletDomain period hPeriod green inputs ↔
      completedValueTrace period hPeriod green inputs field = 0 := by
  change inputs.boundaryTrace period hPeriod green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) 1 0 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp [completedValueTrace]

/-- Corrected completed Neumann membership. -/
theorem mem_completedNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (field : inputs.MaximalDomain period hPeriod green) :
    field ∈ CompletedNeumannDomain period hPeriod green inputs ↔
      completedNormalTrace period hPeriod green inputs field = 0 := by
  change inputs.boundaryTrace period hPeriod green field ∈
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
    (field : inputs.MaximalDomain period hPeriod green) :
    field ∈ CompletedScalarRobinDomain period hPeriod green inputs coefficient ↔
      completedNormalTrace period hPeriod green inputs field =
        coefficient • completedValueTrace period hPeriod green inputs field := by
  change inputs.boundaryTrace period hPeriod green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) (-coefficient) 1 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp only [one_smul]
  change -coefficient • completedValueTrace period hPeriod green inputs field +
      completedNormalTrace period hPeriod green inputs field = 0 ↔ _
  constructor
  · intro h
    simpa using eq_neg_of_add_eq_zero_right h
  · intro h
    rw [h]
    simp

/-- Corrected completed operator-Robin membership. -/
theorem mem_completedOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (field : inputs.MaximalDomain period hPeriod green) :
    field ∈ CompletedOperatorRobinDomain period hPeriod green inputs robin hRobin ↔
      completedNormalTrace period hPeriod green inputs field =
        robin (completedValueTrace period hPeriod green inputs field) := by
  change inputs.boundaryTrace period hPeriod green field ∈
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
  (inputs.triple period hPeriod green).lagrangianInclusion condition

/-- Corrected completed Lagrangian operator. -/
def completedLagrangianOperator
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  (inputs.triple period hPeriod green).lagrangianOperator condition

/-- Every corrected completed Lagrangian realization is symmetric. -/
theorem completedLagrangianOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (first second : completedLagrangianDomain period hPeriod green inputs condition) :
    inner Real (completedLagrangianOperator period hPeriod green inputs condition first)
          (completedLagrangianInclusion period hPeriod green inputs condition second) =
      inner Real (completedLagrangianInclusion period hPeriod green inputs condition first)
          (completedLagrangianOperator period hPeriod green inputs condition second) :=
  (inputs.triple period hPeriod green).lagrangianOperator_symmetric
    condition first second

/-- Corrected completed boundary-adjoint domain equality. -/
theorem completedLagrangianAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    (inputs.triple period hPeriod green).lagrangianAdjointDomain condition =
      (completedLagrangianDomain period hPeriod green inputs condition :
        Set (inputs.MaximalDomain period hPeriod green)) :=
  (inputs.triple period hPeriod green).lagrangianAdjointDomain_eq condition

/-- Corrected standard physical boundary-domain certificate. -/
theorem completedBoundaryDomains_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    (∀ field : inputs.MaximalDomain period hPeriod green,
      field ∈ CompletedDirichletDomain period hPeriod green inputs ↔
        completedValueTrace period hPeriod green inputs field = 0) ∧
    (∀ field : inputs.MaximalDomain period hPeriod green,
      field ∈ CompletedNeumannDomain period hPeriod green inputs ↔
        completedNormalTrace period hPeriod green inputs field = 0) ∧
    (∀ coefficient field,
      field ∈ CompletedScalarRobinDomain period hPeriod green inputs coefficient ↔
        completedNormalTrace period hPeriod green inputs field =
          coefficient • completedValueTrace period hPeriod green inputs field) :=
  ⟨mem_completedDirichletDomain period hPeriod green inputs,
    mem_completedNeumannDomain period hPeriod green inputs,
    mem_completedScalarRobinDomain period hPeriod green inputs⟩

end CanonicalPhysicalScalarFirstSheetGreenCoreData.CompletedBoundaryTripleInputs

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCompletedBoundaryDomains4D
end JanusFormal
