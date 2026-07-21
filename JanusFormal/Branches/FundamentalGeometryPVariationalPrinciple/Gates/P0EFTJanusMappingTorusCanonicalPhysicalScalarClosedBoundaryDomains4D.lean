import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryDomains4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

/-!
# Closed physical scalar Dirichlet, Neumann and Robin domains

Once the physical maximal closure data are supplied, every first-sheet closed
Lagrangian boundary condition pulls back to an actual closed operator domain.
This file specializes the construction to Dirichlet, Neumann, scalar Robin and
bounded symmetric operator-valued Robin data.

The domains are symmetric and equal to their boundary-adjoint domains.  The only
additional theorem needed to call them genuinely self-adjoint in the unbounded
Hilbert-space sense is the concrete characterization of the actual Hilbert
adjoint by the Green boundary test.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarClosedBoundaryDomains4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryDomains4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCore4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

namespace CanonicalPhysicalScalarFirstSheetGreenData.MaximalClosureData

/-- Closed physical domain for an arbitrary first-sheet Lagrangian condition. -/
abbrev ClosedLagrangianDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    green.system (closure.closable green) (closure.graphBound green) condition

/-- Closed physical Dirichlet domain. -/
abbrev ClosedDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :=
  closure.ClosedLagrangianDomain green
    (canonicalPhysicalScalarFirstSheetDirichletCondition period)

/-- Closed physical Neumann domain. -/
abbrev ClosedNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :=
  closure.ClosedLagrangianDomain green
    (canonicalPhysicalScalarFirstSheetNeumannCondition period)

/-- Closed physical scalar Robin domain. -/
abbrev ClosedRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (coefficient : Real) :=
  closure.ClosedLagrangianDomain green
    (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient)

/-- Closed physical operator-valued Robin domain. -/
abbrev ClosedOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric) :=
  closure.ClosedLagrangianDomain green
    (canonicalPhysicalScalarFirstSheetOperatorRobinCondition
      period robin hRobin)

/-- Value component of the completed physical boundary trace. -/
noncomputable def closedValueTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    closure.ClosedDomain green →ₗ[Real] BoundaryL2 period :=
  (LinearMap.fst Real (BoundaryL2 period) (BoundaryL2 period)).comp
    (closure.closedBoundaryTrace green)

/-- Normal component of the completed physical boundary trace. -/
noncomputable def closedNormalTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    closure.ClosedDomain green →ₗ[Real] BoundaryL2 period :=
  (LinearMap.snd Real (BoundaryL2 period) (BoundaryL2 period)).comp
    (closure.closedBoundaryTrace green)

/-- Closed Dirichlet membership. -/
theorem mem_closedDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (field : closure.ClosedDomain green) :
    field ∈ closure.ClosedDirichletDomain green ↔
      closure.closedValueTrace green field = 0 := by
  change closure.closedBoundaryTrace green field ∈
      (canonicalPhysicalScalarFirstSheetDirichletCondition period).subspace ↔ _
  change closure.closedBoundaryTrace green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) 1 0 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp [closedValueTrace]

/-- Closed Neumann membership. -/
theorem mem_closedNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (field : closure.ClosedDomain green) :
    field ∈ closure.ClosedNeumannDomain green ↔
      closure.closedNormalTrace green field = 0 := by
  change closure.closedBoundaryTrace green field ∈
      (canonicalPhysicalScalarFirstSheetNeumannCondition period).subspace ↔ _
  change closure.closedBoundaryTrace green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) 0 1 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp [closedNormalTrace]

/-- Closed constant Robin membership. -/
theorem mem_closedRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (coefficient : Real)
    (field : closure.ClosedDomain green) :
    field ∈ closure.ClosedRobinDomain green coefficient ↔
      closure.closedNormalTrace green field =
        coefficient • closure.closedValueTrace green field := by
  change closure.closedBoundaryTrace green field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) (-coefficient) 1 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  change -coefficient • closure.closedValueTrace green field +
      closure.closedNormalTrace green field = 0 ↔ _
  module

/-- Closed operator-Robin membership. -/
theorem mem_closedOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (field : closure.ClosedDomain green) :
    field ∈ closure.ClosedOperatorRobinDomain green robin hRobin ↔
      closure.closedNormalTrace green field =
        robin (closure.closedValueTrace green field) := by
  change closure.closedBoundaryTrace green field ∈
      canonicalScalarHilbertRobinGraphSubmodule robin ↔ _
  rw [mem_canonicalScalarHilbertRobinGraphSubmodule]
  rfl

/-- Closed-domain operator for an arbitrary physical Lagrangian condition. -/
noncomputable def closedLagrangianOperator
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    closure.ClosedLagrangianDomain green condition →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  canonicalScalarClosedLagrangianDomainOperator
    green.system (closure.closable green) (closure.graphBound green) condition

/-- Ambient inclusion of a closed physical Lagrangian domain. -/
def closedLagrangianInclusion
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    closure.ClosedLagrangianDomain green condition →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  canonicalScalarClosedLagrangianDomainInclusion
    green.system (closure.closable green) (closure.graphBound green) condition

/-- Every closed physical Lagrangian realization is symmetric. -/
theorem closedLagrangianOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (first second : closure.ClosedLagrangianDomain green condition) :
    inner Real (closure.closedLagrangianOperator green condition first)
          (closure.closedLagrangianInclusion green condition second) =
      inner Real (closure.closedLagrangianInclusion green condition first)
          (closure.closedLagrangianOperator green condition second) :=
  canonicalScalarClosedLagrangianDomainOperator_symmetric
    green.system (closure.closable green) (closure.graphBound green)
      condition first second

/-- Boundary-adjoint maximality of every physical closed Lagrangian domain. -/
theorem closedLagrangianBoundaryAdjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    canonicalScalarClosedLagrangianAdjointDomain
        green.system (closure.closable green) (closure.graphBound green)
          condition =
      (closure.ClosedLagrangianDomain green condition :
        Set (closure.ClosedDomain green)) :=
  canonicalScalarClosedLagrangianAdjointDomain_eq
    green.system (closure.closable green) (closure.graphBound green) condition

/-- Concrete characterization of the actual unbounded Hilbert adjoint domain by
the physical Green boundary test. -/
structure ActualHilbertAdjointCharacterization
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) where
  adjointDomain : Set (closure.ClosedDomain green)
  mem_adjointDomain_iff : ∀ candidate : closure.ClosedDomain green,
    candidate ∈ adjointDomain ↔
      canonicalScalarClosedLagrangianAdjointAdmissible
        green.system (closure.closable green) (closure.graphBound green)
          condition candidate

/-- The actual Hilbert adjoint domain equals the physical boundary domain. -/
theorem ActualHilbertAdjointCharacterization.adjointDomain_eq
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period))
    (characterization : closure.ActualHilbertAdjointCharacterization
      green condition) :
    characterization.adjointDomain =
      (closure.ClosedLagrangianDomain green condition :
        Set (closure.ClosedDomain green)) := by
  ext candidate
  rw [characterization.mem_adjointDomain_iff]
  exact canonicalScalarClosedLagrangianAdjointAdmissible_iff_mem
    green.system (closure.closable green) (closure.graphBound green)
      condition candidate

/-- Closed physical boundary-domain certificate. -/
theorem closedBoundaryDomains_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period)) :
    (∀ first second : closure.ClosedLagrangianDomain green condition,
      inner Real (closure.closedLagrangianOperator green condition first)
            (closure.closedLagrangianInclusion green condition second) =
        inner Real (closure.closedLagrangianInclusion green condition first)
            (closure.closedLagrangianOperator green condition second)) ∧
      canonicalScalarClosedLagrangianAdjointDomain
          green.system (closure.closable green) (closure.graphBound green)
            condition =
        (closure.ClosedLagrangianDomain green condition :
          Set (closure.ClosedDomain green)) :=
  ⟨closure.closedLagrangianOperator_symmetric green condition,
    closure.closedLagrangianBoundaryAdjointDomain_eq green condition⟩

end CanonicalPhysicalScalarFirstSheetGreenData.MaximalClosureData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarClosedBoundaryDomains4D
end JanusFormal
