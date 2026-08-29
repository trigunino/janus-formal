import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

/-!
# Concrete first-sheet physical scalar boundary domains

The first-sheet boundary Hilbert space now supports the standard physical
Dirichlet, Neumann, constant Robin and bounded operator-valued Robin conditions.
This file pulls those conditions back to the smooth physical Euler core.

Membership is expressed directly in the concrete L2 traces.  Symmetry follows
from the physical Green identity and Lagrangianity.  Density of any selected
smooth domain then implies closability of its restricted operator by the generic
dense-symmetric theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryDomains4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Physical first-sheet Dirichlet condition. -/
noncomputable def canonicalPhysicalScalarFirstSheetDirichletCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
    (Trace := BoundaryL2 period)

/-- Physical first-sheet Neumann condition. -/
noncomputable def canonicalPhysicalScalarFirstSheetNeumannCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
    (Trace := BoundaryL2 period)

/-- Physical first-sheet constant Robin condition. -/
noncomputable def canonicalPhysicalScalarFirstSheetRobinCondition
    (coefficient : Real) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
    (Trace := BoundaryL2 period) coefficient

/-- Physical first-sheet bounded operator-valued Robin condition. -/
noncomputable def canonicalPhysicalScalarFirstSheetOperatorRobinCondition
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph robin hRobin

namespace CanonicalPhysicalScalarFirstSheetGreenData

/-- Smooth physical Dirichlet core. -/
abbrev SmoothDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :=
  green.smoothLagrangianDomainSubmodule
    (canonicalPhysicalScalarFirstSheetDirichletCondition period)

/-- Smooth physical Neumann core. -/
abbrev SmoothNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :=
  green.smoothLagrangianDomainSubmodule
    (canonicalPhysicalScalarFirstSheetNeumannCondition period)

/-- Smooth physical constant Robin core. -/
abbrev SmoothRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coefficient : Real) :=
  green.smoothLagrangianDomainSubmodule
    (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient)

/-- Smooth physical operator-valued Robin core. -/
abbrev SmoothOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric) :=
  green.smoothLagrangianDomainSubmodule
    (canonicalPhysicalScalarFirstSheetOperatorRobinCondition
      period robin hRobin)

/-- Dirichlet membership is vanishing first-sheet value trace. -/
theorem mem_smoothDirichletDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (field : SmoothQuotientField period hPeriod Real) :
    field ∈ green.SmoothDirichletDomain period hPeriod ↔
      smoothCanonicalPhysicalScalarFirstSheetValueL2
        period hPeriod field = 0 := by
  change green.system.boundaryTrace field ∈
      (canonicalPhysicalScalarFirstSheetDirichletCondition period).subspace ↔ _
  change green.system.boundaryTrace field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) 1 0 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp [CanonicalPhysicalScalarFirstSheetGreenData.system,
    CanonicalPhysicalScalarFirstSheetGreenData.boundaryTrace,
    smoothCanonicalPhysicalScalarFirstSheetCauchyTrace]

/-- Neumann membership is vanishing first-sheet normal trace. -/
theorem mem_smoothNeumannDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (field : SmoothQuotientField period hPeriod Real) :
    field ∈ green.SmoothNeumannDomain period hPeriod ↔
      smoothCanonicalPhysicalScalarFirstSheetNormalL2
        period hPeriod field = 0 := by
  change green.system.boundaryTrace field ∈
      (canonicalPhysicalScalarFirstSheetNeumannCondition period).subspace ↔ _
  change green.system.boundaryTrace field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) 0 1 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  simp [CanonicalPhysicalScalarFirstSheetGreenData.system,
    CanonicalPhysicalScalarFirstSheetGreenData.boundaryTrace,
    smoothCanonicalPhysicalScalarFirstSheetCauchyTrace]

/-- Constant Robin membership is `normal = coefficient • value`. -/
theorem mem_smoothRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coefficient : Real)
    (field : SmoothQuotientField period hPeriod Real) :
    field ∈ green.SmoothRobinDomain period hPeriod coefficient ↔
      smoothCanonicalPhysicalScalarFirstSheetNormalL2
          period hPeriod field =
        coefficient • smoothCanonicalPhysicalScalarFirstSheetValueL2
          period hPeriod field := by
  change green.system.boundaryTrace field ∈
      (canonicalPhysicalScalarFirstSheetRobinCondition
        period coefficient).subspace ↔ _
  change green.system.boundaryTrace field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) (-coefficient) 1 ↔ _
  rw [mem_canonicalScalarHilbertSeparatedBoundarySubmodule]
  change -coefficient •
      smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field +
      smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field = 0 ↔ _
  module

/-- Operator-valued Robin membership is the expected graph equation. -/
theorem mem_smoothOperatorRobinDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (field : SmoothQuotientField period hPeriod Real) :
    field ∈ green.SmoothOperatorRobinDomain period hPeriod robin hRobin ↔
      smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field =
        robin (smoothCanonicalPhysicalScalarFirstSheetValueL2
          period hPeriod field) := by
  change green.system.boundaryTrace field ∈
      canonicalScalarHilbertRobinGraphSubmodule robin ↔ _
  rw [mem_canonicalScalarHilbertRobinGraphSubmodule]
  rfl

/-- Symmetry of the smooth Dirichlet realization. -/
theorem smoothDirichletOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (first second : green.SmoothDirichletDomain period hPeriod) :
    inner Real
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetDirichletCondition period) first)
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetDirichletCondition period) second) =
      inner Real
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetDirichletCondition period) first)
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetDirichletCondition period) second) :=
  green.smoothLagrangianOperator_symmetric
    (canonicalPhysicalScalarFirstSheetDirichletCondition period) first second

/-- Symmetry of the smooth Neumann realization. -/
theorem smoothNeumannOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (first second : green.SmoothNeumannDomain period hPeriod) :
    inner Real
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetNeumannCondition period) first)
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetNeumannCondition period) second) =
      inner Real
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetNeumannCondition period) first)
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetNeumannCondition period) second) :=
  green.smoothLagrangianOperator_symmetric
    (canonicalPhysicalScalarFirstSheetNeumannCondition period) first second

/-- Symmetry of every smooth constant Robin realization. -/
theorem smoothRobinOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (coefficient : Real)
    (first second : green.SmoothRobinDomain period hPeriod coefficient) :
    inner Real
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient) first)
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient) second) =
      inner Real
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient) first)
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient) second) :=
  green.smoothLagrangianOperator_symmetric
    (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient)
    first second

/-- Symmetry of every smooth bounded symmetric operator-Robin realization. -/
theorem smoothOperatorRobinOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (robin : BoundaryL2 period →L[Real] BoundaryL2 period)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (first second : green.SmoothOperatorRobinDomain
      period hPeriod robin hRobin) :
    inner Real
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetOperatorRobinCondition
            period robin hRobin) first)
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetOperatorRobinCondition
            period robin hRobin) second) =
      inner Real
        (green.smoothLagrangianInclusion
          (canonicalPhysicalScalarFirstSheetOperatorRobinCondition
            period robin hRobin) first)
        (green.smoothLagrangianOperator
          (canonicalPhysicalScalarFirstSheetOperatorRobinCondition
            period robin hRobin) second) :=
  green.smoothLagrangianOperator_symmetric
    (canonicalPhysicalScalarFirstSheetOperatorRobinCondition
      period robin hRobin) first second

/-- Density package for the four standard physical smooth domains. -/
structure StandardBoundaryDomainDensityData
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) where
  dirichlet : DenseRange
    (green.smoothLagrangianInclusion
      (canonicalPhysicalScalarFirstSheetDirichletCondition period))
  neumann : DenseRange
    (green.smoothLagrangianInclusion
      (canonicalPhysicalScalarFirstSheetNeumannCondition period))
  scalarRobin : ∀ coefficient : Real, DenseRange
    (green.smoothLagrangianInclusion
      (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient))

/-- Density closes all standard restricted graphs. -/
theorem StandardBoundaryDomainDensityData.closable
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (density : green.StandardBoundaryDomainDensityData period hPeriod) :
    CanonicalScalarGraphClosable
        (green.restrictedSymmetricSystem
          (canonicalPhysicalScalarFirstSheetDirichletCondition period)) ∧
      CanonicalScalarGraphClosable
        (green.restrictedSymmetricSystem
          (canonicalPhysicalScalarFirstSheetNeumannCondition period)) ∧
      (∀ coefficient : Real,
        CanonicalScalarGraphClosable
          (green.restrictedSymmetricSystem
            (canonicalPhysicalScalarFirstSheetRobinCondition
              period coefficient))) :=
  ⟨green.restrictedSystem_closable_of_dense
      (canonicalPhysicalScalarFirstSheetDirichletCondition period)
      density.dirichlet,
    green.restrictedSystem_closable_of_dense
      (canonicalPhysicalScalarFirstSheetNeumannCondition period)
      density.neumann,
    fun coefficient =>
      green.restrictedSystem_closable_of_dense
        (canonicalPhysicalScalarFirstSheetRobinCondition period coefficient)
        (density.scalarRobin coefficient)⟩

/-- Standard physical boundary-domain certificate. -/
theorem standardBoundaryDomains_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :
    (∀ field, field ∈ green.SmoothDirichletDomain period hPeriod ↔
      smoothCanonicalPhysicalScalarFirstSheetValueL2
        period hPeriod field = 0) ∧
    (∀ field, field ∈ green.SmoothNeumannDomain period hPeriod ↔
      smoothCanonicalPhysicalScalarFirstSheetNormalL2
        period hPeriod field = 0) ∧
    (∀ coefficient field,
      field ∈ green.SmoothRobinDomain period hPeriod coefficient ↔
        smoothCanonicalPhysicalScalarFirstSheetNormalL2
            period hPeriod field =
          coefficient • smoothCanonicalPhysicalScalarFirstSheetValueL2
            period hPeriod field) :=
  ⟨green.mem_smoothDirichletDomain period hPeriod,
    green.mem_smoothNeumannDomain period hPeriod,
    green.mem_smoothRobinDomain period hPeriod⟩

end CanonicalPhysicalScalarFirstSheetGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryDomains4D
end JanusFormal
