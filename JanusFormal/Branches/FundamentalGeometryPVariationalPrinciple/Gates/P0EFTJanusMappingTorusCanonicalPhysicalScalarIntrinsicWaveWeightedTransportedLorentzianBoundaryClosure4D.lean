import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D

/-!
# Lorentzian scalar Green and smooth boundary closure

This is the safe conditional endpoint for the intrinsic Lorentzian wave
operator. Given the canonical local-divergence/cut-bulk identity, it uses the
derived weighted global Green package. In particular it does not assume an
elliptic graph estimate, bounded `L² → L²` tangential residual operators,
shifted coercivity, Rellich compactness or semibounded spectrum.

Dirichlet, Neumann and constant Robin conditions are imposed on the smooth
dense Green core.  Their operators are symmetric by the exact Lorentzian Green
identity.  Elliptic/coercive spectral conclusions belong to a separate
auxiliary realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev SmoothDomain :=
  SmoothQuotientField period hPeriod Real

private abbrev BulkL2 :=
  CanonicalPhysicalBulkL2 period hPeriod

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData

/-- Pullback of a Lagrangian boundary condition to the smooth Lorentzian core. -/
def smoothLagrangianDomainSubmodule
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (condition :
      CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period)) :
    Submodule Real (SmoothDomain period hPeriod) :=
  condition.subspace.comap
    (data.greenCore period hPeriod).core.boundaryTrace

@[simp] theorem mem_smoothLagrangianDomainSubmodule
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (condition :
      CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period))
    (field : SmoothDomain period hPeriod) :
    field ∈ smoothLagrangianDomainSubmodule period hPeriod data condition ↔
      (data.greenCore period hPeriod).core.boundaryTrace field ∈
        condition.subspace :=
  Iff.rfl

/-- Bulk inclusion restricted to a smooth Lorentzian boundary domain. -/
def smoothLagrangianInclusion
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (condition :
      CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period)) :
    smoothLagrangianDomainSubmodule period hPeriod data condition →ₗ[Real]
      BulkL2 period hPeriod :=
  (data.greenCore period hPeriod).core.inclusion.comp
    (smoothLagrangianDomainSubmodule
      period hPeriod data condition).subtype

/-- Lorentzian Euler operator restricted to a smooth boundary domain. -/
def smoothLagrangianOperator
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (condition :
      CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period)) :
    smoothLagrangianDomainSubmodule period hPeriod data condition →ₗ[Real]
      BulkL2 period hPeriod :=
  (data.greenCore period hPeriod).core.operator.comp
    (smoothLagrangianDomainSubmodule
      period hPeriod data condition).subtype

/-- Every smooth Lorentzian Lagrangian realization is symmetric. -/
theorem smoothLagrangianOperator_symmetric
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (condition :
      CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period))
    (first second :
      smoothLagrangianDomainSubmodule period hPeriod data condition) :
    inner Real (smoothLagrangianOperator period hPeriod data condition first)
          (smoothLagrangianInclusion period hPeriod data condition second) =
      inner Real (smoothLagrangianInclusion period hPeriod data condition first)
          (smoothLagrangianOperator period hPeriod data condition second) := by
  have hBoundary := condition.pairing_eq_zero
    ((data.greenCore period hPeriod).core.boundaryTrace first.1)
    ((data.greenCore period hPeriod).core.boundaryTrace second.1)
    first.2 second.2
  have hGreen :=
    (data.greenCore period hPeriod).core.green_identity first.1 second.1
  apply sub_eq_zero.mp
  simpa [smoothLagrangianOperator, smoothLagrangianInclusion, hBoundary]
    using hGreen

/-- Smooth physical Dirichlet domain. -/
abbrev SmoothDirichletDomain
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :=
  smoothLagrangianDomainSubmodule period hPeriod data
    (CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
      (Trace := BoundaryL2 period))

/-- Smooth physical Neumann domain. -/
abbrev SmoothNeumannDomain
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :=
  smoothLagrangianDomainSubmodule period hPeriod data
    (CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
      (Trace := BoundaryL2 period))

/-- Smooth physical constant Robin domain. -/
abbrev SmoothRobinDomain
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (coefficient : Real) :=
  smoothLagrangianDomainSubmodule period hPeriod data
    (CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
      (Trace := BoundaryL2 period) coefficient)

/-- Dirichlet means vanishing value trace. -/
theorem mem_smoothDirichletDomain
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (field : SmoothDomain period hPeriod) :
    field ∈ SmoothDirichletDomain period hPeriod data ↔
      ((data.greenCore period hPeriod).core.boundaryTrace field).1 = 0 := by
  change (data.greenCore period hPeriod).core.boundaryTrace field ∈
      canonicalScalarHilbertDirichletBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertDirichletBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Neumann means vanishing normal trace. -/
theorem mem_smoothNeumannDomain
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (field : SmoothDomain period hPeriod) :
    field ∈ SmoothNeumannDomain period hPeriod data ↔
      ((data.greenCore period hPeriod).core.boundaryTrace field).2 = 0 := by
  change (data.greenCore period hPeriod).core.boundaryTrace field ∈
      canonicalScalarHilbertNeumannBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertNeumannBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Robin means `normal = coefficient • value`. -/
theorem mem_smoothRobinDomain
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (coefficient : Real)
    (field : SmoothDomain period hPeriod) :
    field ∈ SmoothRobinDomain period hPeriod data coefficient ↔
      ((data.greenCore period hPeriod).core.boundaryTrace field).2 =
        coefficient •
          ((data.greenCore period hPeriod).core.boundaryTrace field).1 := by
  change (data.greenCore period hPeriod).core.boundaryTrace field ∈
      canonicalScalarHilbertRobinBoundarySubmodule
        (Trace := BoundaryL2 period) coefficient ↔ _
  exact mem_canonicalScalarHilbertRobinBoundarySubmodule
    (Trace := BoundaryL2 period) coefficient _

/-- Symmetry of the smooth Dirichlet realization. -/
theorem smoothDirichletOperator_symmetric
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (first second : SmoothDirichletDomain period hPeriod data) :
    inner Real
        (smoothLagrangianOperator period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
            (Trace := BoundaryL2 period)) first)
        (smoothLagrangianInclusion period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
            (Trace := BoundaryL2 period)) second) =
      inner Real
        (smoothLagrangianInclusion period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
            (Trace := BoundaryL2 period)) first)
        (smoothLagrangianOperator period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
            (Trace := BoundaryL2 period)) second) :=
  smoothLagrangianOperator_symmetric period hPeriod data _ first second

/-- Symmetry of the smooth Neumann realization. -/
theorem smoothNeumannOperator_symmetric
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (first second : SmoothNeumannDomain period hPeriod data) :
    inner Real
        (smoothLagrangianOperator period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
            (Trace := BoundaryL2 period)) first)
        (smoothLagrangianInclusion period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
            (Trace := BoundaryL2 period)) second) =
      inner Real
        (smoothLagrangianInclusion period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
            (Trace := BoundaryL2 period)) first)
        (smoothLagrangianOperator period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
            (Trace := BoundaryL2 period)) second) :=
  smoothLagrangianOperator_symmetric period hPeriod data _ first second

/-- Symmetry of every smooth constant Robin realization. -/
theorem smoothRobinOperator_symmetric
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (coefficient : Real)
    (first second : SmoothRobinDomain period hPeriod data coefficient) :
    inner Real
        (smoothLagrangianOperator period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
            (Trace := BoundaryL2 period) coefficient) first)
        (smoothLagrangianInclusion period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
            (Trace := BoundaryL2 period) coefficient) second) =
      inner Real
        (smoothLagrangianInclusion period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
            (Trace := BoundaryL2 period) coefficient) first)
        (smoothLagrangianOperator period hPeriod data
          (CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
            (Trace := BoundaryL2 period) coefficient) second) :=
  smoothLagrangianOperator_symmetric period hPeriod data _ first second

/-- Safe Lorentzian Green endpoint: naturality, dense trace, exact Green
identity and the physical Euler equation. -/
theorem lorentzianBoundaryClosure_certificate
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod ∧
      DenseRange (data.greenCore period hPeriod).core.boundaryTrace ∧
      (∀ first second : SmoothDomain period hPeriod,
        inner Real ((data.greenCore period hPeriod).core.operator first)
              ((data.greenCore period hPeriod).core.inclusion second) -
            inner Real ((data.greenCore period hPeriod).core.inclusion first)
              ((data.greenCore period hPeriod).core.operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            ((data.greenCore period hPeriod).core.boundaryTrace first)
            ((data.greenCore period hPeriod).core.boundaryTrace second)) ∧
      (∀ field : SmoothDomain period hPeriod,
        CanonicalPhysicalScalarEulerEquation
            period hPeriod massSquared field ↔
          (data.greenCore period hPeriod).core.operator field = 0) :=
  ⟨data.intrinsicWave.toWaveAtlasNaturality period hPeriod,
    (data.greenCore period hPeriod).core.boundary_dense,
    (data.greenCore period hPeriod).core.green_identity,
    (data.greenCore period hPeriod).eulerEquation_iff_operator_eq_zero
      period hPeriod⟩

/-- Marker for the conditional Lorentzian boundary interface. -/
theorem lorentzianBoundaryClosure_interface_available : True :=
  trivial

/-- Compatibility name for the conditional Lorentzian boundary interface. -/
theorem lorentzianBoundaryClosure_available : True :=
  lorentzianBoundaryClosure_interface_available

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D
end JanusFormal
