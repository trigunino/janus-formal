import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarSymmetricCoreClosable4D

/-!
# Concrete first-sheet physical scalar Hilbert Green system

The physical scalar Euler residual and the physical first-sheet Cauchy trace are
now concrete objects.  This file isolates the two genuinely global PDE theorems
still required to assemble them:

* every L2 boundary pair is realized by a smooth bulk scalar;
* the antisymmetric bulk L2 pairing of the Euler operator equals the exact
  oriented global Green current.

The second statement immediately becomes the abstract Hilbert Green identity,
because the oriented current was already identified with twice the first-sheet
Hilbert symplectic pairing.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarSymmetricCoreClosable4D

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

private abbrev SmoothDomain := SmoothQuotientField period hPeriod Real
private abbrev BulkL2 := CanonicalPhysicalBulkL2 period hPeriod
private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

/-- Concrete global PDE data completing the first-sheet physical Green system. -/
structure CanonicalPhysicalScalarFirstSheetGreenData
    (massSquared : Real) where
  operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
    period hPeriod massSquared
  boundary_surjective : Function.Surjective
    (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod)
  bulk_green_stokes : ∀ first second : SmoothDomain period hPeriod,
    inner Real (operatorData.toBulkL2LinearMap first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (operatorData.toBulkL2LinearMap second) =
      cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod first second

namespace CanonicalPhysicalScalarFirstSheetGreenData

/-- Paired first-sheet trace, named as the boundary trace of the Green system. -/
def boundaryTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :
    SmoothDomain period hPeriod →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum
        (Trace := BoundaryL2 period) :=
  smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod

/-- Genuine physical Hilbert Green system on the smooth scalar core. -/
def system
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :
    CanonicalScalarHilbertGreenSystem
      (Domain := SmoothDomain period hPeriod)
      (Ambient := BulkL2 period hPeriod)
      (Trace := BoundaryL2 period) where
  inclusion := smoothToCanonicalPhysicalBulkL2 period hPeriod
  operator := green.operatorData.toBulkL2LinearMap
  boundaryTrace := green.boundaryTrace
  boundary_surjective := green.boundary_surjective
  green_identity := by
    intro first second
    rw [green.bulk_green_stokes]
    exact (canonicalPhysicalScalarFirstSheetHilbertTrace_certificate
      period hPeriod first second).2

/-- The physical Euler equation is zero of the operator component. -/
theorem eulerEquation_iff_operator_eq_zero
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (field : SmoothDomain period hPeriod) :
    CanonicalPhysicalScalarEulerEquation
        period hPeriod massSquared field ↔
      green.system.operator field = 0 :=
  green.operatorData.eulerEquation_iff_operator_eq_zero field

/-- Global Green identity of the assembled system. -/
theorem green_identity
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (first second : SmoothDomain period hPeriod) :
    inner Real (green.system.operator first)
          (green.system.inclusion second) -
        inner Real (green.system.inclusion first)
          (green.system.operator second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (green.system.boundaryTrace first)
        (green.system.boundaryTrace second) :=
  green.system.green_identity first second

/-- Smooth domains selected by an arbitrary first-sheet Lagrangian boundary
condition. -/
def smoothLagrangianDomainSubmodule
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (condition :
      P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D.CanonicalScalarHilbertLagrangianBoundaryCondition
        (BoundaryL2 period)) :
    Submodule Real (SmoothDomain period hPeriod) :=
  condition.subspace.comap green.system.boundaryTrace

@[simp] theorem mem_smoothLagrangianDomainSubmodule
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (condition :
      P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D.CanonicalScalarHilbertLagrangianBoundaryCondition
        (BoundaryL2 period))
    (field : SmoothDomain period hPeriod) :
    field ∈ smoothLagrangianDomainSubmodule
        period hPeriod green condition ↔
      green.system.boundaryTrace field ∈ condition.subspace :=
  Iff.rfl

/-- Inclusion of a smooth physical Lagrangian core into bulk L2. -/
def smoothLagrangianInclusion
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (condition :
      P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D.CanonicalScalarHilbertLagrangianBoundaryCondition
        (BoundaryL2 period)) :
    smoothLagrangianDomainSubmodule period hPeriod green condition →ₗ[Real]
      BulkL2 period hPeriod :=
  green.system.inclusion.comp
    (smoothLagrangianDomainSubmodule period hPeriod green condition).subtype

/-- Euler operator restricted to a smooth physical Lagrangian core. -/
def smoothLagrangianOperator
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (condition :
      P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D.CanonicalScalarHilbertLagrangianBoundaryCondition
        (BoundaryL2 period)) :
    smoothLagrangianDomainSubmodule period hPeriod green condition →ₗ[Real]
      BulkL2 period hPeriod :=
  green.system.operator.comp
    (smoothLagrangianDomainSubmodule period hPeriod green condition).subtype

/-- Every smooth Lagrangian physical core is symmetric. -/
theorem smoothLagrangianOperator_symmetric
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (condition :
      P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D.CanonicalScalarHilbertLagrangianBoundaryCondition
        (BoundaryL2 period))
    (first second : smoothLagrangianDomainSubmodule
      period hPeriod green condition) :
    inner Real (smoothLagrangianOperator period hPeriod green condition first)
          (smoothLagrangianInclusion period hPeriod green condition second) =
      inner Real (smoothLagrangianInclusion period hPeriod green condition first)
          (smoothLagrangianOperator period hPeriod green condition second) := by
  have hBoundary := condition.pairing_eq_zero
    (green.system.boundaryTrace first.1)
    (green.system.boundaryTrace second.1)
    first.2 second.2
  have hGreen := green.system.green_identity first.1 second.1
  rw [hBoundary] at hGreen
  apply sub_eq_zero.mp
  simpa [smoothLagrangianOperator, smoothLagrangianInclusion] using hGreen

/-- Green system restricted to a chosen smooth Lagrangian core.  Its boundary
trace is zero because the isotropic condition has already been imposed; the
trace type remains the same to reuse the generic graph machinery. -/
def restrictedSymmetricSystem
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (condition :
      P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D.CanonicalScalarHilbertLagrangianBoundaryCondition
        (BoundaryL2 period)) :
    CanonicalScalarHilbertGreenSystem
      (Domain := smoothLagrangianDomainSubmodule
        period hPeriod green condition)
      (Ambient := BulkL2 period hPeriod)
      (Trace := PUnit) where
  inclusion := smoothLagrangianInclusion period hPeriod green condition
  operator := smoothLagrangianOperator period hPeriod green condition
  boundaryTrace := 0
  boundary_surjective := by
    intro boundary
    refine ⟨0, ?_⟩
    apply Prod.ext <;> exact Subsingleton.elim _ _
  green_identity := by
    intro first second
    have hSymmetric := smoothLagrangianOperator_symmetric
      period hPeriod green condition first second
    simpa using sub_eq_zero.mpr hSymmetric

/-- Density of a selected smooth Lagrangian core is now the only input needed
for its closability. -/
theorem restrictedSystem_closable_of_dense
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (condition :
      P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D.CanonicalScalarHilbertLagrangianBoundaryCondition
        (BoundaryL2 period))
    (hDense : DenseRange
      (smoothLagrangianInclusion period hPeriod green condition)) :
    CanonicalScalarGraphClosable
      (restrictedSymmetricSystem period hPeriod green condition) :=
  canonicalScalarGraphClosable_of_dense_symmetric
    (restrictedSymmetricSystem period hPeriod green condition) hDense
    (smoothLagrangianOperator_symmetric period hPeriod green condition)

/-- First-sheet physical Green-system certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :
    Function.Surjective green.system.boundaryTrace ∧
      (∀ first second : SmoothDomain period hPeriod,
        inner Real (green.system.operator first)
              (green.system.inclusion second) -
            inner Real (green.system.inclusion first)
              (green.system.operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            (green.system.boundaryTrace first)
            (green.system.boundaryTrace second)) :=
  ⟨green.system.boundary_surjective,
    green.system.green_identity⟩

end CanonicalPhysicalScalarFirstSheetGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D
end JanusFormal
