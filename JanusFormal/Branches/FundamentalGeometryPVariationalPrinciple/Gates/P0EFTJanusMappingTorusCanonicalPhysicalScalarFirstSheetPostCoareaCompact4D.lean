import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetPostCoareaTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCoerciveCompactClosure4D

/-!
# Compact physical scalar closure after spherical coarea

Coarea and completed-trace surjectivity are separated from the final operator
analysis.  Once the post-coarea trace data are supplied, the genuinely remaining
compact-closure inputs for one Lagrangian boundary condition are:

* maximal-adjoint regularity;
* one coercive reference problem with compact domain embedding;
* a lower quadratic-form bound.

Density of the realized operator domain is a theorem from minimal-core density,
not an additional hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetPostCoareaCompact4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetPostCoareaTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetCoerciveCompactClosure4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Final physical compact-closure data after the coarea and trace-completion
frontiers have been removed. -/
structure CanonicalPhysicalScalarFirstSheetPostCoareaCompactData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  trace : CanonicalPhysicalScalarFirstSheetPostCoareaTraceData
    period hPeriod green
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjoint : CanonicalPhysicalScalarStrongAdjointCharacterization
    period hPeriod green (trace.toCompletedBoundaryTripleInputs period hPeriod)
      condition
  referenceParameter : Real
  coerciveCompact : CanonicalScalarClosedLagrangianCoerciveCompactEmbeddingAt
    ((trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green)
    ((trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem_closable green)
    ((trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystemGraphBound green)
    condition referenceParameter
  semibounded : CanonicalScalarClosedLagrangianSemiboundedData
    ((trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green)
    ((trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem_closable green)
    ((trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystemGraphBound green)
    condition

namespace CanonicalPhysicalScalarFirstSheetPostCoareaCompactData

/-- Conversion to the previously proved coercive/compact closure package. -/
noncomputable def toCoerciveCompactData
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (data : CanonicalPhysicalScalarFirstSheetPostCoareaCompactData
      period hPeriod green) :
    CanonicalPhysicalScalarFirstSheetCoerciveCompactData
      period hPeriod green
        (data.trace.toCompletedBoundaryTripleInputs period hPeriod) where
  condition := data.condition
  adjoint := data.adjoint
  referenceParameter := data.referenceParameter
  coerciveCompact := data.coerciveCompact
  semibounded := data.semibounded

/-- Realization-domain density follows automatically from the post-coarea trace
data. -/
theorem denseDomain
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (data : CanonicalPhysicalScalarFirstSheetPostCoareaCompactData
      period hPeriod green) :
    DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green)
        ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem_closable green)
        ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystemGraphBound green)
        data.condition) :=
  (data.toCoerciveCompactData period hPeriod).denseDomain period hPeriod

/-- Actual-adjoint equality and the Fredholm alternative from the genuinely
remaining post-coarea inputs. -/
theorem certificate
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (data : CanonicalPhysicalScalarFirstSheetPostCoareaCompactData
      period hPeriod green) :
    DenseRange
        (canonicalScalarClosedLagrangianDomainInclusion
          ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green)
          ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem_closable green)
          ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystemGraphBound green)
          data.condition) ∧
      data.adjoint.adjointDomain =
        (canonicalScalarClosedLagrangianDomainSubmodule
          ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green)
          ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem_closable green)
          ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystemGraphBound green)
          data.condition :
            Set (canonicalScalarClosedOperatorDomain
              ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green))) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green)
              ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem_closable green)
              ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystemGraphBound green)
              data.condition spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem green)
              ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystem_closable green)
              ((data.trace.toCompletedBoundaryTripleInputs period hPeriod).strongSystemGraphBound green)
              data.condition spectralParameter) :=
  (data.toCoerciveCompactData period hPeriod).certificate period hPeriod

end CanonicalPhysicalScalarFirstSheetPostCoareaCompactData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetPostCoareaCompact4D
end JanusFormal
