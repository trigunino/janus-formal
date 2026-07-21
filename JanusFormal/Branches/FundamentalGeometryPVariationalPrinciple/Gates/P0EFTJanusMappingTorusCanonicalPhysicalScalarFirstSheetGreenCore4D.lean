import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGraphTraceBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D

/-!
# Correct dense physical scalar Green core

The smooth Euler core has a dense, rather than surjective, trace range in the
first-sheet boundary L2 space.  The graph trace is completed using coarea,
ellipticity and normal-control estimates.  Density of the zero-Cauchy minimal
core makes the completed graph single-valued.  Surjectivity is requested only
for the completed trace, exactly where a Sobolev boundary extension theorem
belongs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGraphTraceBound4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

private abbrev SmoothDomain := SmoothQuotientField period hPeriod Real
private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Concrete dense physical Green-core data. -/
structure CanonicalPhysicalScalarFirstSheetGreenCoreData
    (massSquared : Real) where
  operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
    period hPeriod massSquared
  boundary_dense : DenseRange
    (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod)
  bulk_green_stokes : ∀ first second : SmoothDomain period hPeriod,
    inner Real (operatorData.toBulkL2LinearMap first)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod second) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod first)
          (operatorData.toBulkL2LinearMap second) =
      cutBulkGlobalOrientedScalarCurrentIntegral period hPeriod first second

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- Correct physical smooth Green core. -/
def core
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) :
    CanonicalScalarHilbertGreenCore
      (Domain := SmoothDomain period hPeriod)
      (Ambient := CanonicalPhysicalBulkL2 period hPeriod)
      (Trace := BoundaryL2 period) where
  inclusion := smoothToCanonicalPhysicalBulkL2 period hPeriod
  operator := green.operatorData.toBulkL2LinearMap
  boundaryTrace := smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
    period hPeriod
  boundary_dense := green.boundary_dense
  green_identity := by
    intro first second
    rw [green.bulk_green_stokes]
    exact (canonicalPhysicalScalarFirstSheetHilbertTrace_certificate
      period hPeriod first second).2

/-- Physical Euler equation is zero of the core operator. -/
theorem eulerEquation_iff_operator_eq_zero
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (field : SmoothDomain period hPeriod) :
    CanonicalPhysicalScalarEulerEquation period hPeriod massSquared field ↔
      green.core.operator field = 0 :=
  green.operatorData.eulerEquation_iff_operator_eq_zero field

/-- Physical graph-elliptic estimate. -/
structure GraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : SmoothDomain period hPeriod,
    ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ≤
      constant * ‖canonicalScalarGreenCoreToGraph green.core field‖

/-- Physical normal-trace graph estimate. -/
structure NormalGraphEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : SmoothDomain period hPeriod,
    ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2
        period hPeriod field‖ ≤
      constant * ‖canonicalScalarGreenCoreToGraph green.core field‖

/-- First-sheet value trace in the corrected Euler graph norm. -/
theorem valueTrace_norm_le_graph
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : green.GraphEllipticEstimate period hPeriod)
    (field : SmoothDomain period hPeriod) :
    ‖smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field‖ ≤
      (canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
        elliptic.constant) *
      ‖canonicalScalarGreenCoreToGraph green.core field‖ := by
  have hTrace := canonicalPhysicalScalarH1TraceOfCoarea_norm_le
    period hPeriod coarea
    (smoothToCanonicalPhysicalScalarH1 period hPeriod field)
  rw [canonicalPhysicalScalarH1TraceOfCoarea_agrees_on_smooth] at hTrace
  rw [smoothCanonicalPhysicalScalarFirstSheetValueL2_norm_eq_throatTrace]
  calc
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ≤
        canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
          ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ := hTrace
    _ ≤ canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
        (elliptic.constant *
          ‖canonicalScalarGreenCoreToGraph green.core field‖) :=
      mul_le_mul_of_nonneg_left (elliptic.bound field)
        (by
          unfold canonicalPhysicalScalarH1TraceCoareaConstant
          exact mul_nonneg
            (canonicalNormalFrameReconstructionBound period hPeriod).nonnegative
            (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Combined corrected-core paired trace constant. -/
def pairedTraceConstant
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : green.GraphEllipticEstimate period hPeriod)
    (normal : green.NormalGraphEstimate period hPeriod) : Real :=
  max
    (canonicalPhysicalScalarH1TraceCoareaConstant period hPeriod coarea *
      elliptic.constant)
    normal.constant

/-- Combined corrected-core paired trace estimate. -/
theorem boundaryTrace_norm_le_graph
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : green.GraphEllipticEstimate period hPeriod)
    (normal : green.NormalGraphEstimate period hPeriod)
    (field : SmoothDomain period hPeriod) :
    ‖green.core.boundaryTrace field‖ ≤
      green.pairedTraceConstant period hPeriod coarea elliptic normal *
        ‖canonicalScalarGreenCoreToGraph green.core field‖ := by
  change max
      ‖smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field‖
      ‖smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field‖ ≤ _
  apply max_le
  · exact (green.valueTrace_norm_le_graph
      period hPeriod coarea elliptic field).trans
      (mul_le_mul_of_nonneg_right
        (le_max_left _ normal.constant) (norm_nonneg _))
  · exact (normal.bound field).trans
      (mul_le_mul_of_nonneg_right
        (le_max_right _ normal.constant) (norm_nonneg _))

/-- Corrected-core graph-bound package. -/
def boundaryGraphBound
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    (elliptic : green.GraphEllipticEstimate period hPeriod)
    (normal : green.NormalGraphEstimate period hPeriod) :
    HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound green.core where
  constant := green.pairedTraceConstant period hPeriod coarea elliptic normal
  nonnegative := le_trans normal.nonnegative (le_max_right _ _)
  bound := green.boundaryTrace_norm_le_graph
    period hPeriod coarea elliptic normal

/-- Density of smooth zero-Cauchy fields in the physical bulk. -/
def MinimalCoreDense
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) : Prop :=
  green.core.MinimalCoreDense

/-- Surjectivity theorem for the completed physical Cauchy trace. -/
def CompletedBoundaryTraceSurjective
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
      green.core) : Prop :=
  Function.Surjective
    (canonicalScalarGreenCoreCompletedBoundaryTrace green.core traceBound)

/-- Exact completed physical boundary-triple inputs. -/
structure CompletedBoundaryTripleInputs
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod
  elliptic : green.GraphEllipticEstimate period hPeriod
  normal : green.NormalGraphEstimate period hPeriod
  minimalDense : green.MinimalCoreDense period hPeriod
  completedTraceSurjective : green.CompletedBoundaryTraceSurjective
    period hPeriod
    (green.boundaryGraphBound period hPeriod coarea elliptic normal)

namespace CompletedBoundaryTripleInputs

/-- Corrected physical graph bound. -/
def traceBound
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  green.boundaryGraphBound period hPeriod
    inputs.coarea inputs.elliptic inputs.normal

/-- Correct completed physical boundary triple. -/
def triple
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    CanonicalScalarCompletedBoundaryTripleData
      green.core (inputs.traceBound green) where
  boundary_surjective := inputs.completedTraceSurjective
  inclusion_injective :=
    green.core.graphInclusion_injective_of_minimal_dense inputs.minimalDense

/-- Completed maximal physical domain. -/
abbrev MaximalDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :=
  CanonicalScalarGreenCoreGraphSpace green.core

/-- Completed physical Cauchy trace. -/
def boundaryTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    inputs.MaximalDomain green →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := BoundaryL2 period) :=
  canonicalScalarGreenCoreCompletedBoundaryTrace
    green.core (inputs.traceBound green)

/-- Exact completed physical Green identity. -/
theorem greenIdentity
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod)
    (first second : inputs.MaximalDomain green) :
    inner Real (canonicalScalarGreenCoreGraphOperator green.core first)
          (canonicalScalarGreenCoreGraphInclusion green.core second) -
        inner Real (canonicalScalarGreenCoreGraphInclusion green.core first)
          (canonicalScalarGreenCoreGraphOperator green.core second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (inputs.boundaryTrace green first)
        (inputs.boundaryTrace green second) :=
  canonicalScalarGreenCoreCompletedGreenIdentity
    green.core (inputs.traceBound green) first second

/-- Correct physical boundary-triple certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : green.CompletedBoundaryTripleInputs period hPeriod) :
    DenseRange (canonicalScalarGreenCoreToGraph green.core) ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion green.core) ∧
      Function.Surjective (inputs.boundaryTrace green) ∧
      (∀ first second : inputs.MaximalDomain green,
        inner Real (canonicalScalarGreenCoreGraphOperator green.core first)
              (canonicalScalarGreenCoreGraphInclusion green.core second) -
            inner Real (canonicalScalarGreenCoreGraphInclusion green.core first)
              (canonicalScalarGreenCoreGraphOperator green.core second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            (inputs.boundaryTrace green first)
            (inputs.boundaryTrace green second)) :=
  ⟨canonicalScalarGreenCoreToGraph_denseRange green.core,
    (inputs.triple green).inclusion_injective,
    inputs.completedTraceSurjective,
    inputs.greenIdentity green⟩

end CompletedBoundaryTripleInputs

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
end JanusFormal
