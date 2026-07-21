import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMeasureToSphereCoarea4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D

/-!
# Physical first-sheet Cauchy completion after spherical coarea

The latitude coarea theorem is now proved, so this file removes it from the
actual trace-completion frontier.  The remaining inputs are the Euler graph
elliptic estimate, the normal graph estimate, minimal-core density and a bounded
right inverse of the completed Cauchy trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetPostCoareaTrace4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalLatitudeMeasureToSphereCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The proved latitude coarea theorem in the spelling consumed by the corrected
Green core. -/
def provedLatitudeCoarea :
    CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod :=
  canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod

/-- Exact remaining inputs for completed first-sheet Cauchy data. -/
structure CanonicalPhysicalScalarFirstSheetPostCoareaTraceData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  elliptic : green.GraphEllipticEstimate period hPeriod
  normal : green.NormalGraphEstimate period hPeriod
  minimalDense : green.MinimalCoreDense period hPeriod
  completedExtension : CanonicalPhysicalScalarCompletedCauchyExtensionData
    period hPeriod green
      (green.boundaryGraphBound period hPeriod
        (provedLatitudeCoarea period hPeriod) elliptic normal)

namespace CanonicalPhysicalScalarFirstSheetPostCoareaTraceData

/-- Unconditional paired graph bound. -/
def boundaryGraphBound
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (data : CanonicalPhysicalScalarFirstSheetPostCoareaTraceData
      period hPeriod green) :
    HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound green.core :=
  green.boundaryGraphBound period hPeriod
    (provedLatitudeCoarea period hPeriod) data.elliptic data.normal

/-- Completed physical boundary-triple inputs with coarea filled by theorem. -/
def toCompletedBoundaryTripleInputs
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (data : CanonicalPhysicalScalarFirstSheetPostCoareaTraceData
      period hPeriod green) :
    green.CompletedBoundaryTripleInputs period hPeriod :=
  CanonicalPhysicalScalarCompletedCauchyExtensionData.completedBoundaryTripleInputs
    period hPeriod green
    (provedLatitudeCoarea period hPeriod)
    data.elliptic data.normal data.minimalDense data.completedExtension

/-- The completed Cauchy trace is surjective from the genuinely remaining
post-coarea data. -/
theorem completedBoundaryTrace_surjective
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (data : CanonicalPhysicalScalarFirstSheetPostCoareaTraceData
      period hPeriod green) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace green.core
        (data.boundaryGraphBound period hPeriod)) :=
  data.completedExtension.boundaryTrace_surjective green

/-- Post-coarea trace-completion certificate. -/
theorem certificate
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (data : CanonicalPhysicalScalarFirstSheetPostCoareaTraceData
      period hPeriod green) :
    green.MinimalCoreDense period hPeriod ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace green.core
          (data.boundaryGraphBound period hPeriod)) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖green.core.boundaryTrace field‖ ≤
          (data.boundaryGraphBound period hPeriod).constant *
            ‖canonicalScalarGreenCoreToGraph green.core field‖) :=
  ⟨data.minimalDense,
    data.completedBoundaryTrace_surjective period hPeriod,
    (data.boundaryGraphBound period hPeriod).bound⟩

end CanonicalPhysicalScalarFirstSheetPostCoareaTraceData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetPostCoareaTrace4D
end JanusFormal
