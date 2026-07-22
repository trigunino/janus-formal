import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D

/-!
# Reduced analytic frontier after closing spherical coarea

The spherical coarea theorem and the physical value trace are no longer
hypotheses.  This file records the remaining dependency graph in the corrected
first-sheet construction.

For a concrete smooth Green core, completion of the paired Cauchy trace now
requires exactly four PDE/completion inputs:

1. a graph-elliptic estimate controlling the physical `H¹` norm;
2. a graph estimate for the normal trace;
3. density of the smooth zero-Cauchy minimal core;
4. surjectivity of the completed Cauchy trace.

The first two produce the graph-boundary estimate.  The latter two make the
completed boundary triple genuine.  Closability of the resulting strong system
is then derived, not assumed.

After this completion, the genuinely spectral inputs are exactly those already
isolated by `CanonicalPhysicalScalarFirstSheetStrongAnalyticData`: density of
the selected closed boundary domain, characterization of the true Hilbert
adjoint, one compact resolvent point, and a lower quadratic-form bound.  The
boundary condition and reference parameter are choices, not missing theorems.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarReducedAnalyticFrontier4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Coarea is a theorem and therefore does not occur as a field in any reduced
input package. -/
theorem coarea_closed :
    P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.CanonicalPhysicalScalarLatitudeCoareaTheorem
      period hPeriod :=
  canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod

/-- Exact inputs still needed to pass from a concrete smooth Green core to a
completed, surjective boundary triple. -/
structure CoareaClosedCompletedBoundaryInputs
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  elliptic : green.GraphEllipticEstimate period hPeriod
  normal : green.NormalGraphEstimate period hPeriod
  minimalDense : green.MinimalCoreDense period hPeriod
  completedTraceSurjective : green.CompletedBoundaryTraceSurjective
    period hPeriod
    (green.boundaryGraphBound period hPeriod
      (coarea_closed period hPeriod) elliptic normal)

namespace CoareaClosedCompletedBoundaryInputs

/-- The paired Cauchy trace graph bound obtained from the two remaining
quantitative PDE estimates. -/
def traceBound
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :
    HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound green.core :=
  green.boundaryGraphBound period hPeriod
    (coarea_closed period hPeriod) inputs.elliptic inputs.normal

/-- Conversion to the legacy completed-boundary input package.  The former
coarea field is filled by the theorem proved in the preceding gates. -/
def toCompletedBoundaryTripleInputs
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :
    green.CompletedBoundaryTripleInputs period hPeriod where
  coarea := coarea_closed period hPeriod
  elliptic := inputs.elliptic
  normal := inputs.normal
  minimalDense := inputs.minimalDense
  completedTraceSurjective := inputs.completedTraceSurjective

/-- The corrected completed boundary triple. -/
def triple
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :=
  (inputs.toCompletedBoundaryTripleInputs green).triple green

/-- The corresponding strong physical Green system. -/
def strongSystem
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :=
  (inputs.toCompletedBoundaryTripleInputs green).strongSystem green

/-- Closability follows from minimal-core density after completion; it is not an
additional analytic input. -/
theorem strongSystem_closable
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :
    CanonicalScalarGraphClosable (inputs.strongSystem green) := by
  simpa [strongSystem] using
    (inputs.toCompletedBoundaryTripleInputs green).strongSystem_closable green

end CoareaClosedCompletedBoundaryInputs

/-- The spectral/adjoint data that remain after the boundary triple has been
completed.  Its theorem fields are density of the selected domain, the actual
Hilbert-adjoint characterization, compact resolvent, and semiboundedness. -/
abbrev RemainingStrongAnalyticData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :=
  CanonicalPhysicalScalarFirstSheetStrongAnalyticData
    period hPeriod green (inputs.toCompletedBoundaryTripleInputs green)

/-- Complete reduced frontier after spherical coarea.

The `green` field contains the concrete operator atlas, dense smooth boundary
range, and the bulk Green--Stokes identity.  `boundary` contains the four
completion inputs displayed above.  `spectral` contains the four final
closed-operator/spectral theorems. -/
structure ReducedAnalyticFrontier (massSquared : Real) where
  green : CanonicalPhysicalScalarFirstSheetGreenCoreData
    period hPeriod massSquared
  boundary : CoareaClosedCompletedBoundaryInputs
    period hPeriod green
  spectral : RemainingStrongAnalyticData
    period hPeriod green boundary


end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarReducedAnalyticFrontier4D
end JanusFormal
