import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetStrongAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D

/-!
# Reduced analytic frontier after closing spherical coarea

The spherical coarea theorem and the physical value trace are theorems.  The
corrected completed-boundary architecture also derives closability, density of
all Lagrangian domains, completed trace surjectivity, shifted-operator
surjectivity, semiboundedness and compact resolvent from more concrete inputs.

The historical coarse interface below remains for compatibility.  It asks for a
graph-elliptic estimate, normal graph estimate, minimal-core density, completed
trace surjectivity and a strong analytic closure package.

The preferred fully reduced interface is
`FullyReducedAnalyticFrontier`.  Its actual mathematical fields are:

* covariant wave naturality across the total atlas;
* continuity of the global Euler residual;
* the global Euler-skew/divergence integral identity;
* dense smooth value and normal boundary cores;
* a smooth Cauchy jet extension and its graph estimate;
* continuous-to-smooth approximation in physical bulk `L²`;
* shrinking zero-Cauchy collar cutoffs;
* a squared Gårding estimate;
* higher regularity with a bounded normal trace;
* smooth graph approximation of Hilbert adjoint pairs;
* coercivity of one canonical shifted form;
* compact approximations converging to the physical `H¹ -> L²` inclusion.

From these inputs the code constructs the dense physical Green core, the
surjective completed boundary triple, actual Hilbert self-adjointness, a compact
reference resolvent, the Fredholm alternative, spectral completeness and the
lower spectral bound.
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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Coarea is a theorem and therefore does not occur as a field in any reduced
input package. -/
theorem coarea_closed :
    P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.CanonicalPhysicalScalarLatitudeCoareaTheorem
      period hPeriod :=
  canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod

/-- Historical coarse inputs still accepted by the compatibility route. -/
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

/-- Paired Cauchy trace graph bound from the coarse estimates. -/
def traceBound
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :
    HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound green.core :=
  green.boundaryGraphBound period hPeriod
    (coarea_closed period hPeriod) inputs.elliptic inputs.normal

/-- Conversion to the completed-boundary input package. -/
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

/-- Corrected completed boundary triple. -/
def triple
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :=
  (inputs.toCompletedBoundaryTripleInputs green).triple green

/-- Corresponding strong compatibility presentation. -/
def strongSystem
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :=
  (inputs.toCompletedBoundaryTripleInputs green).strongSystem green

/-- Closability is derived from minimal-core density after completion. -/
theorem strongSystem_closable
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :
    CanonicalScalarGraphClosable (inputs.strongSystem green) := by
  simpa [strongSystem] using
    (inputs.toCompletedBoundaryTripleInputs green).strongSystem_closable green

end CoareaClosedCompletedBoundaryInputs

/-- Historical strong analytic package. -/
abbrev RemainingStrongAnalyticData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (inputs : CoareaClosedCompletedBoundaryInputs
      period hPeriod green) :=
  CanonicalPhysicalScalarFirstSheetStrongAnalyticData
    period hPeriod green (inputs.toCompletedBoundaryTripleInputs green)

/-- Historical coarse frontier retained for downstream compatibility. -/
structure ReducedAnalyticFrontier (massSquared : Real) where
  green : CanonicalPhysicalScalarFirstSheetGreenCoreData
    period hPeriod massSquared
  boundary : CoareaClosedCompletedBoundaryInputs
    period hPeriod green
  spectral : RemainingStrongAnalyticData
    period hPeriod green boundary

/-- Preferred current frontier.  It contains only concrete geometric,
approximation, elliptic, adjoint, coercivity and compactness data. -/
abbrev FullyReducedAnalyticFrontier
    (massSquared : Real)
    (ValueCore : Type*) (NormalCore : Type*)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (Regularity : Type*)
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity] :=
  CanonicalPhysicalScalarFullyReducedAnalyticData
    period hPeriod massSquared ValueCore NormalCore
    (Regularity := Regularity)

/-- Every fully reduced frontier produces actual Hilbert self-adjointness. -/
theorem fullyReduced_actualAdjointDomain_eq
    {ValueCore NormalCore Regularity : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : FullyReducedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity) :
    frontier.boundary.triple.actualAdjointDomain frontier.condition =
      frontier.boundary.triple.realizationDomain frontier.condition :=
  frontier.actualAdjointDomain_eq period hPeriod

/-- Every fully reduced frontier produces the direct Fredholm alternative. -/
theorem fullyReduced_fredholmAlternative
    {ValueCore NormalCore Regularity : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : FullyReducedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ frontier.referenceParameter) :
    frontier.boundary.triple.LagrangianHasEigenvalue
        frontier.condition spectralParameter ∨
      frontier.boundary.triple.LagrangianResolventPoint
        frontier.condition spectralParameter :=
  frontier.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Frontier-reduction certificate. -/
theorem fullyReduced_certificate
    {ValueCore NormalCore Regularity : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : FullyReducedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
          period hPeriod) ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      frontier.boundary.triple.actualAdjointDomain frontier.condition =
        frontier.boundary.triple.realizationDomain frontier.condition :=
  ⟨frontier.boundary.smoothing.smoothToCanonicalPhysicalBulkL2_denseRange,
    frontier.rellichApproximation.rellich,
    frontier.actualAdjointDomain_eq period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarReducedAnalyticFrontier4D
end JanusFormal
