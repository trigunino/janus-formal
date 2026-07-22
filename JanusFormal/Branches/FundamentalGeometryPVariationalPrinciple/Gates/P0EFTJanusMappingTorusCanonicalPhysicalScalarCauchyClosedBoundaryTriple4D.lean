import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D

/-!
# Physical scalar boundary triple with the Cauchy extension closed

Smooth bulk density and shrinking zero-Cauchy cutoffs are already theorems.  The
present layer also removes the abstract smooth Cauchy extension and its opaque
graph estimate.

The smooth extension is the explicit deck-compatible latitude jet.  Its global
smoothness comes from regular tubular inverse coordinates and the canonical
polar zero region.  Separate estimates for the bulk `L²` component and the
Euler-residual component combine into the graph bound required for completed
trace surjectivity.

The remaining boundary inputs are now:

* wave globalization and the Euler-skew/divergence integral identity;
* smooth dense periodic/antiperiodic boundary cores;
* regular non-polar tubular inverse coordinates;
* componentwise estimates for the explicit Cauchy extension;
* Gårding and higher normal regularity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedBoundaryTriple4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Boundary-triple inputs after the explicit Cauchy extension and its graph
bound have been installed. -/
structure CanonicalPhysicalScalarCauchyClosedBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  cauchy : CanonicalPhysicalScalarCauchyJetGeometricData
    period hPeriod massSquared ValueCore NormalCore
  garding : cauchy.greenCore.SquaredGardingEstimate period hPeriod
  normalRegularity : cauchy.greenCore.NormalRegularityData
    period hPeriod (Regularity := Regularity)
  extensionEstimate : cauchy.CauchyJetComponentGraphEstimateData
    period hPeriod

namespace CanonicalPhysicalScalarCauchyClosedBoundaryData

/-- Conversion to the cutoff-closed boundary package. -/
def toCutoffClosedBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  geometric := boundaryData.cauchy.toGeometricGreenCoreData
  garding := boundaryData.garding
  normalRegularity := boundaryData.normalRegularity
  extensionConstant := boundaryData.extensionEstimate.graphConstant
  extensionConstant_nonnegative :=
    boundaryData.extensionEstimate.graphConstant_nonnegative
  extensionGraphBound := boundaryData.extensionEstimate.graph_bound

/-- Correct completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  boundaryData.toCutoffClosedBoundaryData.triple

/-- Completed physical boundary inputs. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  boundaryData.toCutoffClosedBoundaryData.completedInputs

/-- Bounded right inverse of the completed paired trace. -/
def completedCauchyExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  boundaryData.extensionEstimate.toBoundedSmoothCauchyExtensionData
    |>.completedExtension

/-- The completed Cauchy extension is a right inverse. -/
theorem completedCauchyExtension_rightInverse
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (boundary :
      P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.CanonicalScalarHilbertBoundaryDatum
        (Trace :=
          P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.CanonicalPhysicalScalarFirstSheetL2
            period)) :
    P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
        boundaryData.cauchy.greenCore.core
        boundaryData.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
          |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
          |>.toBoundaryConstructionData.traceBound
        (boundaryData.completedCauchyExtension boundary) =
      boundary :=
  boundaryData.extensionEstimate.toBoundedSmoothCauchyExtensionData
    |>.completedBoundaryTrace_extension
      (boundaryData.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
        |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
        |>.toBoundaryConstructionData.traceBound)
      boundary

/-- Cauchy-closed boundary-triple certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      boundaryData.cauchy.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          boundaryData.cauchy.greenCore.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          boundaryData.cauchy.greenCore.core
          boundaryData.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
            |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
            |>.toBoundaryConstructionData.traceBound) :=
  ⟨boundaryData.cauchy.boundaryTrace_denseRange,
    P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D.canonicalPhysicalScalarMinimalCoreDense
      period hPeriod boundaryData.cauchy.greenCore,
    boundaryData.triple.inclusion_injective,
    boundaryData.extensionEstimate.completedBoundaryTrace_surjective
      (boundaryData.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
        |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
        |>.toBoundaryConstructionData.traceBound)⟩

end CanonicalPhysicalScalarCauchyClosedBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedBoundaryTriple4D
end JanusFormal
