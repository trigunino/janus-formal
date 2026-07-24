import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticBoundaryTriple4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffInteriorBridge4D

/-!
# Physical scalar boundary triple from shrinking zero-Cauchy cutoffs

The dense interior-core input of the elliptic boundary construction is replaced
here by the standard geometric cutoff argument.  Smooth fields are dense in
bulk `L²`, and shrinking collar cutoffs have zero Cauchy trace and converge to
the original smooth fields.  This proves minimal-core density and supplies the
interior input automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffEllipticBoundaryTriple4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticBoundaryTriple4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore
open P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D
open P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffInteriorBridge4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Elliptic boundary data using shrinking collar cutoffs instead of an abstract
interior core. -/
structure CanonicalPhysicalScalarCutoffEllipticBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  smooth : CanonicalPhysicalScalarSmoothCauchyExtensionData
    period hPeriod massSquared ValueCore NormalCore
  garding : (smooth.greenCoreData).SquaredGardingEstimate period hPeriod
  normalRegularity :
    (smooth.greenCoreData).NormalRegularityData
      period hPeriod (Regularity := Regularity)
  cutoff : CanonicalScalarGreenCoreMinimalCutoffData
    (smooth.greenCoreData).core
  extensionConstant : Real
  extensionConstant_nonnegative : 0 ≤ extensionConstant
  extensionGraphBound : ∀ data : ValueCore × NormalCore,
    ‖P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreToGraph
        (smooth.greenCoreData).core (smooth.extension data)‖ ≤
      extensionConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          smooth.valueEmbedding smooth.normalEmbedding data‖

namespace CanonicalPhysicalScalarCutoffEllipticBoundaryData

/-- Underlying physical Green core. -/
def green
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (cutoffData : CanonicalPhysicalScalarCutoffEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  cutoffData.smooth.greenCoreData

/-- Conversion to the elliptic boundary package. -/
def toEllipticBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (cutoffData : CanonicalPhysicalScalarCutoffEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (minimalDomainSubmodule cutoffData.green.core)
      (Regularity := Regularity) where
  smooth := cutoffData.smooth
  garding := cutoffData.garding
  normalRegularity := cutoffData.normalRegularity
  interior := cutoffData.cutoff.toInteriorDensityData
  extensionConstant := cutoffData.extensionConstant
  extensionConstant_nonnegative := cutoffData.extensionConstant_nonnegative
  extensionGraphBound := cutoffData.extensionGraphBound

/-- Correct completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (cutoffData : CanonicalPhysicalScalarCutoffEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  cutoffData.toEllipticBoundaryData.triple

/-- Complete boundary input package. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (cutoffData : CanonicalPhysicalScalarCutoffEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  cutoffData.toEllipticBoundaryData.completedInputs

/-- Cutoff elliptic boundary certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (cutoffData : CanonicalPhysicalScalarCutoffEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    cutoffData.green.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          cutoffData.green.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          cutoffData.green.core
          cutoffData.toEllipticBoundaryData.toBoundaryConstructionData.traceBound) :=
  ⟨cutoffData.cutoff.minimalCoreDense,
    cutoffData.triple.inclusion_injective,
    cutoffData.toEllipticBoundaryData.toBoundaryConstructionData
      |>.completedTraceSurjective⟩

end CanonicalPhysicalScalarCutoffEllipticBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffEllipticBoundaryTriple4D
end JanusFormal
