import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryTripleConstruction4D

/-!
# Elliptic construction of the physical scalar boundary triple

The concrete boundary-triple construction is restated using standard PDE inputs:

* a squared Gårding estimate for physical `H¹`;
* a higher-regularity graph estimate with a bounded normal trace;
* a smooth Cauchy jet extension with a graph bound;
* a dense interior zero-Cauchy core.

Gårding produces the graph-elliptic estimate.  Higher regularity produces the
normal graph estimate.  The existing constructive boundary theorem then
installs the dense Green core, the completed trace and the surjective completed
boundary triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticBoundaryTriple4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData.NormalRegularityData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryTripleConstruction4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarGreenCoreInteriorDensity4D

universe x y z r

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Standard elliptic inputs for the complete physical boundary triple. -/
structure CanonicalPhysicalScalarEllipticBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y) (InteriorCore : Type z)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore] where
  smooth : CanonicalPhysicalScalarSmoothCauchyExtensionData
    period hPeriod massSquared ValueCore NormalCore
  garding : (smooth.greenCoreData).SquaredGardingEstimate period hPeriod
  normalRegularity :
    (smooth.greenCoreData).NormalRegularityData
      period hPeriod (Regularity := Regularity)
  interior : CanonicalScalarGreenCoreInteriorDensityData
    (InteriorCore := InteriorCore) (smooth.greenCoreData).core
  extensionConstant : Real
  extensionConstant_nonnegative : 0 ≤ extensionConstant
  extensionGraphBound : ∀ data : ValueCore × NormalCore,
    ‖P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreToGraph
        (smooth.greenCoreData).core (smooth.extension data)‖ ≤
      extensionConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          smooth.valueEmbedding smooth.normalEmbedding data‖

namespace CanonicalPhysicalScalarEllipticBoundaryData

/-- Underlying corrected physical Green core. -/
def green
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (ellipticData : CanonicalPhysicalScalarEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :=
  ellipticData.smooth.greenCoreData

/-- Conversion to the generic constructive boundary data. -/
def toBoundaryConstructionData
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (ellipticData : CanonicalPhysicalScalarEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarBoundaryTripleConstructionData
      period hPeriod massSquared ValueCore NormalCore InteriorCore where
  smooth := ellipticData.smooth
  elliptic := ellipticData.garding.toSquaredGraphEllipticEstimate
    period hPeriod ellipticData.green
  normal := ellipticData.normalRegularity.toSquaredNormalGraphEstimate
    period hPeriod ellipticData.green
  interior := ellipticData.interior
  extensionConstant := ellipticData.extensionConstant
  extensionConstant_nonnegative := ellipticData.extensionConstant_nonnegative
  extensionGraphBound := ellipticData.extensionGraphBound

/-- Corrected completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (ellipticData : CanonicalPhysicalScalarEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :=
  (ellipticData.toBoundaryConstructionData period hPeriod).triple
    period hPeriod

/-- Complete physical boundary inputs. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (ellipticData : CanonicalPhysicalScalarEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :=
  (ellipticData.toBoundaryConstructionData period hPeriod).completedInputs
    period hPeriod

/-- Completed normal trace through the supplied regularity space. -/
def completedNormalTraceFromRegularity
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (ellipticData : CanonicalPhysicalScalarEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :=
  fun field => ellipticData.normalRegularity.normalTrace
    (ellipticData.normalRegularity.completedRegularity
      period hPeriod ellipticData.green field)

/-- Elliptic boundary-triple certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y} {InteriorCore : Type z}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [AddCommGroup InteriorCore] [Module Real InteriorCore]
    (ellipticData : CanonicalPhysicalScalarEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore InteriorCore
      (Regularity := Regularity)) :
    Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          ellipticData.green.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          ellipticData.green.core
          (ellipticData.toBoundaryConstructionData
            period hPeriod).traceBound) ∧
      (∀ field,
        ellipticData.completedNormalTraceFromRegularity period hPeriod field =
          completedBoundaryNormalTrace period hPeriod ellipticData.green
            (ellipticData.toBoundaryConstructionData
              period hPeriod).traceBound field) :=
  ⟨(ellipticData.triple period hPeriod).inclusion_injective,
    (ellipticData.toBoundaryConstructionData
      period hPeriod).completedTraceSurjective,
    ellipticData.normalRegularity
      |>.normalTrace_completedRegularity_eq_completedBoundaryNormalTrace
        period hPeriod ellipticData.green
        (ellipticData.toBoundaryConstructionData period hPeriod).traceBound⟩

end CanonicalPhysicalScalarEllipticBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEllipticBoundaryTriple4D
end JanusFormal
