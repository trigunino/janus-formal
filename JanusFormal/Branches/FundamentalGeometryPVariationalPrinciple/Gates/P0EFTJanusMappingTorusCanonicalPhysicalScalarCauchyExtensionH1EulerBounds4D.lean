import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionComponentBounds4D

/-!
# H1 and Euler estimates for the physical Cauchy extension

An explicit collar extension is most naturally estimated in the physical `H¹`
norm, while its massive Euler residual is estimated separately in bulk `L²`.
The continuous forgetting map `H¹ -> L²` turns the first estimate into the bulk
inclusion estimate.  Together with the Euler estimate, the component-bound
construction supplies the complete graph bound and completed trace
surjectivity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionH1EulerBounds4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionComponentBounds4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Physical `H¹` and Euler-residual estimates for the smooth Cauchy extension. -/
structure CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) where
  h1Constant : Real
  operatorConstant : Real
  h1Constant_nonnegative : 0 ≤ h1Constant
  operatorConstant_nonnegative : 0 ≤ operatorConstant
  h1_bound : ∀ data : ValueCore × NormalCore,
    ‖P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
        period hPeriod (geometric.extension data)‖ ≤
      h1Constant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.valueEmbedding geometric.normalEmbedding data‖
  operator_bound : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
      operatorConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.valueEmbedding geometric.normalEmbedding data‖

namespace CanonicalPhysicalScalarCauchyExtensionH1EulerBounds

/-- Bulk `L²` constant obtained by composing the `H¹` estimate with the
forgetting map. -/
def inclusionConstant
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
      period hPeriod geometric) : Real :=
  ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ * bounds.h1Constant

/-- The induced bulk constant is nonnegative. -/
theorem inclusionConstant_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
      period hPeriod geometric) :
    0 ≤ bounds.inclusionConstant :=
  mul_nonneg (norm_nonneg _) bounds.h1Constant_nonnegative

/-- The `H¹` estimate implies the bulk-inclusion component estimate. -/
theorem inclusion_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
      period hPeriod geometric)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
      bounds.inclusionConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.valueEmbedding geometric.normalEmbedding data‖ := by
  let extensionH1 :=
    P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
      period hPeriod (geometric.extension data)
  let boundaryNorm :=
    ‖canonicalScalarBoundaryCorePairEmbedding
      geometric.valueEmbedding geometric.normalEmbedding data‖
  have hBoundaryNonnegative : 0 ≤ boundaryNorm := norm_nonneg _
  have hH1 := bounds.h1_bound data
  change ‖smoothToCanonicalPhysicalBulkL2 period hPeriod
      (geometric.extension data)‖ ≤ _
  rw [← canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth]
  calc
    ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod extensionH1‖ ≤
        ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ * ‖extensionH1‖ :=
      (canonicalPhysicalScalarH1ToBulkL2 period hPeriod).le_opNorm extensionH1
    _ ≤ ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ *
        (bounds.h1Constant * boundaryNorm) :=
      mul_le_mul_of_nonneg_left hH1 (norm_nonneg _)
    _ = bounds.inclusionConstant * boundaryNorm := by
      unfold inclusionConstant
      ring

/-- Conversion to separate graph-component bounds. -/
def toComponentBounds
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (bounds : CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
      period hPeriod geometric) :
    CanonicalPhysicalScalarCauchyExtensionComponentBounds
      period hPeriod geometric where
  inclusionConstant := bounds.inclusionConstant
  operatorConstant := bounds.operatorConstant
  inclusionConstant_nonnegative := bounds.inclusionConstant_nonnegative
  operatorConstant_nonnegative := bounds.operatorConstant_nonnegative
  inclusion_bound := bounds.inclusion_bound
  operator_bound := bounds.operator_bound

/-- Direct installation of the cutoff-closed boundary data from `H¹` and Euler
extension estimates. -/
def toCutoffClosedBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (garding : geometric.greenCore.SquaredGardingEstimate period hPeriod)
    (normalRegularity : geometric.greenCore.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (bounds : CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
      period hPeriod geometric) :
    CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) :=
  (bounds.toComponentBounds geometric).toCutoffClosedBoundaryData
    geometric garding normalRegularity

/-- H1/Euler extension estimate certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (garding : geometric.greenCore.SquaredGardingEstimate period hPeriod)
    (normalRegularity : geometric.greenCore.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (bounds : CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
      period hPeriod geometric) :
    geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion geometric.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          geometric.greenCore.core
          (bounds.toCutoffClosedBoundaryData geometric garding normalRegularity)
            |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
              |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound) :=
  (bounds.toCutoffClosedBoundaryData geometric garding normalRegularity).certificate

end CanonicalPhysicalScalarCauchyExtensionH1EulerBounds

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionH1EulerBounds4D
end JanusFormal
