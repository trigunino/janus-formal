import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D

/-!
# Component estimates for the physical Cauchy extension

The maximal graph norm is the product sup norm of the bulk inclusion and Euler
operator coordinates.  Consequently a graph estimate for a smooth Cauchy
extension follows from two separate estimates:

* an `L²` estimate for the extension itself;
* an `L²` estimate for its Euler residual.

This is the form naturally produced by an explicit collar calculation.  The two
constants combine by `max`, and the result supplies the graph-bounded extension
field of the cutoff-closed boundary-triple package.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionComponentBounds4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Separate bulk and Euler estimates for the explicit smooth Cauchy extension. -/
structure CanonicalPhysicalScalarCauchyExtensionComponentBounds
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) where
  inclusionConstant : Real
  operatorConstant : Real
  inclusionConstant_nonnegative : 0 ≤ inclusionConstant
  operatorConstant_nonnegative : 0 ≤ operatorConstant
  inclusion_bound : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
      inclusionConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.valueEmbedding geometric.normalEmbedding data‖
  operator_bound : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
      operatorConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.valueEmbedding geometric.normalEmbedding data‖

namespace CanonicalPhysicalScalarCauchyExtensionComponentBounds

/-- Common graph constant obtained from the two component constants. -/
def graphConstant
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCauchyExtensionComponentBounds
      period hPeriod geometric) : Real :=
  max bounds.inclusionConstant bounds.operatorConstant

/-- The combined graph constant is nonnegative. -/
theorem graphConstant_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCauchyExtensionComponentBounds
      period hPeriod geometric) :
    0 ≤ bounds.graphConstant :=
  bounds.inclusionConstant_nonnegative.trans
    (le_max_left _ _)

/-- The two component estimates imply the required graph-norm estimate. -/
theorem graph_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCauchyExtensionComponentBounds
      period hPeriod geometric)
    (data : ValueCore × NormalCore) :
    ‖canonicalScalarGreenCoreToGraph geometric.greenCore.core
        (geometric.extension data)‖ ≤
      bounds.graphConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.valueEmbedding geometric.normalEmbedding data‖ := by
  let boundaryNorm :=
    ‖canonicalScalarBoundaryCorePairEmbedding
      geometric.valueEmbedding geometric.normalEmbedding data‖
  have hBoundaryNonnegative : 0 ≤ boundaryNorm := norm_nonneg _
  have hInclusion :
      ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
        bounds.graphConstant * boundaryNorm := by
    calc
      ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
          bounds.inclusionConstant * boundaryNorm :=
        bounds.inclusion_bound data
      _ ≤ bounds.graphConstant * boundaryNorm :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hBoundaryNonnegative
  have hOperator :
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
        bounds.graphConstant * boundaryNorm := by
    calc
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
          bounds.operatorConstant * boundaryNorm :=
        bounds.operator_bound data
      _ ≤ bounds.graphConstant * boundaryNorm :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hBoundaryNonnegative
  change max
      ‖geometric.greenCore.core.inclusion (geometric.extension data)‖
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
    bounds.graphConstant * boundaryNorm
  exact max_le hInclusion hOperator

/-- Install the cutoff-closed boundary data from component extension estimates. -/
def toCutoffClosedBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (garding : geometric.greenCore.SquaredGardingEstimate period hPeriod)
    (normalRegularity : geometric.greenCore.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (bounds : CanonicalPhysicalScalarCauchyExtensionComponentBounds
      period hPeriod geometric) :
    CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  geometric := geometric
  garding := garding
  normalRegularity := normalRegularity
  extensionConstant := bounds.graphConstant
  extensionConstant_nonnegative := bounds.graphConstant_nonnegative
  extensionGraphBound := bounds.graph_bound

/-- Component-bound construction certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (garding : geometric.greenCore.SquaredGardingEstimate period hPeriod)
    (normalRegularity : geometric.greenCore.NormalRegularityData
      period hPeriod (Regularity := Regularity))
    (bounds : CanonicalPhysicalScalarCauchyExtensionComponentBounds
      period hPeriod geometric) :
    geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          geometric.greenCore.core
          (bounds.toCutoffClosedBoundaryData geometric garding normalRegularity)
            |>.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
              |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound) :=
  (bounds.toCutoffClosedBoundaryData geometric garding normalRegularity).certificate
    |>.elim fun hDense hRest => ⟨hDense, hRest.2⟩

end CanonicalPhysicalScalarCauchyExtensionComponentBounds

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionComponentBounds4D
end JanusFormal
