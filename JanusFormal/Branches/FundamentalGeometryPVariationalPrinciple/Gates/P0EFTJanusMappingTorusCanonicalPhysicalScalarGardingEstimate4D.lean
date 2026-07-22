import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSquaredGraphEstimates4D

/-!
# Gårding inequality and the physical scalar graph estimate

The natural elliptic estimate is usually proved as

`‖u‖_H1² ≤ C (‖u‖_L2² + ‖A u‖_L2²)`.

The Program-P graph norm is the product sup norm of `(u,A u)`.  Each component is
bounded by that graph norm, so the sum of squares is bounded by twice its square.
Thus the Gårding estimate gives the squared graph-elliptic estimate with constant
`sqrt (2 C)` and hence the linear graph estimate required by the completed
boundary trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSquaredGraphEstimates4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- The ambient-value coordinate is bounded by the graph norm. -/
theorem inclusion_norm_le_graph
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖green.core.inclusion field‖ ≤
      ‖canonicalScalarGreenCoreToGraph green.core field‖ := by
  change ‖green.core.inclusion field‖ ≤
    max ‖green.core.inclusion field‖ ‖green.core.operator field‖
  exact le_max_left _ _

/-- The Euler coordinate is bounded by the graph norm. -/
theorem operator_norm_le_graph
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖green.core.operator field‖ ≤
      ‖canonicalScalarGreenCoreToGraph green.core field‖ := by
  change ‖green.core.operator field‖ ≤
    max ‖green.core.inclusion field‖ ‖green.core.operator field‖
  exact le_max_right _ _

/-- Squared physical Gårding estimate. -/
structure SquaredGardingEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound_sq : ∀ field : SmoothQuotientField period hPeriod Real,
    ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
      constant *
        (‖green.core.inclusion field‖ ^ 2 +
          ‖green.core.operator field‖ ^ 2)

namespace SquaredGardingEstimate

/-- Graph constant obtained from the Gårding constant. -/
def graphConstant
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (garding : green.SquaredGardingEstimate period hPeriod) : Real :=
  Real.sqrt (2 * garding.constant)

/-- The graph constant is nonnegative. -/
theorem graphConstant_nonnegative
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (garding : green.SquaredGardingEstimate period hPeriod) :
    0 ≤ garding.graphConstant green :=
  Real.sqrt_nonneg _

/-- Sum of ambient and operator squares is controlled by twice the graph-norm
square. -/
theorem component_sq_sum_le_two_graph_sq
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (garding : green.SquaredGardingEstimate period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖green.core.inclusion field‖ ^ 2 +
        ‖green.core.operator field‖ ^ 2 ≤
      2 * ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2 := by
  have hInclusion := green.inclusion_norm_le_graph period hPeriod field
  have hOperator := green.operator_norm_le_graph period hPeriod field
  have hInclusionNonnegative := norm_nonneg (green.core.inclusion field)
  have hOperatorNonnegative := norm_nonneg (green.core.operator field)
  have hGraphNonnegative :=
    norm_nonneg (canonicalScalarGreenCoreToGraph green.core field)
  nlinarith

/-- Gårding gives the squared graph-elliptic estimate. -/
def toSquaredGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (garding : green.SquaredGardingEstimate period hPeriod) :
    green.SquaredGraphEllipticEstimate period hPeriod where
  constant := garding.graphConstant green
  nonnegative := garding.graphConstant_nonnegative green
  bound_sq := by
    intro field
    have hGarding := garding.bound_sq field
    have hComponents := garding.component_sq_sum_le_two_graph_sq green field
    have hScaled :
        garding.constant *
            (‖green.core.inclusion field‖ ^ 2 +
              ‖green.core.operator field‖ ^ 2) ≤
          garding.constant *
            (2 * ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hComponents garding.nonnegative
    calc
      ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
          garding.constant *
            (‖green.core.inclusion field‖ ^ 2 +
              ‖green.core.operator field‖ ^ 2) := hGarding
      _ ≤ garding.constant *
          (2 * ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2) :=
        hScaled
      _ = (garding.graphConstant green) ^ 2 *
          ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2 := by
        unfold graphConstant
        rw [Real.sq_sqrt]
        · ring
        · exact mul_nonneg (by norm_num) garding.nonnegative

/-- Gårding gives the linear graph-elliptic estimate. -/
def toGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (garding : green.SquaredGardingEstimate period hPeriod) :
    green.GraphEllipticEstimate period hPeriod :=
  (garding.toSquaredGraphEllipticEstimate green).toGraphEllipticEstimate green

/-- Gårding-to-graph certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (garding : green.SquaredGardingEstimate period hPeriod) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
        (garding.graphConstant green) ^ 2 *
          ‖canonicalScalarGreenCoreToGraph green.core field‖ ^ 2) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ≤
          garding.graphConstant green *
            ‖canonicalScalarGreenCoreToGraph green.core field‖) :=
  ⟨(garding.toSquaredGraphEllipticEstimate green).bound_sq,
    (garding.toGraphEllipticEstimate green).bound⟩

end SquaredGardingEstimate

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
end JanusFormal
