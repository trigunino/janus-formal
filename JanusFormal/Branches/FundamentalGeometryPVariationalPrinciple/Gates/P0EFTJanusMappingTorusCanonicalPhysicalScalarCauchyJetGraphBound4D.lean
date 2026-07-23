import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

/-!
# Graph bound for the explicit physical Cauchy-jet extension

The graph norm of the smooth physical Euler operator is the maximum of its bulk
`L²` component and its Euler-residual component.  Therefore a graph estimate for
the explicit Cauchy extension need not be supplied as one opaque theorem.

It is enough to prove separately

* an `L²` estimate for the extended field;
* an `L²` estimate for its Euler residual.

The maximum of the two constants gives the graph bound.  The generic completion
theorem then extends the smooth Cauchy lift to a bounded right inverse of the
completed trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Dense embedding of the smooth value-normal core into the boundary Hilbert
pair. -/
def boundaryCoreEmbedding
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :=
  canonicalScalarBoundaryCorePairEmbedding
    geometric.boundaryCore.valueEmbedding
    geometric.boundaryCore.normalEmbedding

/-- Componentwise estimates for the explicit Cauchy-jet extension. -/
structure CauchyJetComponentGraphEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) where
  inclusionConstant : Real
  inclusionConstant_nonnegative : 0 ≤ inclusionConstant
  operatorConstant : Real
  operatorConstant_nonnegative : 0 ≤ operatorConstant
  inclusion_bound : ∀ data : ValueCore × NormalCore,
    ‖(geometric.greenCore period hPeriod).core.inclusion
        (geometric.extension period hPeriod data)‖ ≤
      inclusionConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖
  operator_bound : ∀ data : ValueCore × NormalCore,
    ‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ ≤
      operatorConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖

namespace CauchyJetComponentGraphEstimateData

/-- Combined graph-extension constant. -/
def graphConstant
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetComponentGraphEstimateData
      period hPeriod) : Real :=
  Real.sqrt 2 * max estimate.inclusionConstant estimate.operatorConstant

/-- Nonnegativity of the combined constant. -/
theorem graphConstant_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetComponentGraphEstimateData
      period hPeriod) :
    0 ≤ estimate.graphConstant :=
  mul_nonneg (Real.sqrt_nonneg _)
    (estimate.inclusionConstant_nonnegative.trans (le_max_left _ _))

/-- The componentwise estimates imply the required graph-norm bound. -/
theorem graph_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetComponentGraphEstimateData
      period hPeriod)
    (data : ValueCore × NormalCore) :
    ‖canonicalScalarGreenCoreToGraph
        (geometric.greenCore period hPeriod).core
        (geometric.extension period hPeriod data)‖ ≤
      estimate.graphConstant *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ := by
  let boundaryNorm :=
    ‖geometric.boundaryCoreEmbedding period hPeriod data‖
  have hBoundaryNonnegative : 0 ≤ boundaryNorm := norm_nonneg _
  have hInclusion :
      ‖(geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data)‖ ≤
        max estimate.inclusionConstant estimate.operatorConstant *
          boundaryNorm :=
    (estimate.inclusion_bound data).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hBoundaryNonnegative)
  have hOperator :
      ‖(geometric.greenCore period hPeriod).core.operator
          (geometric.extension period hPeriod data)‖ ≤
        max estimate.inclusionConstant estimate.operatorConstant *
          boundaryNorm :=
    (estimate.operator_bound data).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hBoundaryNonnegative)
  have hCommonNonnegative :
      0 ≤ max estimate.inclusionConstant estimate.operatorConstant *
        boundaryNorm :=
    mul_nonneg
      (estimate.inclusionConstant_nonnegative.trans (le_max_left _ _))
      hBoundaryNonnegative
  have hInclusionSq :
      ‖(geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data)‖ ^ 2 ≤
        (max estimate.inclusionConstant estimate.operatorConstant *
          boundaryNorm) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hInclusion)
      (add_nonneg hCommonNonnegative
        (norm_nonneg ((geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data))))]
  have hOperatorSq :
      ‖(geometric.greenCore period hPeriod).core.operator
          (geometric.extension period hPeriod data)‖ ^ 2 ≤
        (max estimate.inclusionConstant estimate.operatorConstant *
          boundaryNorm) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hOperator)
      (add_nonneg hCommonNonnegative
        (norm_nonneg ((geometric.greenCore period hPeriod).core.operator
          (geometric.extension period hPeriod data))))]
  have hGraphSq :
      ‖canonicalScalarGreenCoreToGraph
          (geometric.greenCore period hPeriod).core
          (geometric.extension period hPeriod data)‖ ^ 2 =
        ‖(geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data)‖ ^ 2 +
        ‖(geometric.greenCore period hPeriod).core.operator
          (geometric.extension period hPeriod data)‖ ^ 2 := by
    exact WithLp.prod_norm_sq_eq_of_L2
      (canonicalScalarGreenCoreToGraph
        (geometric.greenCore period hPeriod).core
        (geometric.extension period hPeriod data)).1
  have hRightSq :
      (estimate.graphConstant * boundaryNorm) ^ 2 =
        2 * (max estimate.inclusionConstant estimate.operatorConstant *
          boundaryNorm) ^ 2 := by
    unfold graphConstant
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
    ring
  have hGraphSqLe :
      ‖canonicalScalarGreenCoreToGraph
          (geometric.greenCore period hPeriod).core
          (geometric.extension period hPeriod data)‖ ^ 2 ≤
        (estimate.graphConstant * boundaryNorm) ^ 2 := by
    linarith
  have hRightNonnegative :
      0 ≤ estimate.graphConstant * boundaryNorm :=
    mul_nonneg estimate.graphConstant_nonnegative hBoundaryNonnegative
  nlinarith [norm_nonneg
    (canonicalScalarGreenCoreToGraph
      (geometric.greenCore period hPeriod).core
      (geometric.extension period hPeriod data))]

/-- Generic smooth Cauchy-extension package generated by the explicit physical
jet construction. -/
def smoothExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetComponentGraphEstimateData
      period hPeriod) :
    CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore)
      (geometric.greenCore period hPeriod).core.boundaryTrace where
  valueEmbedding := geometric.boundaryCore.valueEmbedding
  normalEmbedding := geometric.boundaryCore.normalEmbedding
  valueDense := geometric.boundaryCore.valueDense
  normalDense := geometric.boundaryCore.normalDense
  extension := geometric.extension period hPeriod
  boundary_extension := geometric.cauchyTrace_extension period hPeriod

/-- Bounded smooth extension data for the corrected physical Green core. -/
def toBoundedSmoothCauchyExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetComponentGraphEstimateData
      period hPeriod) :
    CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore)
      (geometric.greenCore period hPeriod).core where
  smooth := estimate.smoothExtensionData period hPeriod
  constant := estimate.graphConstant
  nonnegative := estimate.graphConstant_nonnegative
  graph_bound := estimate.graph_bound period hPeriod

/-- The completed boundary trace is surjective for every available paired trace
bound. -/
theorem completedBoundaryTrace_surjective
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetComponentGraphEstimateData
      period hPeriod)
    (traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
      (geometric.greenCore period hPeriod).core) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace
        (geometric.greenCore period hPeriod).core traceBound) :=
  estimate.toBoundedSmoothCauchyExtensionData period hPeriod
    |>.completedBoundaryTrace_surjective traceBound

/-- Component graph-bound certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (estimate : geometric.CauchyJetComponentGraphEstimateData
      period hPeriod) :
    (∀ data : ValueCore × NormalCore,
      ‖canonicalScalarGreenCoreToGraph
          (geometric.greenCore period hPeriod).core
          (geometric.extension period hPeriod data)‖ ≤
        estimate.graphConstant *
          ‖geometric.boundaryCoreEmbedding period hPeriod data‖) ∧
      (∀ traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
          (geometric.greenCore period hPeriod).core,
        Function.Surjective
          (canonicalScalarGreenCoreCompletedBoundaryTrace
            (geometric.greenCore period hPeriod).core traceBound)) :=
  ⟨estimate.graph_bound period hPeriod,
    estimate.completedBoundaryTrace_surjective period hPeriod⟩

end CauchyJetComponentGraphEstimateData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
end JanusFormal
