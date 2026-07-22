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
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

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
    ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
      inclusionConstant * ‖geometric.boundaryCoreEmbedding data‖
  operator_bound : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
      operatorConstant * ‖geometric.boundaryCoreEmbedding data‖

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
  max estimate.inclusionConstant estimate.operatorConstant

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
  le_max_of_subsingleton_or_nonneg
    estimate.inclusionConstant_nonnegative
    estimate.operatorConstant_nonnegative

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
    ‖canonicalScalarGreenCoreToGraph geometric.greenCore.core
        (geometric.extension data)‖ ≤
      estimate.graphConstant * ‖geometric.boundaryCoreEmbedding data‖ := by
  change max
      ‖geometric.greenCore.core.inclusion (geometric.extension data)‖
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤ _
  apply max_le
  · exact (estimate.inclusion_bound data).trans
      (mul_le_mul_of_nonneg_right
        (le_max_left estimate.inclusionConstant estimate.operatorConstant)
        (norm_nonneg _))
  · exact (estimate.operator_bound data).trans
      (mul_le_mul_of_nonneg_right
        (le_max_right estimate.inclusionConstant estimate.operatorConstant)
        (norm_nonneg _))

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
      geometric.greenCore.core.boundaryTrace where
  valueEmbedding := geometric.boundaryCore.valueEmbedding
  normalEmbedding := geometric.boundaryCore.normalEmbedding
  valueDense := geometric.boundaryCore.valueDense
  normalDense := geometric.boundaryCore.normalDense
  extension := geometric.extension
  boundary_extension := geometric.cauchyTrace_extension

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
      geometric.greenCore.core where
  smooth := estimate.smoothExtensionData
  constant := estimate.graphConstant
  nonnegative := estimate.graphConstant_nonnegative
  graph_bound := estimate.graph_bound

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
      geometric.greenCore.core) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace
        geometric.greenCore.core traceBound) :=
  estimate.toBoundedSmoothCauchyExtensionData
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
      ‖canonicalScalarGreenCoreToGraph geometric.greenCore.core
          (geometric.extension data)‖ ≤
        estimate.graphConstant * ‖geometric.boundaryCoreEmbedding data‖) ∧
      (∀ traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
          geometric.greenCore.core,
        Function.Surjective
          (canonicalScalarGreenCoreCompletedBoundaryTrace
            geometric.greenCore.core traceBound)) :=
  ⟨estimate.graph_bound,
    estimate.completedBoundaryTrace_surjective⟩

end CauchyJetComponentGraphEstimateData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D
end JanusFormal
