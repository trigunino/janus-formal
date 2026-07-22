import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

/-!
# Physical scalar PDE boundary closure

This file assembles the four concrete PDE layers of the corrected physical
boundary triple:

1. geometric Green-core data from Euler overlap compatibility, the explicit
   Cauchy jet and the global divergence integral;
2. a Gårding energy estimate;
3. higher elliptic regularity with a bounded normal trace;
4. `H¹` and Euler-residual estimates for the explicit Cauchy lift.

The value trace is already controlled by spherical coarea.  The shrinking global
cutoffs already make the minimal zero-Cauchy core dense.  The four layers above
therefore construct the paired graph trace, a bounded right inverse of its
completion, and the genuine surjective completed physical boundary triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarPDEBoundaryClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosed4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarBoundaryCauchyGraphExtension4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Physical `H¹` and Euler-residual estimates for the explicit compatibility
Cauchy extension. -/
structure CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) where
  h1Constant : Real
  h1Constant_nonnegative : 0 ≤ h1Constant
  operatorConstant : Real
  operatorConstant_nonnegative : 0 ≤ operatorConstant
  h1_bound : ∀ data : ValueCore × NormalCore,
    ‖P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
        period hPeriod (geometric.extension data)‖ ≤
      h1Constant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.boundaryCore.valueEmbedding
          geometric.boundaryCore.normalEmbedding data‖
  operator_bound : ∀ data : ValueCore × NormalCore,
    ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤
      operatorConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.boundaryCore.valueEmbedding
          geometric.boundaryCore.normalEmbedding data‖

namespace CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds

/-- Bulk `L²` constant obtained through the continuous `H¹ -> L²` map. -/
def inclusionConstant
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
      period hPeriod geometric) : Real :=
  ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ * bounds.h1Constant

/-- Nonnegativity of the induced bulk constant. -/
theorem inclusionConstant_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
      period hPeriod geometric) :
    0 ≤ bounds.inclusionConstant :=
  mul_nonneg (norm_nonneg _) bounds.h1Constant_nonnegative

/-- Bulk `L²` estimate for the explicit extension. -/
theorem inclusion_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
      period hPeriod geometric)
    (data : ValueCore × NormalCore) :
    ‖geometric.greenCore.core.inclusion (geometric.extension data)‖ ≤
      bounds.inclusionConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.boundaryCore.valueEmbedding
          geometric.boundaryCore.normalEmbedding data‖ := by
  let extensionH1 :=
    P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
      period hPeriod (geometric.extension data)
  let boundaryNorm :=
    ‖canonicalScalarBoundaryCorePairEmbedding
      geometric.boundaryCore.valueEmbedding
      geometric.boundaryCore.normalEmbedding data‖
  change ‖smoothToCanonicalPhysicalBulkL2 period hPeriod
      (geometric.extension data)‖ ≤ _
  rw [← canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth]
  calc
    ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod extensionH1‖ ≤
        ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ * ‖extensionH1‖ :=
      (canonicalPhysicalScalarH1ToBulkL2 period hPeriod).le_opNorm extensionH1
    _ ≤ ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ *
        (bounds.h1Constant * boundaryNorm) :=
      mul_le_mul_of_nonneg_left (bounds.h1_bound data) (norm_nonneg _)
    _ = bounds.inclusionConstant * boundaryNorm := by
      unfold inclusionConstant
      ring

/-- Common graph constant. -/
def graphConstant
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
      period hPeriod geometric) : Real :=
  max bounds.inclusionConstant bounds.operatorConstant

/-- Nonnegativity of the graph constant. -/
theorem graphConstant_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
      period hPeriod geometric) :
    0 ≤ bounds.graphConstant :=
  bounds.inclusionConstant_nonnegative.trans (le_max_left _ _)

/-- Complete graph bound of the explicit Cauchy extension. -/
theorem graph_bound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
      period hPeriod geometric)
    (data : ValueCore × NormalCore) :
    ‖canonicalScalarGreenCoreToGraph geometric.greenCore.core
        (geometric.extension data)‖ ≤
      bounds.graphConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.boundaryCore.valueEmbedding
          geometric.boundaryCore.normalEmbedding data‖ := by
  change max
      ‖geometric.greenCore.core.inclusion (geometric.extension data)‖
      ‖geometric.greenCore.core.operator (geometric.extension data)‖ ≤ _
  apply max_le
  · exact (bounds.inclusion_bound data).trans
      (mul_le_mul_of_nonneg_right
        (le_max_left bounds.inclusionConstant bounds.operatorConstant)
        (norm_nonneg _))
  · exact (bounds.operator_bound data).trans
      (mul_le_mul_of_nonneg_right
        (le_max_right bounds.inclusionConstant bounds.operatorConstant)
        (norm_nonneg _))

/-- Generic bounded smooth Cauchy extension. -/
def boundedSmoothExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore}
    (bounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
      period hPeriod geometric) :
    CanonicalScalarBoundedSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore)
      geometric.greenCore.core where
  smooth :=
    { valueEmbedding := geometric.boundaryCore.valueEmbedding
      normalEmbedding := geometric.boundaryCore.normalEmbedding
      valueDense := geometric.boundaryCore.valueDense
      normalDense := geometric.boundaryCore.normalDense
      extension := geometric.extension
      boundary_extension := geometric.cauchyTrace_extension }
  constant := bounds.graphConstant
  nonnegative := bounds.graphConstant_nonnegative
  graph_bound := bounds.graph_bound

end CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds

/-- Complete PDE input for the physical completed boundary triple. -/
structure CanonicalPhysicalScalarPDEBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  geometric : CanonicalPhysicalScalarCauchyJetCompatibilityData
    period hPeriod massSquared ValueCore NormalCore
  gardingEnergy : geometric.greenCore.EnergyGardingData period hPeriod
  normalRegularity : geometric.greenCore.NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  extensionBounds : CanonicalPhysicalScalarCompatibilityCauchyExtensionBounds
    period hPeriod geometric

namespace CanonicalPhysicalScalarPDEBoundaryData

/-- Graph-elliptic estimate from the Gårding energy argument. -/
def elliptic
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    pde.geometric.greenCore.GraphEllipticEstimate period hPeriod :=
  pde.gardingEnergy.toGraphEllipticEstimate pde.geometric.greenCore

/-- Normal graph estimate from higher elliptic regularity. -/
def normal
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    pde.geometric.greenCore.NormalGraphEstimate period hPeriod :=
  pde.normalRegularity.toNormalGraphEstimate pde.geometric.greenCore

/-- Paired physical boundary trace bound. -/
def traceBound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
      pde.geometric.greenCore.core :=
  pde.geometric.greenCore.boundaryGraphBound period hPeriod
    (canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod)
    pde.elliptic pde.normal

/-- Minimal zero-Cauchy core density from the constructed global cutoffs. -/
theorem minimalCoreDense
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    pde.geometric.greenCore.MinimalCoreDense period hPeriod :=
  canonicalPhysicalScalarMinimalCoreDense
    period hPeriod pde.geometric.greenCore

/-- Surjectivity of the completed paired Cauchy trace. -/
theorem completedTraceSurjective
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace
        pde.geometric.greenCore.core pde.traceBound) :=
  pde.extensionBounds.boundedSmoothExtension
    |>.completedBoundaryTrace_surjective pde.traceBound

/-- Correct physical completed-boundary input package. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    pde.geometric.greenCore.CompletedBoundaryTripleInputs period hPeriod where
  coarea := canonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod
  elliptic := pde.elliptic
  normal := pde.normal
  minimalDense := pde.minimalCoreDense
  completedTraceSurjective := pde.completedTraceSurjective

/-- Genuine surjective completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  pde.completedInputs.triple pde.geometric.greenCore

/-- Bounded right inverse of the completed physical Cauchy trace. -/
def completedExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  pde.extensionBounds.boundedSmoothExtension.completedExtension

/-- Full four-layer PDE boundary certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) ∧
      pde.geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          pde.geometric.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          pde.geometric.greenCore.core pde.traceBound) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            pde.geometric.greenCore.core pde.traceBound
            (pde.completedExtension boundary) = boundary) :=
  ⟨pde.geometric.boundaryTrace_denseRange,
    pde.minimalCoreDense,
    pde.triple.inclusion_injective,
    pde.completedTraceSurjective,
    pde.extensionBounds.boundedSmoothExtension
      |>.completedBoundaryTrace_extension pde.traceBound⟩

end CanonicalPhysicalScalarPDEBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarPDEBoundaryClosure4D
end JanusFormal
