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

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}
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
        period hPeriod (geometric.extension period hPeriod data)‖ ≤
      h1Constant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.boundaryCore.valueEmbedding
          geometric.boundaryCore.normalEmbedding data‖
  operator_bound : ∀ data : ValueCore × NormalCore,
    ‖(geometric.greenCore period hPeriod).core.operator
        (geometric.extension period hPeriod data)‖ ≤
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
  mul_nonneg
    (norm_nonneg (canonicalPhysicalScalarH1ToBulkL2 period hPeriod))
    bounds.h1Constant_nonnegative

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
    ‖(geometric.greenCore period hPeriod).core.inclusion
        (geometric.extension period hPeriod data)‖ ≤
      bounds.inclusionConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.boundaryCore.valueEmbedding
          geometric.boundaryCore.normalEmbedding data‖ := by
  let extensionH1 :=
    P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
      period hPeriod (geometric.extension period hPeriod data)
  let boundaryNorm :=
    ‖canonicalScalarBoundaryCorePairEmbedding
      geometric.boundaryCore.valueEmbedding
      geometric.boundaryCore.normalEmbedding data‖
  change ‖smoothToCanonicalPhysicalBulkL2 period hPeriod
      (geometric.extension period hPeriod data)‖ ≤ _
  rw [← canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth]
  calc
    ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod extensionH1‖ ≤
        ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ * ‖extensionH1‖ :=
      (canonicalPhysicalScalarH1ToBulkL2 period hPeriod).le_opNorm extensionH1
    _ ≤ ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ *
        (bounds.h1Constant * boundaryNorm) :=
      mul_le_mul_of_nonneg_left (bounds.h1_bound data)
        (norm_nonneg (canonicalPhysicalScalarH1ToBulkL2 period hPeriod))
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
  Real.sqrt 2 * max bounds.inclusionConstant bounds.operatorConstant

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
  mul_nonneg (Real.sqrt_nonneg _)
    (bounds.inclusionConstant_nonnegative.trans (le_max_left _ _))

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
    ‖canonicalScalarGreenCoreToGraph
        (geometric.greenCore period hPeriod).core
        (geometric.extension period hPeriod data)‖ ≤
      bounds.graphConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.boundaryCore.valueEmbedding
          geometric.boundaryCore.normalEmbedding data‖ := by
  let boundaryNorm :=
    ‖canonicalScalarBoundaryCorePairEmbedding
      geometric.boundaryCore.valueEmbedding
      geometric.boundaryCore.normalEmbedding data‖
  have hBoundaryNonnegative : 0 ≤ boundaryNorm := norm_nonneg _
  have hInclusion :
      ‖(geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data)‖ ≤
        max bounds.inclusionConstant bounds.operatorConstant *
          boundaryNorm := by
    exact (bounds.inclusion_bound period hPeriod data).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        hBoundaryNonnegative)
  have hOperator :
      ‖(geometric.greenCore period hPeriod).core.operator
          (geometric.extension period hPeriod data)‖ ≤
        max bounds.inclusionConstant bounds.operatorConstant *
          boundaryNorm := by
    exact (bounds.operator_bound data).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        hBoundaryNonnegative)
  have hCommonNonnegative :
      0 ≤ max bounds.inclusionConstant bounds.operatorConstant *
        boundaryNorm :=
    mul_nonneg
      (bounds.inclusionConstant_nonnegative.trans (le_max_left _ _))
      hBoundaryNonnegative
  have hInclusionSq :
      ‖(geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data)‖ ^ 2 ≤
        (max bounds.inclusionConstant bounds.operatorConstant *
          boundaryNorm) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hInclusion)
      (add_nonneg hCommonNonnegative
        (norm_nonneg ((geometric.greenCore period hPeriod).core.inclusion
          (geometric.extension period hPeriod data))))]
  have hOperatorSq :
      ‖(geometric.greenCore period hPeriod).core.operator
          (geometric.extension period hPeriod data)‖ ^ 2 ≤
        (max bounds.inclusionConstant bounds.operatorConstant *
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
      (bounds.graphConstant * boundaryNorm) ^ 2 =
        2 * (max bounds.inclusionConstant bounds.operatorConstant *
          boundaryNorm) ^ 2 := by
    unfold graphConstant
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
    ring
  have hGraphSqLe :
      ‖canonicalScalarGreenCoreToGraph
          (geometric.greenCore period hPeriod).core
          (geometric.extension period hPeriod data)‖ ^ 2 ≤
        (bounds.graphConstant * boundaryNorm) ^ 2 := by
    linarith
  have hRightNonnegative :
      0 ≤ bounds.graphConstant * boundaryNorm :=
    mul_nonneg bounds.graphConstant_nonnegative hBoundaryNonnegative
  nlinarith [norm_nonneg
    (canonicalScalarGreenCoreToGraph
      (geometric.greenCore period hPeriod).core
      (geometric.extension period hPeriod data))]

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
      (geometric.greenCore period hPeriod).core where
  smooth :=
    { valueEmbedding := geometric.boundaryCore.valueEmbedding
      normalEmbedding := geometric.boundaryCore.normalEmbedding
      valueDense := geometric.boundaryCore.valueDense
      normalDense := geometric.boundaryCore.normalDense
      extension := geometric.extension period hPeriod
      boundary_extension := geometric.cauchyTrace_extension period hPeriod }
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
  gardingEnergy : (geometric.greenCore period hPeriod).EnergyGardingData
    period hPeriod
  normalRegularity : (geometric.greenCore period hPeriod).NormalEllipticRegularityData
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
    (pde.geometric.greenCore period hPeriod).GraphEllipticEstimate
      period hPeriod :=
  pde.gardingEnergy.toGraphEllipticEstimate period hPeriod
    (pde.geometric.greenCore period hPeriod)

/-- Normal graph estimate from higher elliptic regularity. -/
def normal
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    (pde.geometric.greenCore period hPeriod).NormalGraphEstimate
      period hPeriod :=
  pde.normalRegularity.toNormalGraphEstimate period hPeriod
    (pde.geometric.greenCore period hPeriod)

/-- Paired physical boundary trace bound. -/
def traceBound
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (pde : CanonicalPhysicalScalarPDEBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound
      (pde.geometric.greenCore period hPeriod).core :=
  (pde.geometric.greenCore period hPeriod).boundaryGraphBound period hPeriod
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
    (pde.geometric.greenCore period hPeriod).MinimalCoreDense period hPeriod :=
  canonicalPhysicalScalarMinimalCoreDense
    period hPeriod (pde.geometric.greenCore period hPeriod)

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
        (pde.geometric.greenCore period hPeriod).core pde.traceBound) :=
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
    (pde.geometric.greenCore period hPeriod).CompletedBoundaryTripleInputs
      period hPeriod where
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
  pde.completedInputs.triple period hPeriod
    (pde.geometric.greenCore period hPeriod)

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
      (pde.geometric.greenCore period hPeriod).MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (pde.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          (pde.geometric.greenCore period hPeriod).core pde.traceBound) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            (pde.geometric.greenCore period hPeriod).core pde.traceBound
            (pde.completedExtension period hPeriod boundary) = boundary) :=
  ⟨pde.geometric.boundaryTrace_denseRange period hPeriod,
    pde.minimalCoreDense,
    pde.triple.inclusion_injective,
    pde.completedTraceSurjective,
    pde.extensionBounds.boundedSmoothExtension
      |>.completedBoundaryTrace_extension pde.traceBound⟩

end CanonicalPhysicalScalarPDEBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarPDEBoundaryClosure4D
end JanusFormal
