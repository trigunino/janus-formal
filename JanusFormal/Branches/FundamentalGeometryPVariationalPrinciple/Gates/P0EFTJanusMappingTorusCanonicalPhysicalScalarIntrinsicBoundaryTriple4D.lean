import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D

/-!
# Intrinsic physical scalar boundary-triple inputs

Smooth quotient scalar fields are now unconditionally dense in physical bulk
`L²`, by manifold smooth approximation.  Therefore the fully geometric boundary
package no longer needs a user-supplied continuous-to-smooth approximation.

The remaining density input is only the geometric shrinking-collar cutoff family
that annihilates both Cauchy traces.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicBoundaryTriple4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Physical boundary inputs after smooth L2 density has been discharged. -/
structure CanonicalPhysicalScalarIntrinsicBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  geometric : CanonicalPhysicalScalarGeometricGreenCoreData
    period hPeriod massSquared ValueCore NormalCore
  cutoff : Nat →
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      SmoothQuotientField period hPeriod Real
  cutoff_boundary_zero : ∀ (index : Nat)
    (field : SmoothQuotientField period hPeriod Real),
    geometric.greenCore.core.boundaryTrace (cutoff index field) = 0
  cutoff_tendsto_l2 : ∀ field : SmoothQuotientField period hPeriod Real,
    Tendsto
      (fun index => geometric.greenCore.core.inclusion (cutoff index field))
      atTop (𝓝 (geometric.greenCore.core.inclusion field))
  garding : geometric.greenCore.SquaredGardingEstimate period hPeriod
  normalRegularity : geometric.greenCore.NormalRegularityData
    period hPeriod (Regularity := Regularity)
  extensionConstant : Real
  extensionConstant_nonnegative : 0 ≤ extensionConstant
  extensionGraphBound : ∀ data : ValueCore × NormalCore,
    ‖P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreToGraph
        geometric.greenCore.core (geometric.extension data)‖ ≤
      extensionConstant *
        ‖canonicalScalarBoundaryCorePairEmbedding
          geometric.valueEmbedding geometric.normalEmbedding data‖

namespace CanonicalPhysicalScalarIntrinsicBoundaryData

/-- Conversion to the fully geometric package, filling smooth L2 density by the
unconditional theorem. -/
def toFullyGeometricBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (intrinsic : CanonicalPhysicalScalarIntrinsicBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  geometric := intrinsic.geometric
  smoothing := canonicalPhysicalScalarContinuousSmoothApproximationData
    period hPeriod
  cutoff := intrinsic.cutoff
  cutoff_boundary_zero := intrinsic.cutoff_boundary_zero
  cutoff_tendsto_l2 := intrinsic.cutoff_tendsto_l2
  garding := intrinsic.garding
  normalRegularity := intrinsic.normalRegularity
  extensionConstant := intrinsic.extensionConstant
  extensionConstant_nonnegative := intrinsic.extensionConstant_nonnegative
  extensionGraphBound := intrinsic.extensionGraphBound

/-- Correct completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (intrinsic : CanonicalPhysicalScalarIntrinsicBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  intrinsic.toFullyGeometricBoundaryData.triple

/-- Completed boundary inputs. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (intrinsic : CanonicalPhysicalScalarIntrinsicBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  intrinsic.toFullyGeometricBoundaryData.completedInputs

/-- Intrinsic boundary-triple certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (intrinsic : CanonicalPhysicalScalarIntrinsicBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
          period hPeriod) ∧
      intrinsic.geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          intrinsic.geometric.greenCore.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          intrinsic.geometric.greenCore.core
          intrinsic.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
            |>.toEllipticBoundaryData.toBoundaryConstructionData.traceBound) :=
  ⟨smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod,
    intrinsic.toFullyGeometricBoundaryData.minimalCollarCutoffData
      |>.minimalCoreDense intrinsic.geometric.greenCore,
    intrinsic.triple.inclusion_injective,
    intrinsic.toFullyGeometricBoundaryData.cutoffEllipticBoundaryData
      |>.toEllipticBoundaryData.toBoundaryConstructionData
      |>.completedTraceSurjective⟩

end CanonicalPhysicalScalarIntrinsicBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicBoundaryTriple4D
end JanusFormal
