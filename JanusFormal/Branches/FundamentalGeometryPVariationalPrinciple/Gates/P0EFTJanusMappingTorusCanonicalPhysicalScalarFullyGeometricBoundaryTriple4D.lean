import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCollarCutoffDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffEllipticBoundaryTriple4D

/-!
# Fully geometric construction of the physical scalar boundary triple

The smooth Green core is constructed from wave naturality, the Euler-divergence
integral theorem and a smooth Cauchy jet extension.  Smooth density in bulk L2
is constructed from continuous-to-smooth approximation.  Shrinking collar
cutoffs then give minimal-core density.  Gårding and higher normal regularity
supply the paired graph trace estimate, while the graph bound on the smooth
Cauchy extension supplies surjectivity after completion.

This file packages all those ingredients and returns the corrected completed
physical boundary triple without an abstract density, closability or
surjectivity hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D

set_option autoImplicit false
noncomputable section

open Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCollarCutoffDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffEllipticBoundaryTriple4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusScalarGreenCoreMinimalCutoffDensity4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Fully geometric boundary-triple inputs. -/
structure CanonicalPhysicalScalarFullyGeometricBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  geometric : CanonicalPhysicalScalarGeometricGreenCoreData
    period hPeriod massSquared ValueCore NormalCore
  smoothing : CanonicalPhysicalScalarContinuousSmoothApproximationData
    period hPeriod
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

namespace CanonicalPhysicalScalarFullyGeometricBoundaryData

/-- Underlying physical Green core. -/
def green
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  boundaryData.geometric.greenCore

/-- Physical smoothing and shrinking collar cutoff data. -/
def minimalCollarCutoffData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarMinimalCollarCutoffData
      period hPeriod boundaryData.green where
  smoothing := boundaryData.smoothing
  cutoff := boundaryData.cutoff
  boundary_zero := boundaryData.cutoff_boundary_zero
  tendsto_l2 := boundaryData.cutoff_tendsto_l2

/-- Generic minimal cutoff package. -/
def genericCutoffData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalScalarGreenCoreMinimalCutoffData boundaryData.green.core :=
  (boundaryData.minimalCollarCutoffData period hPeriod).toGeneric
    period hPeriod boundaryData.green

/-- Elliptic cutoff boundary construction. -/
def cutoffEllipticBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarCutoffEllipticBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  smooth := boundaryData.geometric.smoothCauchyExtensionData
  garding := boundaryData.garding
  normalRegularity := boundaryData.normalRegularity
  cutoff := boundaryData.genericCutoffData period hPeriod
  extensionConstant := boundaryData.extensionConstant
  extensionConstant_nonnegative := boundaryData.extensionConstant_nonnegative
  extensionGraphBound := boundaryData.extensionGraphBound

/-- Fully constructed completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (boundaryData.cutoffEllipticBoundaryData period hPeriod).triple
    period hPeriod

/-- Completed boundary inputs. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (boundaryData.cutoffEllipticBoundaryData period hPeriod).completedInputs
    period hPeriod

/-- Fully geometric boundary-triple certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
          period hPeriod) ∧
      boundaryData.green.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          boundaryData.green.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          boundaryData.green.core
          (((boundaryData.cutoffEllipticBoundaryData period hPeriod)
            |>.toEllipticBoundaryData period hPeriod)
            |>.toBoundaryConstructionData period hPeriod).traceBound) :=
  ⟨boundaryData.geometric.smoothCauchyExtensionData.boundaryTrace_denseRange,
    boundaryData.smoothing.smoothToCanonicalPhysicalBulkL2_denseRange,
    (boundaryData.minimalCollarCutoffData period hPeriod).minimalCoreDense
      period hPeriod boundaryData.green,
    (boundaryData.triple period hPeriod).inclusion_injective,
    (((boundaryData.cutoffEllipticBoundaryData period hPeriod)
      |>.toEllipticBoundaryData period hPeriod)
      |>.toBoundaryConstructionData period hPeriod).completedTraceSurjective⟩

end CanonicalPhysicalScalarFullyGeometricBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D
end JanusFormal
