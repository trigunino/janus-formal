import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D

/-!
# Physical scalar boundary triple with the cutoff theorem closed

The globally descended shrinking cutoffs are now constructed and converge in the
physical bulk `L²`.  Consequently the fully geometric boundary package no
longer needs a user-supplied smoothing scheme or collar cutoff family.

The remaining boundary inputs are geometric Green-core data, Gårding, higher
normal regularity, and a graph-bounded smooth Cauchy extension.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyGeometricBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Physical boundary inputs after the smooth-density and shrinking-cutoff
arguments have both been discharged. -/
structure CanonicalPhysicalScalarCutoffClosedBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  geometric : CanonicalPhysicalScalarGeometricGreenCoreData
    period hPeriod massSquared ValueCore NormalCore
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

namespace CanonicalPhysicalScalarCutoffClosedBoundaryData

/-- Conversion to the previous fully geometric package, with smoothing and
cutoffs filled by theorem. -/
def toFullyGeometricBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarFullyGeometricBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  geometric := boundaryData.geometric
  smoothing := canonicalPhysicalScalarContinuousSmoothApproximationData
    period hPeriod
  cutoff := canonicalLatitudeMinimalCutoffLinearMap period hPeriod
  cutoff_boundary_zero := by
    intro index field
    change P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
      period hPeriod
      (canonicalLatitudeMinimalCutoffLinearMap
        period hPeriod index field) = 0
    exact smoothFirstSheetCauchyTrace_minimalCutoff_eq_zero
      period hPeriod index field
  cutoff_tendsto_l2 :=
    smoothToCanonicalPhysicalBulkL2_minimalCutoff_tendsto period hPeriod
  garding := boundaryData.garding
  normalRegularity := boundaryData.normalRegularity
  extensionConstant := boundaryData.extensionConstant
  extensionConstant_nonnegative := boundaryData.extensionConstant_nonnegative
  extensionGraphBound := boundaryData.extensionGraphBound

/-- Correct completed physical boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (boundaryData.toFullyGeometricBoundaryData period hPeriod).triple
    period hPeriod

/-- Completed physical boundary inputs. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (boundaryData.toFullyGeometricBoundaryData period hPeriod).completedInputs
    period hPeriod

/-- Cutoff-closed boundary certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    boundaryData.geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          boundaryData.geometric.greenCore.core) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          boundaryData.geometric.greenCore.core
          (((boundaryData.toFullyGeometricBoundaryData period hPeriod)
            |>.cutoffEllipticBoundaryData period hPeriod)
            |>.toEllipticBoundaryData period hPeriod
            |>.toBoundaryConstructionData period hPeriod).traceBound) :=
  ⟨canonicalPhysicalScalarMinimalCoreDense
      period hPeriod boundaryData.geometric.greenCore,
    (boundaryData.triple period hPeriod).inclusion_injective,
    ((((boundaryData.toFullyGeometricBoundaryData period hPeriod)
      |>.cutoffEllipticBoundaryData period hPeriod)
      |>.toEllipticBoundaryData period hPeriod)
      |>.toBoundaryConstructionData period hPeriod).completedTraceSurjective⟩

end CanonicalPhysicalScalarCutoffClosedBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D
end JanusFormal
