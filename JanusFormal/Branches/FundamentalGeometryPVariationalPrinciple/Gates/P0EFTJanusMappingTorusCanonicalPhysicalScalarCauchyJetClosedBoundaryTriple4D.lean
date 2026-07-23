import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionH1EulerBounds4D

/-!
# Boundary triple from a globalized Cauchy jet

This is the constructive boundary interface after the global cutoff theorem.
The smooth extension is no longer supplied as an opaque field: it is generated
by the exact latitude Cauchy profiles and a deck-invariant collar globalization.
Its graph bound is reduced to separate physical `H¹` and Euler-residual
estimates.

Together with Gårding and higher normal regularity, these data construct the
surjective completed physical boundary triple and the dense zero-Cauchy minimal
core.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetClosedBoundaryTriple4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyExtensionH1EulerBounds4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedBoundaryTriple4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Constructive boundary data based on an explicit globalized Cauchy jet. -/
structure CanonicalPhysicalScalarCauchyJetClosedBoundaryData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  constructive : CanonicalPhysicalScalarCauchyJetGreenCoreData
    period hPeriod massSquared ValueCore NormalCore
  garding : constructive.toGeometricGreenCoreData.greenCore.SquaredGardingEstimate
    period hPeriod
  normalRegularity :
    constructive.toGeometricGreenCoreData.greenCore.NormalRegularityData
      period hPeriod (Regularity := Regularity)
  extensionBounds : CanonicalPhysicalScalarCauchyExtensionH1EulerBounds
    period hPeriod constructive.toGeometricGreenCoreData

namespace CanonicalPhysicalScalarCauchyJetClosedBoundaryData

/-- Conversion to the cutoff-closed boundary package. -/
def toCutoffClosedBoundaryData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyJetClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarCutoffClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) :=
  boundaryData.extensionBounds.toCutoffClosedBoundaryData period hPeriod
    boundaryData.constructive.toGeometricGreenCoreData
    boundaryData.garding boundaryData.normalRegularity

/-- Constructed completed boundary triple. -/
def triple
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyJetClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (boundaryData.toCutoffClosedBoundaryData period hPeriod).triple
    period hPeriod

/-- Constructed completed boundary inputs. -/
def completedInputs
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyJetClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (boundaryData.toCutoffClosedBoundaryData period hPeriod).completedInputs
    period hPeriod

/-- The zero-Cauchy minimal core is dense. -/
theorem minimalCoreDense
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyJetClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    boundaryData.constructive.greenCore.MinimalCoreDense period hPeriod :=
  ((boundaryData.toCutoffClosedBoundaryData period hPeriod).certificate
    period hPeriod).1

/-- The maximal graph inclusion is injective. -/
theorem graphInclusion_injective
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyJetClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    Function.Injective
      (canonicalScalarGreenCoreGraphInclusion
        boundaryData.constructive.greenCore.core) :=
  ((boundaryData.toCutoffClosedBoundaryData period hPeriod).certificate
    period hPeriod).2.1

/-- The completed Cauchy trace is surjective. -/
theorem completedTrace_surjective
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyJetClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    Function.Surjective
      (canonicalScalarGreenCoreCompletedBoundaryTrace
        boundaryData.constructive.greenCore.core
        ((((boundaryData.toCutoffClosedBoundaryData period hPeriod)
          |>.toFullyGeometricBoundaryData period hPeriod)
          |>.cutoffEllipticBoundaryData period hPeriod)
          |>.toEllipticBoundaryData period hPeriod
          |>.toBoundaryConstructionData period hPeriod).traceBound) :=
  ((boundaryData.toCutoffClosedBoundaryData period hPeriod).certificate
    period hPeriod).2.2

/-- Constructive Cauchy-jet boundary certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (boundaryData : CanonicalPhysicalScalarCauchyJetClosedBoundaryData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      boundaryData.constructive.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          boundaryData.constructive.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          boundaryData.constructive.greenCore.core
          ((((boundaryData.toCutoffClosedBoundaryData period hPeriod)
            |>.toFullyGeometricBoundaryData period hPeriod)
            |>.cutoffEllipticBoundaryData period hPeriod)
            |>.toEllipticBoundaryData period hPeriod
            |>.toBoundaryConstructionData period hPeriod).traceBound) :=
  ⟨boundaryData.constructive.boundaryTrace_denseRange,
    boundaryData.minimalCoreDense period hPeriod,
    boundaryData.graphInclusion_injective period hPeriod,
    boundaryData.completedTrace_surjective period hPeriod⟩

end CanonicalPhysicalScalarCauchyJetClosedBoundaryData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetClosedBoundaryTriple4D
end JanusFormal
