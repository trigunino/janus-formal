import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D

/-!
# Geometric construction of the physical scalar Green core

The physical scalar smooth Green core can be assembled from purely geometric and
local-analytic data:

* naturality of the covariant scalar wave operator across the total atlas;
* continuity of the resulting global Euler residual;
* the global integral identity relating the Euler skew density to the canonical
  divergence measure;
* dense smooth value and normal boundary cores with a smooth Cauchy jet
  extension.

The first two construct the genuine bulk-L2 Euler operator.  The divergence
identity and global Green--Stokes theorem produce the Hilbert Green identity.
The smooth Cauchy extension proves density of the smooth boundary trace.  No
abstract Green-system field remains to be supplied separately.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Complete geometric smooth-core input. -/
structure CanonicalPhysicalScalarGeometricGreenCoreData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  globalization : CanonicalPhysicalScalarWaveGlobalizationData
    period hPeriod massSquared
  valueEmbedding : ValueCore →ₗ[Real] BoundaryL2 period
  normalEmbedding : NormalCore →ₗ[Real] BoundaryL2 period
  valueDense : DenseRange valueEmbedding
  normalDense : DenseRange normalEmbedding
  extension : ValueCore × NormalCore →ₗ[Real]
    SmoothQuotientField period hPeriod Real
  boundary_extension : ∀ data,
    smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
        period hPeriod (extension data) =
      canonicalScalarBoundaryCorePairEmbedding
        valueEmbedding normalEmbedding data
  integral_eq_divergence :
    ∀ field test : SmoothQuotientField period hPeriod Real,
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarGeometricGreenCoreData

/-- Global physical Euler operator data. -/
def operatorData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :=
  geometric.globalization.toEulerGlobalizationData.toOperatorData

/-- Global Euler/divergence integral package. -/
def divergenceIntegralData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarEulerDivergenceIntegralData
      period hPeriod massSquared where
  operatorData := geometric.operatorData
  integral_eq_divergence := geometric.integral_eq_divergence

/-- Exact bulk Green--Stokes pairing for the physical Euler operator. -/
theorem bulk_green_stokes
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real (geometric.operatorData.toBulkL2LinearMap field)
          (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
            period hPeriod test) -
        inner Real
          (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
            period hPeriod field)
          (geometric.operatorData.toBulkL2LinearMap test) =
      P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod field test :=
  geometric.divergenceIntegralData.pairing_eq_orientedBoundaryCurrent
    period hPeriod field test

/-- Smooth Cauchy extension package with the physical Euler and Green identity. -/
def smoothCauchyExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarSmoothCauchyExtensionData
      period hPeriod massSquared ValueCore NormalCore where
  operatorData := geometric.operatorData
  valueEmbedding := geometric.valueEmbedding
  normalEmbedding := geometric.normalEmbedding
  valueDense := geometric.valueDense
  normalDense := geometric.normalDense
  extension := geometric.extension
  boundary_extension := geometric.boundary_extension
  bulk_green_stokes := geometric.bulk_green_stokes

/-- Correct dense physical scalar Green core. -/
def greenCore
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared :=
  geometric.smoothCauchyExtensionData.greenCoreData

/-- The physical Euler equation is zero of the constructed Green-core operator. -/
theorem eulerEquation_iff_operator_eq_zero
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (field : SmoothQuotientField period hPeriod Real) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.CanonicalPhysicalScalarEulerEquation
        period hPeriod massSquared field ↔
      geometric.greenCore.core.operator field = 0 :=
  geometric.greenCore.eulerEquation_iff_operator_eq_zero period hPeriod field

/-- Geometric Green-core construction certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    DenseRange
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) ∧
      (∀ field test : SmoothQuotientField period hPeriod Real,
        inner Real (geometric.greenCore.core.operator field)
              (geometric.greenCore.core.inclusion test) -
            inner Real (geometric.greenCore.core.inclusion field)
              (geometric.greenCore.core.operator test) =
          2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
            (geometric.greenCore.core.boundaryTrace field)
            (geometric.greenCore.core.boundaryTrace test)) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.CanonicalPhysicalScalarEulerEquation
            period hPeriod massSquared field ↔
          geometric.greenCore.core.operator field = 0) :=
  ⟨geometric.smoothCauchyExtensionData.boundaryTrace_denseRange,
    geometric.greenCore.core.green_identity,
    geometric.eulerEquation_iff_operator_eq_zero⟩

end CanonicalPhysicalScalarGeometricGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
end JanusFormal
