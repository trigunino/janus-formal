import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D

/-!
# Physical scalar Green core from Euler overlap compatibility

Linearity of the physical Euler residual and continuity of its global
representative are already theorems.  Consequently the operator part of the
smooth Green core only needs overlap compatibility of the chartwise residual.

Together with a dense smooth Cauchy extension and the global
Euler-skew/divergence integral identity, this compatibility constructs the
physical bulk `L²` operator and the exact Green identity.  No separately supplied
wave-globalization or continuity field remains.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCompatibilityGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Green-core data with Euler globalization reduced to chart-overlap
compatibility. -/
structure CanonicalPhysicalScalarCompatibilityGreenCoreData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  eulerCompatibility : CanonicalPhysicalScalarEulerCompatibilityData
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

namespace CanonicalPhysicalScalarCompatibilityGreenCoreData

/-- Genuine physical Euler operator data. -/
def operatorData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (greenData : CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :=
  greenData.eulerCompatibility.toOperatorData

/-- Euler/divergence integral package. -/
def divergenceIntegralData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (greenData : CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarEulerDivergenceIntegralData
      period hPeriod massSquared where
  operatorData := greenData.operatorData
  integral_eq_divergence := greenData.integral_eq_divergence

/-- Exact physical bulk Green--Stokes identity. -/
theorem bulk_green_stokes
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (greenData : CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real (greenData.operatorData.toBulkL2LinearMap field)
          (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
            period hPeriod test) -
        inner Real
          (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
            period hPeriod field)
          (greenData.operatorData.toBulkL2LinearMap test) =
      P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod field test :=
  greenData.divergenceIntegralData.pairing_eq_orientedBoundaryCurrent
    period hPeriod field test

/-- Smooth Cauchy-extension package. -/
def smoothCauchyExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (greenData : CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarSmoothCauchyExtensionData
      period hPeriod massSquared ValueCore NormalCore where
  operatorData := greenData.operatorData
  valueEmbedding := greenData.valueEmbedding
  normalEmbedding := greenData.normalEmbedding
  valueDense := greenData.valueDense
  normalDense := greenData.normalDense
  extension := greenData.extension
  boundary_extension := greenData.boundary_extension
  bulk_green_stokes := greenData.bulk_green_stokes

/-- Correct dense physical scalar Green core. -/
def greenCore
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (greenData : CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared :=
  greenData.smoothCauchyExtensionData.greenCoreData

/-- The physical Euler equation is exactly zero of the constructed operator. -/
theorem eulerEquation_iff_operator_eq_zero
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (greenData : CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalPhysicalScalarEulerEquation period hPeriod massSquared field ↔
      greenData.greenCore.core.operator field = 0 :=
  greenData.greenCore.eulerEquation_iff_operator_eq_zero period hPeriod field

/-- Compatibility-based Green-core certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (greenData : CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      Continuous
        (canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared field)) ∧
      DenseRange
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      (∀ field test : SmoothQuotientField period hPeriod Real,
        inner Real (greenData.greenCore.core.operator field)
              (greenData.greenCore.core.inclusion test) -
            inner Real (greenData.greenCore.core.inclusion field)
              (greenData.greenCore.core.operator test) =
          2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
            (greenData.greenCore.core.boundaryTrace field)
            (greenData.greenCore.core.boundaryTrace test)) :=
  ⟨fun field =>
      canonicalPhysicalScalarEulerGlobalResidual_continuous_of_compatible
        period hPeriod massSquared field
        (greenData.eulerCompatibility.compatible field),
    greenData.smoothCauchyExtensionData.boundaryTrace_denseRange,
    greenData.greenCore.core.green_identity⟩

end CanonicalPhysicalScalarCompatibilityGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCompatibilityGreenCore4D
end JanusFormal
