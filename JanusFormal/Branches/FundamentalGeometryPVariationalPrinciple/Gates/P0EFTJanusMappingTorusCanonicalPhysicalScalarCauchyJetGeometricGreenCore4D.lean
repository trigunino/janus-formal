import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D

/-!
# Geometric Green core from the explicit Cauchy-jet extension

The former geometric Green-core package accepted a smooth Cauchy extension as
an independent field.  The explicit latitude construction now supplies that
extension.

The data retained here are:

* globalization of the physical scalar wave operator;
* smooth periodic value representatives and smooth antiperiodic normal
  representatives on the latitude base;
* a regular inverse of the non-polar tubular cover coordinates;
* the Euler-skew/divergence integral identity.

The tubular inverse proves global smoothness of the extension-by-zero candidate.
Its exact first-sheet value and normal jets produce the dense smooth Cauchy
trace.  Combining this extension with the global Green--Stokes identity installs
the corrected physical scalar Green core.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCandidateExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetTubularChartReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

/-- Geometric smooth-core data with the Cauchy extension replaced by its
explicit latitude-jet construction. -/
structure CanonicalPhysicalScalarCauchyJetGeometricData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  globalization : CanonicalPhysicalScalarWaveGlobalizationData
    period hPeriod massSquared
  boundaryCore :
    CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
      period ValueCore NormalCore
  tubularInverse : CanonicalLatitudeTubularCoverInverseRegularityData
    period hPeriod
  integral_eq_divergence :
    ∀ field test : SmoothQuotientField period hPeriod Real,
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Globally smooth explicit Cauchy-jet extension data. -/
def candidateExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarCauchyJetCandidateExtensionData
      period hPeriod ValueCore NormalCore :=
  geometric.tubularInverse.toCandidateExtensionData geometric.boundaryCore

/-- Linear smooth bulk extension realizing every boundary-core pair. -/
def extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    ValueCore × NormalCore →ₗ[Real]
      SmoothQuotientField period hPeriod Real :=
  geometric.candidateExtension.extension

/-- Exact paired Cauchy trace of the explicit extension. -/
theorem cauchyTrace_extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
        (geometric.extension data) =
      canonicalScalarBoundaryCorePairEmbedding
        geometric.boundaryCore.valueEmbedding
        geometric.boundaryCore.normalEmbedding data :=
  geometric.candidateExtension.cauchyTrace_extension data

/-- Conversion to the earlier geometric Green-core package.  The former
abstract smooth extension and boundary-extension equations are now theorems. -/
def toGeometricGreenCoreData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore where
  globalization := geometric.globalization
  valueEmbedding := geometric.boundaryCore.valueEmbedding
  normalEmbedding := geometric.boundaryCore.normalEmbedding
  valueDense := geometric.boundaryCore.valueDense
  normalDense := geometric.boundaryCore.normalDense
  extension := geometric.extension
  boundary_extension := geometric.cauchyTrace_extension
  integral_eq_divergence := geometric.integral_eq_divergence

/-- Genuine physical Euler operator on the smooth scalar core. -/
def operatorData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :=
  geometric.toGeometricGreenCoreData.operatorData

/-- Correct dense physical Green core. -/
def greenCore
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :=
  geometric.toGeometricGreenCoreData.greenCore

/-- The explicit Cauchy extension proves density of the physical smooth boundary
trace. -/
theorem boundaryTrace_denseRange
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    DenseRange
      (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) :=
  geometric.candidateExtension.boundaryTrace_denseRange

/-- Exact bulk Green--Stokes identity for the constructed physical operator. -/
theorem bulk_green_stokes
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
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
  geometric.toGeometricGreenCoreData.bulk_green_stokes field test

/-- Cauchy-jet geometric Green-core certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) :
    DenseRange
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) ∧
      (∀ data : ValueCore × NormalCore,
        smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
            (geometric.extension data) =
          canonicalScalarBoundaryCorePairEmbedding
            geometric.boundaryCore.valueEmbedding
            geometric.boundaryCore.normalEmbedding data) ∧
      (∀ field test : SmoothQuotientField period hPeriod Real,
        inner Real (geometric.greenCore.core.operator field)
              (geometric.greenCore.core.inclusion test) -
            inner Real (geometric.greenCore.core.inclusion field)
              (geometric.greenCore.core.operator test) =
          2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
            (geometric.greenCore.core.boundaryTrace field)
            (geometric.greenCore.core.boundaryTrace test)) :=
  ⟨geometric.boundaryTrace_denseRange,
    geometric.cauchyTrace_extension,
    geometric.greenCore.core.green_identity⟩

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
end JanusFormal
