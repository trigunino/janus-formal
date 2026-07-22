import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCompatibilityGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D

/-!
# Explicit Cauchy-jet Green core from Euler compatibility

The explicit latitude Cauchy extension is independent of the operator
compatibility proof.  This file combines:

* overlap compatibility of the chartwise Euler residual;
* smooth periodic value and antiperiodic normal boundary cores;
* a regular inverse of the non-polar tubular coordinates;
* the global Euler-skew/divergence integral identity.

The tubular inverse constructs the globally smooth extension-by-zero candidate.
Euler compatibility constructs the physical bulk `L²` operator and its
continuity.  Together they install the exact dense physical scalar Green core.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCandidateExtension4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCoverInverseReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCompatibilityGreenCore4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

/-- Explicit physical Green-core data with operator globalization reduced to
Euler overlap compatibility. -/
structure CanonicalPhysicalScalarCauchyJetCompatibilityData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  eulerCompatibility : CanonicalPhysicalScalarEulerCompatibilityData
    period hPeriod massSquared
  boundaryCore : CanonicalPhysicalScalarSmoothCauchyJetBoundaryCoreData
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

namespace CanonicalPhysicalScalarCauchyJetCompatibilityData

/-- Globally smooth explicit Cauchy-jet extension data. -/
def candidateExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarCauchyJetCandidateExtensionData
      period hPeriod ValueCore NormalCore :=
  data.tubularInverse.toCandidateExtensionData data.boundaryCore

/-- Linear smooth physical Cauchy extension. -/
def extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    ValueCore × NormalCore →ₗ[Real]
      SmoothQuotientField period hPeriod Real :=
  data.candidateExtension.extension

/-- Exact physical Cauchy trace of the explicit extension. -/
theorem cauchyTrace_extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore)
    (boundary : ValueCore × NormalCore) :
    smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
        (data.extension boundary) =
      canonicalScalarBoundaryCorePairEmbedding
        data.boundaryCore.valueEmbedding
        data.boundaryCore.normalEmbedding boundary :=
  data.candidateExtension.cauchyTrace_extension boundary

/-- Conversion to the compatibility-based Green-core construction. -/
def toCompatibilityGreenCoreData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarCompatibilityGreenCoreData
      period hPeriod massSquared ValueCore NormalCore where
  eulerCompatibility := data.eulerCompatibility
  valueEmbedding := data.boundaryCore.valueEmbedding
  normalEmbedding := data.boundaryCore.normalEmbedding
  valueDense := data.boundaryCore.valueDense
  normalDense := data.boundaryCore.normalDense
  extension := data.extension
  boundary_extension := data.cauchyTrace_extension
  integral_eq_divergence := data.integral_eq_divergence

/-- Genuine physical Euler operator. -/
def operatorData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :=
  data.toCompatibilityGreenCoreData.operatorData

/-- Correct dense physical scalar Green core. -/
def greenCore
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :=
  data.toCompatibilityGreenCoreData.greenCore

/-- Dense smooth physical Cauchy trace. -/
theorem boundaryTrace_denseRange
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    DenseRange
      (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) :=
  data.toCompatibilityGreenCoreData.smoothCauchyExtensionData
    |>.boundaryTrace_denseRange

/-- Exact physical Green identity. -/
theorem green_identity
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore)
    (field test : SmoothQuotientField period hPeriod Real) :
    inner Real (data.greenCore.core.operator field)
          (data.greenCore.core.inclusion test) -
        inner Real (data.greenCore.core.inclusion field)
          (data.greenCore.core.operator test) =
      2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
        (data.greenCore.core.boundaryTrace field)
        (data.greenCore.core.boundaryTrace test) :=
  data.greenCore.core.green_identity field test

/-- Compatibility-Cauchy Green-core certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    DenseRange
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) ∧
      (∀ boundary : ValueCore × NormalCore,
        smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
            (data.extension boundary) =
          canonicalScalarBoundaryCorePairEmbedding
            data.boundaryCore.valueEmbedding
            data.boundaryCore.normalEmbedding boundary) ∧
      (∀ field test : SmoothQuotientField period hPeriod Real,
        inner Real (data.greenCore.core.operator field)
              (data.greenCore.core.inclusion test) -
            inner Real (data.greenCore.core.inclusion field)
              (data.greenCore.core.operator test) =
          2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
            (data.greenCore.core.boundaryTrace field)
            (data.greenCore.core.boundaryTrace test)) :=
  ⟨data.boundaryTrace_denseRange,
    data.cauchyTrace_extension,
    data.green_identity⟩

end CanonicalPhysicalScalarCauchyJetCompatibilityData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
end JanusFormal
