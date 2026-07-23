import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerWaveCompatibilityEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

/-!
# Compatibility bridge for the explicit Cauchy-jet estimate chain

Euler overlap compatibility is equivalent to scalar-wave naturality.  Hence the
compatibility-only explicit Cauchy data can be converted definitionally to the
older `CanonicalPhysicalScalarCauchyJetGeometricData` interface.  All product
coarea, bulk `L²`, Euler-residual and graph-extension estimates can therefore be
reused without duplication.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityBridge4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerWaveCompatibilityEquiv4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0) {massSquared : Real}

namespace CanonicalPhysicalScalarCauchyJetCompatibilityData

/-- Conversion to the original wave-natural explicit-Cauchy interface. -/
def _root_.JanusFormal.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D.CanonicalPhysicalScalarCauchyJetCompatibilityData.toCauchyJetGeometricData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore where
  globalization := data.eulerCompatibility.toWaveGlobalizationData
  boundaryCore := data.boundaryCore
  tubularInverse := data.tubularInverse
  integral_eq_divergence := data.integral_eq_divergence

/-- The two explicit extension maps agree definitionally. -/
theorem extension_eq_geometricExtension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    data.extension period hPeriod =
      (data.toCauchyJetGeometricData period hPeriod).extension period hPeriod := by
  rfl

/-- The compatibility and wave-natural Green cores agree. -/
theorem greenCore_eq_geometricGreenCore
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    data.greenCore period hPeriod =
      (data.toCauchyJetGeometricData period hPeriod).greenCore period hPeriod := by
  rfl

/-- The boundary-core embeddings agree. -/
theorem boundaryCoreEmbedding_eq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D.canonicalScalarBoundaryCorePairEmbedding
      data.boundaryCore.valueEmbedding data.boundaryCore.normalEmbedding =
      canonicalScalarBoundaryCorePairEmbedding
        (data.toCauchyJetGeometricData period hPeriod).boundaryCore.valueEmbedding
        (data.toCauchyJetGeometricData period hPeriod).boundaryCore.normalEmbedding := by
  rfl

/-- Compatibility bridge certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (data : CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared ValueCore NormalCore) :
    data.extension period hPeriod =
        (data.toCauchyJetGeometricData period hPeriod).extension period hPeriod ∧
      data.greenCore period hPeriod =
        (data.toCauchyJetGeometricData period hPeriod).greenCore period hPeriod ∧
      data.eulerCompatibility.toOperatorData =
        (data.toCauchyJetGeometricData period hPeriod).operatorData period hPeriod := by
  exact ⟨rfl, rfl, rfl⟩

end CanonicalPhysicalScalarCauchyJetCompatibilityData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityBridge4D
end JanusFormal
