import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEClosure4D

/-!
# Reduced physical scalar PDE closure from intrinsic wave and local Green data

This endpoint contains no pairwise atlas-compatibility proposition and no global
quotient integral theorem.  The geometric operator is specified by a global
intrinsic scalar-wave representative, while Green's theorem is specified by the
canonical local-divergence/positive-half-collar comparison.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCompletedNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Reduced PDE data based on an intrinsic wave and direct local Green bridge. -/
structure CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveLocalGreenData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ExactEnergyGardingIdentityData
    period hPeriod
  completedNormalRegularity : geometric.greenCore.CompletedNormalRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    geometric.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData

/-- Conversion to the local-divergence reduced PDE package. -/
def toCanonicalLocalDivergenceReducedPDEData
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric.toLocalToCutBulkData
  energyIdentity := data.energyIdentity
  completedNormalRegularity := data.completedNormalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Conversion to the established reduced PDE package. -/
def toCanonicalReducedPDEData
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalLocalDivergenceReducedPDEData.toCanonicalReducedPDEData

/-- Correct completed boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.triple

/-- Completed boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.completedInputs

/-- Bounded completed Cauchy extension. -/
def completedExtension
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.completedExtension

/-- Graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.graphEllipticEstimate

/-- Normal graph estimate. -/
def normalGraphEstimate
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.normalGraphEstimate

/-- Intrinsic-wave local PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          data.geometric.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          data.geometric.greenCore.core
          (data.completedInputs.traceBound data.geometric.greenCore)) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            data.geometric.greenCore.core
            (data.completedInputs.traceBound data.geometric.greenCore)
            (data.completedExtension boundary) = boundary) :=
  ⟨data.geometric.intrinsicWave.toWaveAtlasNaturality,
    data.toCanonicalReducedPDEData.certificate.2.2.2.1,
    data.toCanonicalReducedPDEData.certificate.2.2.2.2.1,
    data.toCanonicalReducedPDEData.certificate.2.2.2.2.2⟩

end CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData

/-- Reduced PDE data using the normal/tangential Green split. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialReducedPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialGreenData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ExactEnergyGardingIdentityData
    period hPeriod
  completedNormalRegularity : geometric.greenCore.CompletedNormalRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    geometric.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialReducedPDEData

/-- Conversion to the direct local Green PDE package. -/
def toIntrinsicWaveLocalReducedPDEData
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric.toIntrinsicWaveLocalGreenData
  energyIdentity := data.energyIdentity
  completedNormalRegularity := data.completedNormalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Correct completed boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toIntrinsicWaveLocalReducedPDEData.triple

/-- Normal/tangential reduced PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    (∀ field test,
      (∫ parameter,
        data.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          data.geometric.greenCore.core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          data.geometric.greenCore.core
          (data.toIntrinsicWaveLocalReducedPDEData.completedInputs.traceBound
            data.geometric.greenCore)) :=
  ⟨data.geometric.toNormalTangentialSplitData.tangential_integral_eq_zero,
    data.toIntrinsicWaveLocalReducedPDEData.certificate.2.1,
    data.toIntrinsicWaveLocalReducedPDEData.certificate.2.2.1⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialReducedPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalReducedPDEClosure4D
end JanusFormal
