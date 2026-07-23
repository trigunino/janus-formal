import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEClosure4D

/-!
# Riesz boundary triple from the intrinsic normal/tangential Green split

This endpoint combines the geometrically natural decomposition of the local
Green divergence with the Riesz reconstruction of the completed boundary trace.

The tangential part is required only to have zero integral over the canonical
boundary base; the normal part carries the cut-boundary flux.  No fiberwise
vanishing assumption and no independent normal trace regularity theorem are
required.

The remaining quantitative PDE inputs are the exact first-jet energy identity
and the six bounded coefficient operators controlling the explicit Cauchy lift.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Smallest current PDE package using the normal/tangential local Green split
and the Riesz completed trace. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialGreenData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ExactEnergyGardingIdentityData
    period hPeriod
  eulerCoefficients :
    geometric.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData

/-- Conversion to the direct intrinsic-wave Riesz package. -/
def toIntrinsicWaveRieszReducedPDEData
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared where
  geometric := data.geometric.toIntrinsicWaveLocalGreenData period hPeriod
  energyIdentity := data.energyIdentity
  eulerCoefficients := data.eulerCoefficients

/-- Riesz-generated completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
      period hPeriod massSquared) :=
  (data.toIntrinsicWaveRieszReducedPDEData period hPeriod).triple period hPeriod

/-- Riesz-generated completed Cauchy trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
      period hPeriod massSquared) :=
  (data.toIntrinsicWaveRieszReducedPDEData period hPeriod).completedBoundaryTrace
    period hPeriod

/-- Bounded right inverse of the completed trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
      period hPeriod massSquared) :=
  (data.toIntrinsicWaveRieszReducedPDEData period hPeriod).completedExtension
    period hPeriod

/-- Physical graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
      period hPeriod massSquared) :=
  (data.toIntrinsicWaveRieszReducedPDEData period hPeriod).graphEllipticEstimate
    period hPeriod

/-- The completed extension is a right inverse of the Riesz trace. -/
theorem completedBoundaryTrace_extension
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
      period hPeriod massSquared)
    (boundary :
      P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.CanonicalScalarHilbertBoundaryDatum
        (Trace := P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.CanonicalPhysicalScalarFirstSheetL2 period)) :
    data.completedBoundaryTrace period hPeriod
        (data.completedExtension period hPeriod boundary) = boundary :=
  (data.toIntrinsicWaveRieszReducedPDEData period hPeriod)
    |>.completedBoundaryTrace_extension period hPeriod boundary

/-- Normal/tangential Riesz boundary certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
      period hPeriod massSquared) :
    (∀ field test,
      (∫ parameter,
        data.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
      (data.geometric.greenCore period hPeriod).MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (data.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective (data.completedBoundaryTrace period hPeriod) ∧
      (∀ boundary,
        data.completedBoundaryTrace period hPeriod
          (data.completedExtension period hPeriod boundary) = boundary) :=
  ⟨(data.geometric.toNormalTangentialSplitData period hPeriod)
      |>.tangential_integral_eq_zero period hPeriod,
    ((data.toIntrinsicWaveRieszReducedPDEData period hPeriod).rieszBoundaryData
      period hPeriod).minimalCoreDense period hPeriod,
    ((data.toIntrinsicWaveRieszReducedPDEData period hPeriod).rieszBoundaryData
      period hPeriod).graphInclusion_injective period hPeriod,
    (((data.toIntrinsicWaveRieszReducedPDEData period hPeriod).rieszBoundaryData
      period hPeriod).boundedSmoothExtension period hPeriod)
      |>.rieszBoundaryTrace_surjective,
    data.completedBoundaryTrace_extension period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEClosure4D
end JanusFormal
