import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetRieszBoundaryTriple4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D

/-!
# Reduced physical scalar PDE closure through the Riesz boundary trace

The completed Cauchy trace is reconstructed from the Green defect and the
bounded explicit Cauchy extension.  Therefore the former higher regularity
space and completed normal-trace map are absent from this endpoint.

The remaining physical PDE data are:

* one intrinsic global scalar-wave representative;
* one local Green comparison with the positive half collar;
* one exact first-jet energy identity with bounded zeroth-order remainder;
* six bounded tangential coefficient operators for the explicit Cauchy lift.

From these data the code constructs the graph-elliptic estimate, the Riesz
completed trace, its bounded right inverse and the surjective completed boundary
triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetRieszBoundaryTriple4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period

private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Smallest current physical scalar PDE package.  In particular it contains no
normal-trace regularity field. -/
structure CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveLocalGreenData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ExactEnergyGardingIdentityData
    period hPeriod
  eulerCoefficients :
    geometric.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData

/-- Canonical compatibility-based Cauchy-jet data. -/
def compatibilityData
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityGreenCore4D.CanonicalPhysicalScalarCauchyJetCompatibilityData
      period hPeriod massSquared (ValueCore period) (NormalCore period) :=
  data.geometric.toCanonicalLocalDivergenceData period hPeriod
    |>.toCanonicalWaveCauchyJetData period hPeriod
    |>.toCanonicalCauchyJetCompatibilityData period hPeriod
    |>.toCompatibilityData period hPeriod

/-- Explicit geometric Cauchy-jet data. -/
def jetGeometric
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :=
  (data.compatibilityData period hPeriod).toCauchyJetGeometricData period hPeriod

/-- Euler product estimate generated from the six bounded coefficient
operators. -/
def eulerEstimate
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :=
  data.eulerCoefficients.toEulerProductEstimateData period hPeriod

/-- Riesz boundary-triple input generated from the bounded Cauchy extension. -/
def rieszBoundaryData
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCauchyJetRieszBoundaryData
      period hPeriod massSquared (ValueCore period) (NormalCore period) where
  geometric := data.compatibilityData period hPeriod
  eulerEstimate := data.eulerEstimate period hPeriod

/-- Riesz-generated physical graph trace bound. -/
def traceBound
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :=
  (data.rieszBoundaryData period hPeriod).traceBound period hPeriod

/-- Riesz-generated completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :=
  (data.rieszBoundaryData period hPeriod).triple period hPeriod

/-- Completed physical Cauchy trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :=
  (data.rieszBoundaryData period hPeriod).completedBoundaryTrace period hPeriod

/-- Bounded right inverse of the completed physical Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :=
  (data.rieszBoundaryData period hPeriod).completedExtension period hPeriod

/-- Graph-elliptic estimate generated by the exact first-jet energy identity. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :=
  data.energyIdentity.toGraphEllipticEstimate period hPeriod
    (data.geometric.greenCore period hPeriod)

/-- The completed extension is a right inverse of the Riesz trace. -/
theorem completedBoundaryTrace_extension
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared)
    (boundary :
      P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.CanonicalScalarHilbertBoundaryDatum
        (Trace := P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.CanonicalPhysicalScalarFirstSheetL2 period)) :
    data.completedBoundaryTrace period hPeriod
        (data.completedExtension period hPeriod boundary) = boundary :=
  (data.rieszBoundaryData period hPeriod).completedBoundaryTrace_extension
    period hPeriod boundary

/-- Riesz-reduced physical PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (data.geometric.greenCore period hPeriod).MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (data.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective (data.completedBoundaryTrace period hPeriod) ∧
      (∀ boundary,
        data.completedBoundaryTrace period hPeriod
          (data.completedExtension period hPeriod boundary) = boundary) ∧
      (∀ field :
        P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
          period hPeriod Real,
        data.completedBoundaryTrace period hPeriod
            (canonicalScalarGreenCoreToGraph
              (data.geometric.greenCore period hPeriod).core field) =
          (data.geometric.greenCore period hPeriod).core.boundaryTrace field) :=
  ⟨data.geometric.intrinsicWave.toWaveAtlasNaturality,
    (data.rieszBoundaryData period hPeriod).minimalCoreDense period hPeriod,
    (data.rieszBoundaryData period hPeriod).graphInclusion_injective period hPeriod,
    ((data.rieszBoundaryData period hPeriod).boundedSmoothExtension period hPeriod)
      |>.rieszBoundaryTrace_surjective,
    data.completedBoundaryTrace_extension period hPeriod,
    ((data.rieszBoundaryData period hPeriod).boundedSmoothExtension period hPeriod)
      |>.rieszBoundaryTrace_smooth⟩

end CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEClosure4D
end JanusFormal
