import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEClosure4D

/-!
# Smallest current physical scalar PDE package

The tangential Green divergence is defined as the local divergence minus one
chosen normal component.  The lower-order energy is one scalar coefficient, and
the completed trace is reconstructed by Riesz duality.

The remaining PDE inputs are therefore:

* one intrinsic global scalar-wave representative;
* one integrable normal Green density;
* cancellation of its induced tangential remainder after base integration;
* the normal integral/half-collar comparison;
* one scalar first-jet energy identity;
* six bounded coefficient operators for the explicit Cauchy lift.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Smallest current completed-boundary PDE data. -/
structure CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ScalarRemainderEnergyIdentityData
    period hPeriod
  eulerCoefficients :
    geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData

/-- Conversion to the established normal/tangential scalar-energy package. -/
def toNormalTangentialRieszScalarEnergyPDEData
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEData
      period hPeriod massSquared where
  geometric := data.geometric.toNormalTangentialGreenData
  energyIdentity := data.energyIdentity
  eulerCoefficients := data.eulerCoefficients

/-- Riesz-generated completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  data.toNormalTangentialRieszScalarEnergyPDEData.triple

/-- Completed Riesz trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  data.toNormalTangentialRieszScalarEnergyPDEData.completedBoundaryTrace

/-- Bounded right inverse of the completed Riesz trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  data.toNormalTangentialRieszScalarEnergyPDEData.completedExtension

/-- Physical graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  data.energyIdentity.toGraphEllipticEstimate data.geometric.greenCore

/-- Completed extension is a right inverse. -/
theorem completedBoundaryTrace_extension
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared)
    (boundary :
      P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.CanonicalScalarHilbertBoundaryDatum
        (Trace := P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.CanonicalPhysicalScalarFirstSheetL2 period)) :
    data.completedBoundaryTrace (data.completedExtension boundary) = boundary :=
  data.toNormalTangentialRieszScalarEnergyPDEData
    |>.completedBoundaryTrace_extension boundary

/-- Smallest physical PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ field test,
        (∫ parameter,
          data.geometric.tangentialDensity field test parameter
          ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
            period) = 0) ∧
      (∀ field :
        P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
          period hPeriod Real,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D.canonicalPhysicalScalarFirstJetComponentEnergy
            period hPeriod field =
          data.energyIdentity.pairingSign *
              inner Real (data.geometric.greenCore.core.operator field)
                (data.geometric.greenCore.core.inclusion field) +
            data.energyIdentity.zerothCoefficient *
              ‖data.geometric.greenCore.core.inclusion field‖ ^ 2) ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          data.geometric.greenCore.core) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      (∀ boundary,
        data.completedBoundaryTrace
          (data.completedExtension boundary) = boundary) :=
  ⟨data.geometric.intrinsicWave.toWaveAtlasNaturality,
    data.geometric.toCanonicalNormalSplitData.toNormalTangentialSplitData
      |>.tangential_integral_eq_zero,
    data.energyIdentity.energy_identity,
    data.toNormalTangentialRieszScalarEnergyPDEData.toNormalTangentialRieszPDEData.rieszBoundaryData
      |>.graphInclusion_injective,
    data.toNormalTangentialRieszScalarEnergyPDEData.toNormalTangentialRieszPDEData.rieszBoundaryData
      |>.boundedSmoothExtension.rieszBoundaryTrace_surjective,
    data.completedBoundaryTrace_extension⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEClosure4D
end JanusFormal
