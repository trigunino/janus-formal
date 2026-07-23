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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Smallest current completed-boundary PDE data. -/
structure CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
    period hPeriod massSquared
  energyIdentity : (geometric.greenCore period hPeriod).ScalarRemainderEnergyIdentityData
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
  geometric := data.geometric.toNormalTangentialGreenData period hPeriod
  energyIdentity := data.energyIdentity
  eulerCoefficients := data.eulerCoefficients

/-- Riesz-generated completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  (data.toNormalTangentialRieszScalarEnergyPDEData period hPeriod).triple
    period hPeriod

/-- Completed Riesz trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  (data.toNormalTangentialRieszScalarEnergyPDEData period hPeriod).completedBoundaryTrace
    period hPeriod

/-- Bounded right inverse of the completed Riesz trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  (data.toNormalTangentialRieszScalarEnergyPDEData period hPeriod).completedExtension
    period hPeriod

/-- Physical graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :=
  data.energyIdentity.toGraphEllipticEstimate period hPeriod
    (data.geometric.greenCore period hPeriod)

/-- Completed extension is a right inverse. -/
theorem completedBoundaryTrace_extension
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared)
    (boundary :
      P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.CanonicalScalarHilbertBoundaryDatum
        (Trace := P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.CanonicalPhysicalScalarFirstSheetL2 period)) :
    data.completedBoundaryTrace period hPeriod
        (data.completedExtension period hPeriod boundary) = boundary :=
  (data.toNormalTangentialRieszScalarEnergyPDEData period hPeriod)
    |>.completedBoundaryTrace_extension period hPeriod boundary

/-- Smallest physical PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ field test,
        (∫ parameter,
          data.geometric.tangentialDensity period hPeriod field test parameter
          ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
            period) = 0) ∧
      (∀ field :
        P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
          period hPeriod Real,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D.canonicalPhysicalScalarFirstJetComponentEnergy
            period hPeriod field =
          data.energyIdentity.pairingSign *
              inner Real ((data.geometric.greenCore period hPeriod).core.operator field)
                ((data.geometric.greenCore period hPeriod).core.inclusion field) +
            data.energyIdentity.zerothCoefficient *
              ‖(data.geometric.greenCore period hPeriod).core.inclusion field‖ ^ 2) ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (data.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective (data.completedBoundaryTrace period hPeriod) ∧
      (∀ boundary,
        data.completedBoundaryTrace period hPeriod
          (data.completedExtension period hPeriod boundary) = boundary) :=
  ⟨data.geometric.intrinsicWave.toWaveAtlasNaturality period hPeriod,
    ((data.toNormalTangentialRieszScalarEnergyPDEData period hPeriod).certificate
      period hPeriod).1,
    data.energyIdentity.energy_identity,
    ((data.toNormalTangentialRieszScalarEnergyPDEData period hPeriod).certificate
      period hPeriod).2.2.1,
    ((data.toNormalTangentialRieszScalarEnergyPDEData period hPeriod).certificate
      period hPeriod).2.2.2.1,
    data.completedBoundaryTrace_extension period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyPDEClosure4D
end JanusFormal
