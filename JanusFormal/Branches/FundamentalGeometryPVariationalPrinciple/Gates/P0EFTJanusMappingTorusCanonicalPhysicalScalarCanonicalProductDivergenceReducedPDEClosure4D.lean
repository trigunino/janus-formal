import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D

/-!
# Reduced physical scalar PDE closure from product divergence data

The global quotient-space Euler--divergence integral is no longer part of this
endpoint.  It is generated from the canonical product-coordinate coarea theorem
and one product divergence identity.

The remaining boundary-theory inputs are:

* scalar-wave naturality;
* the product-coordinate Euler-skew/divergence identity;
* one exact first-jet energy identity;
* one bounded completed-graph normal-regularity map;
* six bounded tangential coefficient operators for the Cauchy lift.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCompletedNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Reduced PDE data with Green's identity stated in explicit product
coordinates. -/
structure CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ExactEnergyGardingIdentityData
    period hPeriod
  completedNormalRegularity : geometric.greenCore.CompletedNormalRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    geometric.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData

/-- Conversion to the established reduced PDE package. -/
def toCanonicalReducedPDEData
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalReducedPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric.toCanonicalWaveCauchyJetData
  energyIdentity := data.energyIdentity
  completedNormalRegularity := data.completedNormalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.triple

/-- Completed boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.completedInputs

/-- Bounded right inverse of the completed Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.completedExtension

/-- Physical graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.graphEllipticEstimate

/-- Physical normal graph estimate. -/
def normalGraphEstimate
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.normalGraphEstimate

/-- Product-divergence reduced PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    (∀ field test,
      (∫ point,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      -2 * P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ) ∧
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
  ⟨data.geometric.toProductDivergenceIntegralData.toEulerDivergenceIntegralData
      |>.integral_eq_divergence,
    data.toCanonicalReducedPDEData.certificate.2.2.2.1,
    data.toCanonicalReducedPDEData.certificate.2.2.2.2.1,
    data.toCanonicalReducedPDEData.certificate.2.2.2.2.2⟩

end CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEClosure4D
end JanusFormal
