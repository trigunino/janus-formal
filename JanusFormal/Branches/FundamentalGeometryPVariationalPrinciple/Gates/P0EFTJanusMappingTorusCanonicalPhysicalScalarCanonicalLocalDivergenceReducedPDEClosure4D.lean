import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLocalToCutBulkBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEClosure4D

/-!
# Reduced physical scalar PDE closure from the local half-collar bridge

The Green identity is now supplied solely by a coordinate comparison between:

* the canonical holonomic local divergence on the full product coarea domain;
* the cutoff densitized divergence on the positive half collar.

All quotient integration, coarea transport, vector-measure pushforward and
boundary-sheet signs are already theorems.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLocalToCutBulkBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCompletedNormalRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

/-- Smallest current physical PDE package with Green's theorem reduced to one
local-to-half-collar integral comparison. -/
structure CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarEulerLocalToCutBulkData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ExactEnergyGardingIdentityData
    period hPeriod
  completedNormalRegularity : geometric.greenCore.CompletedNormalRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    geometric.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod
      geometric.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.canonicalEulerProductRealization

namespace CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData

/-- Conversion to the product-divergence reduced package. -/
def toProductDivergenceReducedPDEData
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalProductDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric.toCanonicalProductDivergenceCauchyJetData
  energyIdentity := data.energyIdentity
  completedNormalRegularity := data.completedNormalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Conversion to the established reduced physical PDE package. -/
def toCanonicalReducedPDEData
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toProductDivergenceReducedPDEData.toCanonicalReducedPDEData

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.triple

/-- Completed boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.completedInputs

/-- Bounded completed Cauchy extension. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.completedExtension

/-- Physical graph-elliptic estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.graphEllipticEstimate

/-- Physical normal graph estimate. -/
def normalGraphEstimate
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toCanonicalReducedPDEData.normalGraphEstimate

/-- Local-divergence reduced boundary certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    (∀ field test,
      (∫ parameter,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D.canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) =
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
  ⟨data.geometric.localDivergence_integral_eq_cutBulk,
    data.toCanonicalReducedPDEData.certificate.2.2.2.1,
    data.toCanonicalReducedPDEData.certificate.2.2.2.2.1,
    data.toCanonicalReducedPDEData.certificate.2.2.2.2.2⟩

end CanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceReducedPDEClosure4D
end JanusFormal
