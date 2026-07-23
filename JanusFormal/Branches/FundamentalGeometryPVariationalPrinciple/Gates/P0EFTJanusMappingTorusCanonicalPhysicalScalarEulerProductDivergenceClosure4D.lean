import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveCauchyJetGreenCore4D

/-!
# Euler--divergence identity in canonical product coordinates

The canonical latitude product map

`(boundary point, normal angle) -> physical point`

preserves the exact physical Lorentz volume.  Therefore the global integral of
the Euler skew density is definitionally reducible to its pullback to the
explicit product measure

`boundary measure × cos²(normal) d normal`.

This file replaces the former quotient-space integral input by a product-space
identity.  A further density-oriented package allows the local PDE proof to
supply:

* one explicit product divergence density;
* an almost-everywhere pointwise identity with the pulled Euler skew density;
* the integral of that density as the canonical cut-bulk divergence measure.

All transport through the quotient and all global integrability are then
automatic consequences of coarea.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveCauchyJetGreenCore4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Pullback of the physical Euler skew density to canonical boundary-normal
product coordinates. -/
def canonicalPhysicalScalarEulerProductSkewDensity
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  canonicalPhysicalScalarEulerSkewDensity
    period hPeriod massSquared field test
      (canonicalLatitudeCauchyJetProductPhysicalMap
        period hPeriod parameter)

/-- Exact transport of the global skew integral to canonical product
coordinates. -/
theorem integral_productSkewDensity_eq_global
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      canonicalPhysicalScalarEulerProductSkewDensity
        period hPeriod massSquared field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      ∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let physicalMap := canonicalLatitudeCauchyJetProductPhysicalMap
    period hPeriod
  let sourceMeasure := canonicalLatitudeCauchyJetProductMeasure period
  let targetMeasure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  have hPreserving : MeasurePreserving physicalMap sourceMeasure targetMeasure :=
    canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving
      period hPeriod
  have hIntegrable := canonicalPhysicalScalarEulerSkewDensity_integrable
    period hPeriod operatorData field test
  have hStrong : AEStronglyMeasurable
      (canonicalPhysicalScalarEulerSkewDensity
        period hPeriod massSquared field test)
      (Measure.map physicalMap sourceMeasure) := by
    rw [hPreserving.map_eq]
    exact hIntegrable.aestronglyMeasurable
  unfold canonicalPhysicalScalarEulerProductSkewDensity
  change (∫ parameter,
      canonicalPhysicalScalarEulerSkewDensity
        period hPeriod massSquared field test (physicalMap parameter)
      ∂sourceMeasure) = _
  calc
    (∫ parameter,
      canonicalPhysicalScalarEulerSkewDensity
        period hPeriod massSquared field test (physicalMap parameter)
      ∂sourceMeasure) =
        ∫ point,
          canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂Measure.map physicalMap sourceMeasure :=
      (MeasureTheory.integral_map
        hPreserving.measurable.aemeasurable hStrong).symm
    _ = _ := by rw [hPreserving.map_eq]

/-- Product-coordinate form of the sole remaining Green-divergence integral. -/
structure CanonicalPhysicalScalarEulerProductDivergenceIntegralData
    (massSquared : Real) where
  operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
    period hPeriod massSquared
  product_integral_eq_divergence :
    ∀ field test : SmoothScalarField period hPeriod,
      (∫ parameter,
        canonicalPhysicalScalarEulerProductSkewDensity
          period hPeriod massSquared field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarEulerProductDivergenceIntegralData

/-- Product-coordinate identity implies the former global quotient identity. -/
def toEulerDivergenceIntegralData
    (data : CanonicalPhysicalScalarEulerProductDivergenceIntegralData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerDivergenceIntegralData
      period hPeriod massSquared where
  operatorData := data.operatorData
  integral_eq_divergence := by
    intro field test
    rw [← integral_productSkewDensity_eq_global
      period hPeriod data.operatorData field test]
    exact data.product_integral_eq_divergence field test

/-- Exact physical Green bridge generated from the product-coordinate theorem. -/
def toBulkEulerDivergenceBridge
    (data : CanonicalPhysicalScalarEulerProductDivergenceIntegralData
      period hPeriod massSquared) :=
  data.toEulerDivergenceIntegralData.toBulkEulerDivergenceBridge

/-- Product-coordinate Green certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerProductDivergenceIntegralData
      period hPeriod massSquared) :
    (∀ field test : SmoothScalarField period hPeriod,
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ) ∧
      (∀ field test : SmoothScalarField period hPeriod,
        inner Real (data.operatorData.toBulkL2LinearMap field)
              (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
                period hPeriod test) -
            inner Real
              (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
                period hPeriod field)
              (data.operatorData.toBulkL2LinearMap test) =
          P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
            period hPeriod field test) :=
  ⟨data.toEulerDivergenceIntegralData.integral_eq_divergence,
    data.toEulerDivergenceIntegralData.pairing_eq_orientedBoundaryCurrent⟩

end CanonicalPhysicalScalarEulerProductDivergenceIntegralData

/-- Density-level product-coordinate input.  The PDE proof may work entirely on
the explicit boundary-normal product. -/
structure CanonicalPhysicalScalarEulerProductDivergenceDensityData
    (massSquared : Real) where
  operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
    period hPeriod massSquared
  divergenceDensity :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod →
        CanonicalLatitudeCauchyJetProductParameter → Real
  divergenceDensity_integrable :
    ∀ field test,
      Integrable (divergenceDensity field test)
        (canonicalLatitudeCauchyJetProductMeasure period)
  skew_eq_divergenceDensity :
    ∀ field test,
      canonicalPhysicalScalarEulerProductSkewDensity
          period hPeriod massSquared field test =ᵐ[
            canonicalLatitudeCauchyJetProductMeasure period]
        divergenceDensity field test
  divergenceDensity_integral_eq_cutBulk :
    ∀ field test,
      (∫ parameter,
        divergenceDensity field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarEulerProductDivergenceDensityData

/-- Density-level input implies the product integral theorem. -/
def toProductDivergenceIntegralData
    (data : CanonicalPhysicalScalarEulerProductDivergenceDensityData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerProductDivergenceIntegralData
      period hPeriod massSquared where
  operatorData := data.operatorData
  product_integral_eq_divergence := by
    intro field test
    rw [integral_congr_ae
      (data.skew_eq_divergenceDensity field test)]
    exact data.divergenceDensity_integral_eq_cutBulk field test

/-- Density-level input implies the global Euler-divergence theorem. -/
def toEulerDivergenceIntegralData
    (data : CanonicalPhysicalScalarEulerProductDivergenceDensityData
      period hPeriod massSquared) :=
  data.toProductDivergenceIntegralData.toEulerDivergenceIntegralData

/-- Density-level closure certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerProductDivergenceDensityData
      period hPeriod massSquared) :
    (∀ field test,
      canonicalPhysicalScalarEulerProductSkewDensity
          period hPeriod massSquared field test =ᵐ[
            canonicalLatitudeCauchyJetProductMeasure period]
        data.divergenceDensity field test) ∧
      (∀ field test,
        (∫ point,
          canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.skew_eq_divergenceDensity,
    data.toEulerDivergenceIntegralData.integral_eq_divergence⟩

end CanonicalPhysicalScalarEulerProductDivergenceDensityData

/-- Preferred canonical Green-core input with the divergence theorem stated in
explicit product coordinates. -/
structure CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
    (massSquared : Real) where
  waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod
  product_integral_eq_divergence :
    ∀ field test : SmoothScalarField period hPeriod,
      (∫ parameter,
        canonicalPhysicalScalarEulerProductSkewDensity
          period hPeriod massSquared field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData

/-- Euler compatibility produced by wave naturality. -/
def eulerCompatibilityOnlyData
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared where
  compatible := canonicalPhysicalScalarEulerAtlasCompatible_all
    period hPeriod data.waveNaturality massSquared

/-- Faithful physical Euler operator before using the divergence theorem. -/
def operatorData
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared :=
  (data.eulerCompatibilityOnlyData.toCanonicalCompatibilityData
    period hPeriod).toOperatorData

/-- Product-coordinate divergence package. -/
def toProductDivergenceIntegralData
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerProductDivergenceIntegralData
      period hPeriod massSquared where
  operatorData := data.operatorData
  product_integral_eq_divergence := data.product_integral_eq_divergence

/-- Conversion to the established wave-natural Green-core endpoint. -/
def toCanonicalWaveCauchyJetData
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  integral_eq_divergence :=
    data.toProductDivergenceIntegralData.toEulerDivergenceIntegralData
      |>.integral_eq_divergence

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalWaveCauchyJetData.greenCore

/-- Product-coordinate canonical Green certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
      period hPeriod massSquared) :
    (∀ field test,
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) :=
  ⟨data.toProductDivergenceIntegralData.toEulerDivergenceIntegralData
      |>.integral_eq_divergence,
    data.toCanonicalWaveCauchyJetData.certificate.2.2.2⟩

end CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D
end JanusFormal
