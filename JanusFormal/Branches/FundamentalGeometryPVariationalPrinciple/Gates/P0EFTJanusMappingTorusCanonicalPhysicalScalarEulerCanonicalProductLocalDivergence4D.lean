import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D

/-!
# Canonical local divergence density in product coarea coordinates

Every physical point already carries a canonical total holonomic
local-diffeomorphism witness.  Apply that witness to the image of each canonical
boundary-normal product parameter and evaluate its chart at coordinate zero.

The existing local Green identity then gives, pointwise,

`EulerSkew(productMap p) = - localGreenDivergence(productPatch p, 0)`.

Thus neither a chart family nor an almost-everywhere density identity needs to
be supplied.  Integrability of the local divergence density is transported from
the global continuous Euler skew density by exact coarea.

The only remaining Green input is the one-dimensional/global Stokes statement
that the integral of this canonical local density is the canonical cut-bulk
divergence measure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter Function
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Canonical local-diffeomorphism witness at one product-coordinate physical
point. -/
noncomputable def canonicalPhysicalScalarEulerProductWitness
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    CanonicalPhysicalScalarEulerLocalDiffeomorphWitness
      period hPeriod
      (canonicalLatitudeCauchyJetProductPhysicalMap
        period hPeriod parameter) :=
  canonicalPhysicalScalarEulerLocalDiffeomorphWitness
    period hPeriod
    (canonicalLatitudeCauchyJetProductPhysicalMap
      period hPeriod parameter)

/-- Canonical holonomic patch at one product parameter. -/
noncomputable def canonicalPhysicalScalarEulerProductPatch
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    SmoothHolonomicFrameChart4 period hPeriod :=
  (canonicalPhysicalScalarEulerProductWitness
    period hPeriod parameter).patch

/-- Coordinate zero of the canonical product patch represents the physical
product point. -/
theorem canonicalPhysicalScalarEulerProductPatch_zero
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    (canonicalPhysicalScalarEulerProductPatch period hPeriod parameter)
        |>.coordinateMap 0 =
      canonicalLatitudeCauchyJetProductPhysicalMap
        period hPeriod parameter := by
  exact (canonicalPhysicalScalarEulerProductWitness
    period hPeriod parameter).at_zero

/-- Canonical local Green-divergence density on product coarea coordinates. -/
def canonicalPhysicalScalarEulerProductLocalDivergenceDensity
    (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) : Real :=
  -localSmoothScalarGreenDivergence period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    (canonicalPhysicalScalarEulerProductPatch period hPeriod parameter)
    field test 0

/-- Wave naturality supplies the faithful global Euler operator used by the
canonical local identity. -/
def canonicalPhysicalScalarEulerProductOperatorData
    (waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod)
    (massSquared : Real) :
    CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared :=
  ((CanonicalPhysicalScalarEulerCompatibilityOnlyData.toCanonicalCompatibilityData
    period hPeriod
    { compatible := canonicalPhysicalScalarEulerAtlasCompatible_all
        period hPeriod waveNaturality massSquared })).toOperatorData

/-- The pulled global Euler skew density is pointwise equal to the canonical
local Green divergence density. -/
theorem canonicalPhysicalScalarEulerProductSkewDensity_eq_localDivergence
    (waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod)
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    canonicalPhysicalScalarEulerProductSkewDensity
        period hPeriod massSquared field test parameter =
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter := by
  have hLocal := canonicalPhysicalScalarEulerSkewDensity_eq_neg_localDivergence
    period hPeriod
    (canonicalPhysicalScalarEulerProductOperatorData
      period hPeriod waveNaturality massSquared)
    field test
    (canonicalPhysicalScalarEulerProductPatch period hPeriod parameter)
    (0 : Vector4)
  rw [canonicalPhysicalScalarEulerProductPatch_zero
    period hPeriod parameter] at hLocal
  simpa [canonicalPhysicalScalarEulerProductSkewDensity,
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity] using hLocal

/-- The product Euler skew density is integrable by exact coarea. -/
theorem canonicalPhysicalScalarEulerProductSkewDensity_integrable
    (waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod)
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod) :
    Integrable
      (canonicalPhysicalScalarEulerProductSkewDensity
        period hPeriod massSquared field test)
      (canonicalLatitudeCauchyJetProductMeasure period) := by
  let operatorData := canonicalPhysicalScalarEulerProductOperatorData
    period hPeriod waveNaturality massSquared
  have hGlobal := canonicalPhysicalScalarEulerSkewDensity_integrable
    period hPeriod operatorData field test
  have hPullback :=
    (canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving
      period hPeriod).integrable_comp_of_integrable hGlobal
  simpa [canonicalPhysicalScalarEulerProductSkewDensity,
    Function.comp_def] using hPullback

/-- Integrability of the canonical local Green-divergence density is automatic. -/
theorem canonicalPhysicalScalarEulerProductLocalDivergenceDensity_integrable
    (waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod)
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod) :
    Integrable
      (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test)
      (canonicalLatitudeCauchyJetProductMeasure period) :=
  (canonicalPhysicalScalarEulerProductSkewDensity_integrable
    period hPeriod waveNaturality massSquared field test).congr
      (Filter.Eventually.of_forall fun parameter =>
        canonicalPhysicalScalarEulerProductSkewDensity_eq_localDivergence
          period hPeriod waveNaturality massSquared field test parameter)

/-- Final canonical local-divergence Green input. -/
structure CanonicalPhysicalScalarCanonicalLocalDivergenceData
    (massSquared : Real) where
  waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod
  localDivergence_integral_eq_cutBulk :
    ∀ field test : SmoothScalarField period hPeriod,
      (∫ parameter,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarCanonicalLocalDivergenceData

/-- Density-level product Green package; pointwise identity and integrability are
filled by theorem. -/
def toProductDivergenceDensityData
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerProductDivergenceDensityData
      period hPeriod massSquared where
  operatorData := canonicalPhysicalScalarEulerProductOperatorData
    period hPeriod data.waveNaturality massSquared
  divergenceDensity := fun field test =>
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity
      period hPeriod field test
  divergenceDensity_integrable :=
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity_integrable
      period hPeriod data.waveNaturality massSquared
  skew_eq_divergenceDensity := by
    intro field test
    exact Filter.Eventually.of_forall fun parameter =>
      canonicalPhysicalScalarEulerProductSkewDensity_eq_localDivergence
        period hPeriod data.waveNaturality massSquared field test parameter
  divergenceDensity_integral_eq_cutBulk :=
    data.localDivergence_integral_eq_cutBulk

/-- Product-coordinate Green-core package. -/
def toCanonicalProductDivergenceCauchyJetData
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalProductDivergenceCauchyJetData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  product_integral_eq_divergence :=
    data.toProductDivergenceDensityData.toProductDivergenceIntegralData
      |>.product_integral_eq_divergence

/-- Established wave-natural Green-core package. -/
def toCanonicalWaveCauchyJetData
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared) :=
  data.toCanonicalProductDivergenceCauchyJetData.toCanonicalWaveCauchyJetData

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared) :=
  data.toCanonicalWaveCauchyJetData.greenCore

/-- Canonical local-divergence closure certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared) :
    (∀ field test parameter,
      canonicalPhysicalScalarEulerProductSkewDensity
          period hPeriod massSquared field test parameter =
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter) ∧
      (∀ field test,
        Integrable
          (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test)
          (canonicalLatitudeCauchyJetProductMeasure period)) ∧
      (∀ field test,
        (∫ point,
          canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨canonicalPhysicalScalarEulerProductSkewDensity_eq_localDivergence
      period hPeriod data.waveNaturality massSquared,
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity_integrable
      period hPeriod data.waveNaturality massSquared,
    data.toProductDivergenceDensityData.toEulerDivergenceIntegralData
      |>.integral_eq_divergence⟩

end CanonicalPhysicalScalarCanonicalLocalDivergenceData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
end JanusFormal
