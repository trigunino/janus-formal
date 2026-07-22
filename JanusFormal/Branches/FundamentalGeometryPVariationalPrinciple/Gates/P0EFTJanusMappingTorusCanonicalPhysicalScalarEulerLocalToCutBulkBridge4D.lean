import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

/-!
# From the canonical local divergence to the positive cut-bulk collar

The vector-measure construction already proves that the total canonical
cut-bulk divergence is the iterated integral over the positive half collar
`0 ≤ normal ≤ 1`.

Consequently the remaining global Green theorem does not need to mention vector
measures or the exact cut-bulk manifold.  It is enough to prove the explicit
coordinate comparison

`∫ productLocalDivergence = -2 ∫ boundary ∫₀¹ cutoffDivergence`.

The theorem in this file then inserts the established pushforward identity and
constructs the full canonical local-divergence Green package.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLocalToCutBulkBridge4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Final coordinate-comparison input for Green's theorem. -/
structure CanonicalPhysicalScalarEulerLocalToCutBulkData
    (massSquared : Real) where
  waveNaturality :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod
  localDivergence_eq_halfCollar :
    ∀ field test : SmoothScalarField period hPeriod,
      (∫ parameter,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 *
        (∫ base, (∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period)

namespace CanonicalPhysicalScalarEulerLocalToCutBulkData

/-- The coordinate comparison implies the exact cut-bulk divergence identity. -/
theorem localDivergence_integral_eq_cutBulk
    (data : CanonicalPhysicalScalarEulerLocalToCutBulkData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ := by
  rw [data.localDivergence_eq_halfCollar field test]
  rw [cutBulkCanonicalDivergenceMeasure_univ
    period hPeriod massSquared field test]

/-- Conversion to the canonical local-divergence Green package. -/
def toCanonicalLocalDivergenceData
    (data : CanonicalPhysicalScalarEulerLocalToCutBulkData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  localDivergence_integral_eq_cutBulk :=
    data.localDivergence_integral_eq_cutBulk

/-- Conversion to the canonical product-divergence Green package. -/
def toCanonicalProductDivergenceCauchyJetData
    (data : CanonicalPhysicalScalarEulerLocalToCutBulkData
      period hPeriod massSquared) :=
  data.toCanonicalLocalDivergenceData
    |>.toCanonicalProductDivergenceCauchyJetData

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarEulerLocalToCutBulkData
      period hPeriod massSquared) :=
  data.toCanonicalLocalDivergenceData.greenCore

/-- Half-collar reduction certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerLocalToCutBulkData
      period hPeriod massSquared) :
    (∀ field test,
      (∫ parameter,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.localDivergence_integral_eq_cutBulk,
    data.toCanonicalLocalDivergenceData.certificate.2.2⟩

end CanonicalPhysicalScalarEulerLocalToCutBulkData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLocalToCutBulkBridge4D
end JanusFormal
