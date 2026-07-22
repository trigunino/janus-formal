import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D

/-!
# Canonical physical Green core from scalar-wave naturality

The massive Euler residual is `□g φ - m² φ`.  Evaluation of `φ` at a quotient
point is intrinsic, hence the mass term is automatically compatible on chart
overlaps.  The only remaining overlap theorem is naturality of the scalar wave
contraction.

Full support of the physical volume, smooth periodic/antiperiodic boundary
core density, the tubular inverse and the Cauchy extension are already theorems.
Thus the preferred canonical Green-core package now asks only for:

* naturality of `□g` for every smooth physical scalar;
* the global Euler-skew/divergence integral identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveCauchyJetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalInteriorCauchyJetGreenCore4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Preferred canonical Green-core input after reducing overlap compatibility to
scalar-wave naturality. -/
structure CanonicalPhysicalScalarCanonicalWaveCauchyJetData
    (massSquared : Real) where
  waveNaturality : CanonicalPhysicalScalarWaveAtlasNaturality period hPeriod
  integral_eq_divergence :
    ∀ field test : SmoothQuotientField period hPeriod Real,
      (∫ point,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarCanonicalWaveCauchyJetData

/-- Wave naturality generates universal massive Euler compatibility. -/
def eulerCompatibilityOnlyData
    (data : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared where
  compatible := canonicalPhysicalScalarEulerAtlasCompatible_all
    period hPeriod data.waveNaturality massSquared

/-- Conversion to the fully constructed canonical Cauchy-jet Green core. -/
def toCanonicalInteriorCauchyJetData
    (data : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalInteriorCauchyJetData
      period hPeriod massSquared where
  euler := data.eulerCompatibilityOnlyData
  integral_eq_divergence := data.integral_eq_divergence

/-- Canonical compatibility package. -/
def toCanonicalCauchyJetCompatibilityData
    (data : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalInteriorCauchyJetData.toCanonicalCauchyJetCompatibilityData

/-- Genuine faithful physical Euler operator. -/
def operatorData
    (data : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalInteriorCauchyJetData.operatorData

/-- Explicit global smooth Cauchy extension. -/
def extension
    (data : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalInteriorCauchyJetData.extension

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared) :=
  data.toCanonicalInteriorCauchyJetData.greenCore

/-- Canonical wave-based Green-core certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalWaveCauchyJetData
      period hPeriod massSquared) :
    (∀ field : SmoothScalarField period hPeriod,
      CanonicalPhysicalScalarEulerAtlasCompatible
        period hPeriod massSquared field) ∧
      DenseRange
        (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) ∧
      DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) :=
  ⟨canonicalPhysicalScalarEulerAtlasCompatible_all
      period hPeriod data.waveNaturality massSquared,
    data.toCanonicalInteriorCauchyJetData.boundaryDensity.valueDense,
    data.toCanonicalInteriorCauchyJetData.boundaryDensity.normalDense,
    data.toCanonicalCauchyJetCompatibilityData.boundaryTrace_denseRange⟩

end CanonicalPhysicalScalarCanonicalWaveCauchyJetData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalWaveCauchyJetGreenCore4D
end JanusFormal
