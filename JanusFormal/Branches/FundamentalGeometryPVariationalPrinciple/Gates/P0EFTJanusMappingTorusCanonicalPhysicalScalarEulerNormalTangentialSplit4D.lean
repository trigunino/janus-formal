import Mathlib.MeasureTheory.Integral.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLocalToCutBulkBridge4D

/-!
# Normal/tangential split of the canonical Euler divergence

A holonomic divergence in canonical product coordinates naturally decomposes
into:

* a normal derivative, responsible for the cut-boundary flux;
* a tangential divergence on `S² ×` time, whose base integral vanishes.

The stronger fiberwise Stokes interface is not required when tangential terms
are present.  This file provides the geometrically natural reduction: pointwise
normal/tangential decomposition, tangential base cancellation at each normal
coordinate, and one normal total-integral comparison with the positive cutoff
collar.

Fubini then proves the full local-divergence/half-collar identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalTangentialSplit4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLocalToCutBulkBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Normal/tangential decomposition data for the canonical local divergence. -/
structure CanonicalPhysicalScalarEulerNormalTangentialSplitData
    (massSquared : Real) where
  waveNaturality :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod
  normalDensity :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod →
        CanonicalLatitudeCauchyJetProductParameter → Real
  tangentialDensity :
    SmoothScalarField period hPeriod →
      SmoothScalarField period hPeriod →
        CanonicalLatitudeCauchyJetProductParameter → Real
  normalDensity_integrable : ∀ field test,
    Integrable (normalDensity field test)
      (canonicalLatitudeCauchyJetProductMeasure period)
  tangentialDensity_integrable : ∀ field test,
    Integrable (tangentialDensity field test)
      (canonicalLatitudeCauchyJetProductMeasure period)
  localDivergence_eq_normal_add_tangential :
    ∀ field test parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter =
        normalDensity field test parameter +
          tangentialDensity field test parameter
  tangential_base_integral_zero :
    ∀ field test normal,
      (∫ base,
        tangentialDensity field test (base, normal)
        ∂canonicalLatitudeBaseMeasure period) = 0
  normal_integral_eq_halfCollar :
    ∀ field test,
      (∫ parameter,
        normalDensity field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 *
        (∫ base, (∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period)

namespace CanonicalPhysicalScalarEulerNormalTangentialSplitData

/-- The tangential divergence has zero total integral. -/
theorem tangential_integral_eq_zero
    (data : CanonicalPhysicalScalarEulerNormalTangentialSplitData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      data.tangentialDensity field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) = 0 := by
  have hIntegrable := data.tangentialDensity_integrable field test
  unfold canonicalLatitudeCauchyJetProductMeasure at hIntegrable ⊢
  rw [integral_prod_symm _ hIntegrable]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun normal =>
    data.tangential_base_integral_zero field test normal

/-- The normal/tangential split implies the complete local-to-half-collar
comparison. -/
theorem localDivergence_eq_halfCollar
    (data : CanonicalPhysicalScalarEulerNormalTangentialSplitData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 *
        (∫ base, (∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period) := by
  have hNormal := data.normalDensity_integrable field test
  have hTangential := data.tangentialDensity_integrable field test
  calc
    (∫ parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
        ∫ parameter,
          (data.normalDensity field test parameter +
            data.tangentialDensity field test parameter)
          ∂canonicalLatitudeCauchyJetProductMeasure period := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun parameter =>
        data.localDivergence_eq_normal_add_tangential
          field test parameter
    _ =
        (∫ parameter,
          data.normalDensity field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) +
        ∫ parameter,
          data.tangentialDensity field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period :=
      integral_add hNormal hTangential
    _ =
        (∫ parameter,
          data.normalDensity field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) := by
      rw [data.tangential_integral_eq_zero field test, add_zero]
    _ = _ := data.normal_integral_eq_halfCollar field test

/-- Conversion to the established local-to-cut-bulk package. -/
def toLocalToCutBulkData
    (data : CanonicalPhysicalScalarEulerNormalTangentialSplitData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerLocalToCutBulkData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  localDivergence_eq_halfCollar := data.localDivergence_eq_halfCollar

/-- Canonical local-divergence Green package. -/
def toCanonicalLocalDivergenceData
    (data : CanonicalPhysicalScalarEulerNormalTangentialSplitData
      period hPeriod massSquared) :=
  data.toLocalToCutBulkData.toCanonicalLocalDivergenceData

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarEulerNormalTangentialSplitData
      period hPeriod massSquared) :=
  data.toCanonicalLocalDivergenceData.greenCore

/-- Normal/tangential split certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerNormalTangentialSplitData
      period hPeriod massSquared) :
    (∀ field test,
      (∫ parameter,
        data.tangentialDensity field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) = 0) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.tangential_integral_eq_zero,
    data.toLocalToCutBulkData.certificate.2⟩

end CanonicalPhysicalScalarEulerNormalTangentialSplitData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalTangentialSplit4D
end JanusFormal
