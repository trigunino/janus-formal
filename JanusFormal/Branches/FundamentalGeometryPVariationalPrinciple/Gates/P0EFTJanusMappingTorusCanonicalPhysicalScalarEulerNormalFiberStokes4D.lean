import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLocalToCutBulkBridge4D

/-!
# Green's theorem reduced to one normal-fiber identity

The canonical product measure is exactly

`boundaryBaseMeasure × weightedNormalMeasure`.

The canonical local divergence density is integrable by coarea.  Hence Fubini
reduces its total integral to the integral over the boundary base of a
one-dimensional weighted normal integral.

It is therefore enough to prove, for every fixed boundary base,

`∫ normal, localDivergence(base,normal) dμnormal
   = -2 ∫₀¹ cutoffDivergence(base,normal) d normal`.

This file performs all Fubini and scalar-factor bookkeeping and constructs the
full local-to-cut-bulk Green package from that fiberwise statement.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalFiberStokes4D

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

/-- Final one-dimensional Green input, parameterized by the boundary base. -/
structure CanonicalPhysicalScalarEulerNormalFiberStokesData
    (massSquared : Real) where
  waveNaturality :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
      period hPeriod
  normalFiber_identity :
    ∀ field test : SmoothScalarField period hPeriod,
    ∀ base : CanonicalLatitudeBase,
      (∫ normal,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test (base, normal)
        ∂canonicalLatitudeCauchyJetNormalMeasure) =
      -2 *
        ∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal

namespace CanonicalPhysicalScalarEulerNormalFiberStokesData

/-- Fubini form of the canonical local product divergence integral. -/
theorem localDivergence_integral_eq_iterated
    (data : CanonicalPhysicalScalarEulerNormalFiberStokesData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      ∫ base, (∫ normal,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test (base, normal)
        ∂canonicalLatitudeCauchyJetNormalMeasure)
        ∂canonicalLatitudeBaseMeasure period := by
  have hIntegrable :=
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity_integrable
      period hPeriod data.waveNaturality massSquared field test
  unfold canonicalLatitudeCauchyJetProductMeasure at hIntegrable ⊢
  simpa [Function.uncurry] using (integral_integral hIntegrable).symm

/-- Fiberwise Stokes implies the full coordinate comparison with the positive
half collar. -/
theorem localDivergence_eq_halfCollar
    (data : CanonicalPhysicalScalarEulerNormalFiberStokesData
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
  rw [data.localDivergence_integral_eq_iterated field test]
  calc
    (∫ base, (∫ normal,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test (base, normal)
      ∂canonicalLatitudeCauchyJetNormalMeasure)
      ∂canonicalLatitudeBaseMeasure period) =
        ∫ base,
          (-2 : Real) *
            (∫ normal in (0 : Real)..1,
              cutoffCollarScalarCurrentDensitizedDivergence
                period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base =>
        data.normalFiber_identity field test base
    _ = -2 *
        (∫ base, (∫ normal in (0 : Real)..1,
          cutoffCollarScalarCurrentDensitizedDivergence
            period hPeriod massSquared field test base normal)
          ∂canonicalLatitudeBaseMeasure period) := by
      rw [integral_const_mul]

/-- Conversion to the local-to-cut-bulk package. -/
def toLocalToCutBulkData
    (data : CanonicalPhysicalScalarEulerNormalFiberStokesData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerLocalToCutBulkData
      period hPeriod massSquared where
  waveNaturality := data.waveNaturality
  localDivergence_eq_halfCollar := data.localDivergence_eq_halfCollar

/-- Canonical local-divergence Green package. -/
def toCanonicalLocalDivergenceData
    (data : CanonicalPhysicalScalarEulerNormalFiberStokesData
      period hPeriod massSquared) :=
  data.toLocalToCutBulkData.toCanonicalLocalDivergenceData

/-- Correct dense physical Green core. -/
def greenCore
    (data : CanonicalPhysicalScalarEulerNormalFiberStokesData
      period hPeriod massSquared) :=
  data.toCanonicalLocalDivergenceData.greenCore

/-- Fiberwise Green closure certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerNormalFiberStokesData
      period hPeriod massSquared) :
    (∀ field test base,
      (∫ normal,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test (base, normal)
        ∂canonicalLatitudeCauchyJetNormalMeasure) =
        -2 *
          ∫ normal in (0 : Real)..1,
            cutoffCollarScalarCurrentDensitizedDivergence
              period hPeriod massSquared field test base normal) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D.cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨data.normalFiber_identity,
    data.toLocalToCutBulkData.certificate.2⟩

end CanonicalPhysicalScalarEulerNormalFiberStokesData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalFiberStokes4D
end JanusFormal
