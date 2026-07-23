import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalHalfCollarTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

/-!
# Intrinsic Green data from the canonical local-divergence identity

The factor-two transport and all integrability statements are constructive.
The sole remaining Stokes input is stated directly as the integral identity
between the canonical local divergence and the cut-bulk divergence measure.
The weighted global cancellation is then derived.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal Interval
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerNormalHalfCollarTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D
open P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D
open P0EFTJanusMappingTorusCutBulkGlobalGreenStokes4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Intrinsic wave plus the genuine global Green--Stokes statement.  The
cut-bulk theorem already fixes the two-sheet orientation and factor two. -/
structure CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
    (massSquared : Real) where
  intrinsicWave : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod
  eulerSkew_integral_eq_orientedBoundary :
    ∀ field test : SmoothScalarField period hPeriod,
      (∫ point,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod field test

/-- Intrinsic wave plus the sole remaining canonical Stokes identity. -/
structure CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
    (massSquared : Real) where
  intrinsicWave : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod
  localDivergence_integral_eq_cutBulk :
    ∀ field test : SmoothScalarField period hPeriod,
      (∫ parameter,
        canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData

/-- Build the intrinsic/global Green package directly from the finite rebased
transition-jet obligation and the genuine global Stokes theorem. -/
def ofRebasedWaveTransition
    (transition :
      CanonicalPhysicalScalarRebasedWaveTransitionData period hPeriod)
    (eulerSkew_integral_eq_orientedBoundary :
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test) :
    CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared where
  intrinsicWave :=
    CanonicalPhysicalScalarIntrinsicWaveData.ofRebasedWaveTransition
      period hPeriod transition
  eulerSkew_integral_eq_orientedBoundary :=
    eulerSkew_integral_eq_orientedBoundary

/-- Build the same global Green package from genuine covariant Hessian
transitions; metric transformation is derived automatically. -/
def ofCovariantWaveTransition
    (transition :
      CanonicalPhysicalScalarCovariantWaveTransitionData period hPeriod)
    (eulerSkew_integral_eq_orientedBoundary :
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test) :
    CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared where
  intrinsicWave :=
    CanonicalPhysicalScalarIntrinsicWaveData.ofCovariantWaveTransition
      period hPeriod transition
  eulerSkew_integral_eq_orientedBoundary :=
    eulerSkew_integral_eq_orientedBoundary

/-- Field-independent Levi--Civita naturality is enough to construct the
intrinsic/global Green package. -/
def ofLeviCivitaTransition
    (transition :
      CanonicalPhysicalScalarLeviCivitaTransitionData period hPeriod)
    (eulerSkew_integral_eq_orientedBoundary :
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test) :
    CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared where
  intrinsicWave :=
    CanonicalPhysicalScalarIntrinsicWaveData.ofLeviCivitaTransition
      period hPeriod transition
  eulerSkew_integral_eq_orientedBoundary :=
    eulerSkew_integral_eq_orientedBoundary

/-- Build the global Green package from the canonical Levi--Civita
naturality theorem.  Only the genuine global Stokes identity remains. -/
def ofCanonicalIntrinsicWave
    (eulerSkew_integral_eq_orientedBoundary :
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test) :
    CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared where
  intrinsicWave :=
    CanonicalPhysicalScalarIntrinsicWaveData.canonical period hPeriod
  eulerSkew_integral_eq_orientedBoundary :=
    eulerSkew_integral_eq_orientedBoundary

/-- Since intrinsic wave naturality is canonical, inhabiting the global Green
package is exactly the genuine global Stokes identity. -/
theorem nonempty_iff_eulerSkew_integral_eq_orientedBoundary :
    Nonempty
        (CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
          period hPeriod massSquared) ↔
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod field test := by
  constructor
  · rintro ⟨data⟩
    exact data.eulerSkew_integral_eq_orientedBoundary
  · intro hStokes
    exact ⟨ofCanonicalIntrinsicWave period hPeriod hStokes⟩

/-- Exact coarea transport from the canonical local divergence to the global
Euler skew integral. -/
theorem localDivergence_integral_eq_globalSkew
    (data : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      ∫ point,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod := by
  let waveNaturality :=
    data.intrinsicWave.toWaveAtlasNaturality period hPeriod
  let operatorData :=
    canonicalPhysicalScalarEulerProductOperatorData
      period hPeriod waveNaturality massSquared
  calc
    (∫ parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
        ∫ parameter,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D.canonicalPhysicalScalarEulerProductSkewDensity
            period hPeriod massSquared field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun parameter =>
        (canonicalPhysicalScalarEulerProductSkewDensity_eq_localDivergence
          period hPeriod waveNaturality massSquared field test parameter).symm
    _ = _ :=
      P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerProductDivergenceClosure4D.integral_productSkewDensity_eq_global
        period hPeriod operatorData field test

/-- The genuine global Stokes statement implies the exact canonical
local-divergence/cut-bulk identity, with signs fixed by the established
two-sheet theorem. -/
theorem localDivergence_integral_eq_cutBulk
    (data : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test parameter
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ := by
  rw [data.localDivergence_integral_eq_globalSkew period hPeriod field test,
    data.eulerSkew_integral_eq_orientedBoundary field test]
  have hStokes :=
    cutBulkGlobalMeasuredGreenStokes
      period hPeriod massSquared field test
  linarith

/-- Conversion to the canonical local-divergence package. -/
def toCanonicalLocalDivergenceData
    (data : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared where
  waveNaturality :=
    data.intrinsicWave.toWaveAtlasNaturality period hPeriod
  localDivergence_integral_eq_cutBulk :=
    data.localDivergence_integral_eq_cutBulk period hPeriod

/-- Conversion to the weighted transport presentation. -/
def toWeightedTransportedGlobalGreenData
    (data : CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared where
  intrinsicWave := data.intrinsicWave
  localDivergence_integral_eq_cutBulk :=
    data.localDivergence_integral_eq_cutBulk period hPeriod

/-- Conversely, the canonical local-divergence package recovers the genuine
global boundary statement using the established cut-bulk Stokes theorem. -/
def ofCanonicalLocalDivergenceData
    (localData :
      CanonicalPhysicalScalarCanonicalLocalDivergenceData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
      period hPeriod massSquared where
  intrinsicWave :=
    CanonicalPhysicalScalarIntrinsicWaveData.ofWaveAtlasNaturality
      period hPeriod localData.waveNaturality
  eulerSkew_integral_eq_orientedBoundary := by
    intro field test
    have hEuler := localData.certificate.2.2 field test
    have hStokes :=
      cutBulkGlobalMeasuredGreenStokes
        period hPeriod massSquared field test
    linarith

/-- The former local integral input is exactly the genuine global
Green--Stokes statement; no extra factor or orientation assumption remains. -/
theorem nonempty_iff_canonicalLocalDivergenceData :
    Nonempty
        (CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData
          period hPeriod massSquared) ↔
      Nonempty
        (CanonicalPhysicalScalarCanonicalLocalDivergenceData
          period hPeriod massSquared) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toCanonicalLocalDivergenceData period hPeriod⟩
  · rintro ⟨localData⟩
    exact ⟨ofCanonicalLocalDivergenceData period hPeriod localData⟩

end CanonicalPhysicalScalarIntrinsicWaveGlobalGreenStokesData

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData

/-- The corrected weighted transport is exactly twice the canonical cut-bulk
divergence measure. -/
theorem correctedTransportedDivergence_integral_eq_two_cutBulk
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      (canonicalLatitudeNormalHalfCollarCorrection parameter.2).toReal *
        canonicalPhysicalScalarHalfCollarDivergenceDensity
          period hPeriod massSquared field test
          (canonicalLatitudeWeightedNormalToHalfCollarTransport parameter)
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ := by
  let collarDensity := canonicalPhysicalScalarHalfCollarDivergenceDensity
    period hPeriod massSquared field test
  have hIntegrable :
      Integrable collarDensity (canonicalLatitudeCollarMeasure period) := by
    change Integrable
      (canonicalCutBulkDivergenceDensity
        period hPeriod massSquared field test)
      (canonicalLatitudeCollarMeasure period)
    exact canonicalCutBulkDivergenceDensity_integrable
      period hPeriod massSquared field test
  have hTransport :=
    canonicalLatitudeWeightedNormalToHalfCollar_integral_comp
      period collarDensity hIntegrable
  have hIterated :=
    canonicalLatitudeCollar_integral_eq_iterated
      period collarDensity hIntegrable
  calc
    (∫ parameter,
      (canonicalLatitudeNormalHalfCollarCorrection parameter.2).toReal *
        canonicalPhysicalScalarHalfCollarDivergenceDensity
          period hPeriod massSquared field test
          (canonicalLatitudeWeightedNormalToHalfCollarTransport parameter)
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
        2 * ∫ parameter, collarDensity parameter
          ∂canonicalLatitudeCollarMeasure period := by
      simpa [collarDensity] using hTransport
    _ = 2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ := by
      rw [hIterated,
        cutBulkCanonicalDivergenceMeasure_univ
          period hPeriod massSquared field test]
      rfl

/-- The canonical local-divergence identity and corrected factor-two transport
give the weighted global cancellation. -/
theorem global_cancellation
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    (∫ parameter,
      (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test parameter +
        (canonicalLatitudeNormalHalfCollarCorrection parameter.2).toReal *
          canonicalPhysicalScalarHalfCollarDivergenceDensity
            period hPeriod massSquared field test
            (canonicalLatitudeWeightedNormalToHalfCollarTransport parameter))
      ∂canonicalLatitudeCauchyJetProductMeasure period) = 0 := by
  have hLocal :
      Integrable
        (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
          period hPeriod field test)
        (canonicalLatitudeCauchyJetProductMeasure period) :=
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity_integrable
      period hPeriod
      (data.intrinsicWave.toWaveAtlasNaturality period hPeriod)
      massSquared field test
  have hHalfCollar :
      Integrable
        (canonicalPhysicalScalarHalfCollarDivergenceDensity
          period hPeriod massSquared field test)
        (canonicalLatitudeCollarMeasure period) := by
    change Integrable
      (canonicalCutBulkDivergenceDensity
        period hPeriod massSquared field test)
      (canonicalLatitudeCollarMeasure period)
    exact canonicalCutBulkDivergenceDensity_integrable
      period hPeriod massSquared field test
  have hTransported :
      Integrable
        (fun parameter =>
          (canonicalLatitudeNormalHalfCollarCorrection parameter.2).toReal *
            canonicalPhysicalScalarHalfCollarDivergenceDensity
              period hPeriod massSquared field test
              (canonicalLatitudeWeightedNormalToHalfCollarTransport parameter))
        (canonicalLatitudeCauchyJetProductMeasure period) :=
    canonicalLatitudeWeightedNormalToHalfCollar_integrable_comp
      period
      (canonicalPhysicalScalarHalfCollarDivergenceDensity
        period hPeriod massSquared field test)
      hHalfCollar
  rw [integral_add hLocal hTransported,
    data.localDivergence_integral_eq_cutBulk field test,
    correctedTransportedDivergence_integral_eq_two_cutBulk
      period hPeriod (massSquared := massSquared) field test]
  ring

/-- Build the weighted global Green package from the canonical local-divergence
identity. This exposes that identity as the sole remaining geometric input. -/
def ofLocalDivergenceIntegral
    (intrinsicWave : CanonicalPhysicalScalarIntrinsicWaveData period hPeriod)
    (localDivergence_integral_eq_cutBulk :
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ parameter,
          canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared where
  intrinsicWave := intrinsicWave
  localDivergence_integral_eq_cutBulk :=
    localDivergence_integral_eq_cutBulk

/-- Build the weighted package with the canonical intrinsic wave. -/
def ofCanonicalIntrinsicWave
    (localDivergence_integral_eq_cutBulk :
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ parameter,
          canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared :=
  ofLocalDivergenceIntegral period hPeriod
    (CanonicalPhysicalScalarIntrinsicWaveData.canonical period hPeriod)
    localDivergence_integral_eq_cutBulk

/-- Since intrinsic wave naturality is canonical, inhabiting the weighted
package is exactly the remaining local-divergence/cut-bulk identity. -/
theorem nonempty_iff_localDivergence_integral_eq_cutBulk :
    Nonempty
        (CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
          period hPeriod massSquared) ↔
      ∀ field test : SmoothScalarField period hPeriod,
        (∫ parameter,
          canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test parameter
          ∂canonicalLatitudeCauchyJetProductMeasure period) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ := by
  constructor
  · rintro ⟨data⟩
    exact data.localDivergence_integral_eq_cutBulk
  · intro hStokes
    exact ⟨ofCanonicalIntrinsicWave period hPeriod hStokes⟩

/-- The existing canonical local-divergence package feeds the weighted global
Green construction without any additional Stokes assumption. -/
def ofCanonicalLocalDivergenceData
    (localData :
      CanonicalPhysicalScalarCanonicalLocalDivergenceData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared :=
  ofLocalDivergenceIntegral period hPeriod
    (CanonicalPhysicalScalarIntrinsicWaveData.ofWaveAtlasNaturality
      period hPeriod localData.waveNaturality)
    localData.localDivergence_integral_eq_cutBulk

/-- Forgetting the weighted transport recovers the canonical local-divergence
package. -/
def toCanonicalLocalDivergenceData
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarCanonicalLocalDivergenceData
      period hPeriod massSquared where
  waveNaturality :=
    data.intrinsicWave.toWaveAtlasNaturality period hPeriod
  localDivergence_integral_eq_cutBulk :=
    data.localDivergence_integral_eq_cutBulk

/-- The weighted package introduces no extra mathematical obligation beyond
the canonical local-divergence package. -/
theorem nonempty_iff_canonicalLocalDivergenceData :
    Nonempty
        (CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
          period hPeriod massSquared) ↔
      Nonempty
        (CanonicalPhysicalScalarCanonicalLocalDivergenceData
          period hPeriod massSquared) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.toCanonicalLocalDivergenceData period hPeriod⟩
  · rintro ⟨localData⟩
    exact ⟨ofCanonicalLocalDivergenceData period hPeriod localData⟩

/-- Integrability of the explicit half-collar divergence. -/
theorem halfCollarDivergence_integrable
    (_data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Integrable
      (canonicalPhysicalScalarHalfCollarDivergenceDensity
        period hPeriod massSquared field test)
      (canonicalLatitudeCollarMeasure period) := by
  change Integrable
    (canonicalCutBulkDivergenceDensity
      period hPeriod massSquared field test)
    (canonicalLatitudeCollarMeasure period)
  exact canonicalCutBulkDivergenceDensity_integrable
    period hPeriod massSquared field test

/-- Integrability of the corrected transported half-collar divergence. -/
theorem transportedDivergence_integrable
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Integrable
      (fun parameter =>
        (canonicalLatitudeNormalHalfCollarCorrection parameter.2).toReal *
          canonicalPhysicalScalarHalfCollarDivergenceDensity
            period hPeriod massSquared field test
            (canonicalLatitudeWeightedNormalToHalfCollarTransport parameter))
      (canonicalLatitudeCauchyJetProductMeasure period) :=
  canonicalLatitudeWeightedNormalToHalfCollar_integrable_comp
    period
    (canonicalPhysicalScalarHalfCollarDivergenceDensity
      period hPeriod massSquared field test)
    (data.halfCollarDivergence_integrable period hPeriod field test)

/-- Integrability of the canonical local divergence. -/
theorem localDivergence_integrable
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Integrable
      (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
        period hPeriod field test)
      (canonicalLatitudeCauchyJetProductMeasure period) :=
  canonicalPhysicalScalarEulerProductLocalDivergenceDensity_integrable
    period hPeriod
    (data.intrinsicWave.toWaveAtlasNaturality period hPeriod)
    massSquared field test

/-- The canonical cut-bulk identity gives the exact half-collar Green
integral. -/
theorem localDivergence_eq_halfCollar
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
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
  rw [data.localDivergence_integral_eq_cutBulk field test,
    cutBulkCanonicalDivergenceMeasure_univ
      period hPeriod massSquared field test]

/-- Direct intrinsic local Green package. -/
def toIntrinsicWaveLocalGreenData
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveLocalGreen4D.CanonicalPhysicalScalarIntrinsicWaveLocalGreenData
      period hPeriod massSquared where
  intrinsicWave := data.intrinsicWave
  localDivergence_eq_halfCollar :=
    data.localDivergence_eq_halfCollar period hPeriod

/-- The local divergence itself is a canonical normal component with zero
induced tangential remainder. -/
def toCanonicalNormalGreenData
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared where
  intrinsicWave := data.intrinsicWave
  normalDensity := fun field test =>
    canonicalPhysicalScalarEulerProductLocalDivergenceDensity
      period hPeriod field test
  normalDensity_integrable :=
    data.localDivergence_integrable period hPeriod
  tangential_base_integral_zero := by
    intro field test normal
    simp
  normal_integral_eq_halfCollar :=
    data.localDivergence_eq_halfCollar period hPeriod

/-- Correct dense physical Green core. -/
def greenCore
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :=
  (data.toIntrinsicWaveLocalGreenData period hPeriod).greenCore
    period hPeriod

/-- Global weighted-transport Green certificate. -/
theorem certificate
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
        period hPeriod massSquared) :
    Measure.map canonicalLatitudeWeightedNormalToHalfCollarTransport
        (canonicalLatitudeCorrectedCauchyJetProductMeasure period) =
      (2 : NNReal) • canonicalLatitudeCollarMeasure period ∧
      (∀ field test,
        Integrable
          (canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test)
          (canonicalLatitudeCauchyJetProductMeasure period)) ∧
      (∀ field test,
        (∫ point,
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
            period hPeriod) =
        -2 * cutBulkCanonicalDivergenceMeasure
          period hPeriod massSquared field test Set.univ) :=
  ⟨map_canonicalLatitudeCorrectedCauchyJetProductMeasure period,
    data.localDivergence_integrable period hPeriod,
    (data.toIntrinsicWaveLocalGreenData period hPeriod).certificate
      period hPeriod |>.2⟩

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
end JanusFormal
