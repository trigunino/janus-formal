import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D

/-!
# Global smooth scalar wave on the canonical Lorentz quotient

The canonical intrinsic scalar-wave representative already globalizes the
chartwise covariant contraction.  This gate proves that representative is a
smooth scalar field, packages it as a real linear map on smooth scalar fields,
and records automatic integrability for every finite measure.

This is the analytic input needed before a spatially varying conformal
curvature law can be stated with global smooth fields.  The scalar-wave product
rule, conformal Christoffel/Ricci/scalar-curvature laws and the corresponding
Einstein--Hilbert Hessian remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalSmoothScalarWave4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Smooth local and global wave representatives -/

theorem canonicalPhysicalScalarWaveAtlasRepresentative_contDiff
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (canonicalPhysicalScalarWaveAtlasRepresentative
        period hPeriod field patch) := by
  unfold canonicalPhysicalScalarWaveAtlasRepresentative
    covariantScalarJetWave
  apply ContDiff.sum
  intro first _
  apply ContDiff.sum
  intro second _
  exact
    (localMetricInverseEntry_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch first second).mul
      (localCovariantScalarJet_hessian_component_contDiff period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch field first second)

def canonicalGlobalSmoothScalarWave
    (field : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod where
  toFun :=
    (CanonicalPhysicalScalarIntrinsicWaveData.canonical
      period hPeriod).wave field
  contMDiff_toFun := by
    intro point
    let witness :=
      canonicalPhysicalScalarEulerChartWitness period hPeriod point
    rw [← witness.coordinate_eq]
    let hLocal :=
      witness.patch.coordinateMap_isLocalDiffeomorph witness.coordinate
    have hRepresentative :
        ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
          (canonicalPhysicalScalarWaveAtlasRepresentative
              period hPeriod field witness.patch ∘
            hLocal.localInverse)
          (witness.patch.coordinateMap witness.coordinate) :=
      (canonicalPhysicalScalarWaveAtlasRepresentative_contDiff
        period hPeriod field witness.patch)
        |>.contMDiff.contMDiffAt.comp _
          hLocal.localInverse_contMDiffAt
    apply hRepresentative.congr_of_eventuallyEq
    filter_upwards [hLocal.localInverse_eventuallyEq_right] with nearby hNearby
    have hRight :
        witness.patch.coordinateMap (hLocal.localInverse nearby) = nearby := by
      simpa only [Function.comp_apply, id_eq] using hNearby
    change
      (CanonicalPhysicalScalarIntrinsicWaveData.canonical
          period hPeriod).wave field nearby =
        canonicalPhysicalScalarWaveAtlasRepresentative
          period hPeriod field witness.patch (hLocal.localInverse nearby)
    calc
      (CanonicalPhysicalScalarIntrinsicWaveData.canonical
          period hPeriod).wave field nearby =
          (CanonicalPhysicalScalarIntrinsicWaveData.canonical
            period hPeriod).wave field
              (witness.patch.coordinateMap (hLocal.localInverse nearby)) :=
        congrArg
          ((CanonicalPhysicalScalarIntrinsicWaveData.canonical
            period hPeriod).wave field) hRight.symm
      _ = _ :=
        ((CanonicalPhysicalScalarIntrinsicWaveData.canonical
          period hPeriod).local_eq field witness.patch
            (hLocal.localInverse nearby)).symm

theorem canonicalGlobalSmoothScalarWave_eq_local
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    canonicalGlobalSmoothScalarWave period hPeriod field
        (patch.coordinateMap coordinate) =
      canonicalPhysicalScalarWaveAtlasRepresentative
        period hPeriod field patch coordinate :=
  ((CanonicalPhysicalScalarIntrinsicWaveData.canonical
    period hPeriod).local_eq field patch coordinate).symm

/-! ## Linearity and integrability -/

theorem canonicalGlobalSmoothScalarWave_add
    (first second : SmoothScalarField period hPeriod) :
    canonicalGlobalSmoothScalarWave period hPeriod (first + second) =
      canonicalGlobalSmoothScalarWave period hPeriod first +
        canonicalGlobalSmoothScalarWave period hPeriod second := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    canonicalGlobalSmoothScalarWave period hPeriod (first + second) point =
      canonicalGlobalSmoothScalarWave period hPeriod first point +
        canonicalGlobalSmoothScalarWave period hPeriod second point
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  rw [canonicalGlobalSmoothScalarWave_eq_local,
    canonicalGlobalSmoothScalarWave_eq_local,
    canonicalGlobalSmoothScalarWave_eq_local]
  exact localCovariantScalarWave_add period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      witness.patch first second witness.coordinate

theorem canonicalGlobalSmoothScalarWave_smul
    (scalar : Real)
    (field : SmoothScalarField period hPeriod) :
    canonicalGlobalSmoothScalarWave period hPeriod (scalar • field) =
      scalar • canonicalGlobalSmoothScalarWave period hPeriod field := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change
    canonicalGlobalSmoothScalarWave period hPeriod (scalar • field) point =
      scalar • canonicalGlobalSmoothScalarWave period hPeriod field point
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  rw [canonicalGlobalSmoothScalarWave_eq_local,
    canonicalGlobalSmoothScalarWave_eq_local]
  exact localCovariantScalarWave_smul period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      witness.patch scalar field witness.coordinate

def canonicalGlobalSmoothScalarWaveLinearMap :
    SmoothScalarField period hPeriod →ₗ[Real]
      SmoothScalarField period hPeriod where
  toFun := canonicalGlobalSmoothScalarWave period hPeriod
  map_add' := canonicalGlobalSmoothScalarWave_add period hPeriod
  map_smul' := canonicalGlobalSmoothScalarWave_smul period hPeriod

@[simp]
theorem canonicalGlobalSmoothScalarWaveLinearMap_apply
    (field : SmoothScalarField period hPeriod) :
    canonicalGlobalSmoothScalarWaveLinearMap period hPeriod field =
      canonicalGlobalSmoothScalarWave period hPeriod field :=
  rfl

theorem canonicalGlobalSmoothScalarWave_integrable
    (field : SmoothScalarField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable
      (canonicalGlobalSmoothScalarWave period hPeriod field)
      measure :=
  (canonicalGlobalSmoothScalarWave period hPeriod field)
    |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end

end P0EFTJanusMappingTorusGlobalSmoothScalarWave4D
end JanusFormal
