import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalSpatialRotationMeasure4D

/-! # Joint smoothness of canonical phased normal rotations -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhasedNormalRotationSmooth4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationQuotient4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The jointly parameterized phased normal action. -/
def jointPhasedNormalRotationFlow
    (axis : Fin 3) (phase : Fin 2)
    (input : Real × EffectiveQuotient period hPeriod) :
    EffectiveQuotient period hPeriod :=
  phasedNormalRotationFlow period hPeriod axis phase input.1 input.2

theorem jointPhasedNormalRotationFlow_contMDiff
    (axis : Fin 3) (phase : Fin 2) :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (jointPhasedNormalRotationFlow period hPeriod axis phase) := by
  have hProjection := reflectedSphere_projection_isLocalDiffeomorph period hPeriod
  have hLift : ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (fun input : Real × EffectiveCover period hPeriod =>
        mappingTorusMk (sphereData period hPeriod)
          (coverPhasedNormalRotationFlow period hPeriod axis phase input)) :=
    (hProjection.contMDiff.of_le (m := ∞) (by simp)).comp
      (coverPhasedNormalRotationFlow_contMDiff period hPeriod axis phase)
  rintro ⟨parameter, quotientPoint⟩
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
  have hLocal := hProjection anchor
  have hInput : ContMDiffAt
      (𝓘(Real, Real).prod coverModelWithCorners)
      (𝓘(Real, Real).prod coverModelWithCorners) ∞
      (fun input : Real × EffectiveQuotient period hPeriod =>
        (input.1, hLocal.localInverse input.2))
      (parameter, mappingTorusMk (sphereData period hPeriod) anchor) :=
    contMDiffAt_fst.prodMk
      ((hLocal.localInverse_contMDiffAt.of_le (m := ∞) (by simp)).comp
        (parameter, mappingTorusMk (sphereData period hPeriod) anchor)
        contMDiffAt_snd)
  have hLocalLift : ContMDiffAt
      (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      ((fun input : Real × EffectiveCover period hPeriod =>
          mappingTorusMk (sphereData period hPeriod)
            (coverPhasedNormalRotationFlow period hPeriod axis phase input)) ∘
        (fun input : Real × EffectiveQuotient period hPeriod =>
          (input.1, hLocal.localInverse input.2)))
      (parameter, mappingTorusMk (sphereData period hPeriod) anchor) :=
    hLift.contMDiffAt.comp _ hInput
  apply hLocalLift.congr_of_eventuallyEq
  have hSnd : Filter.Tendsto
      (fun input : Real × EffectiveQuotient period hPeriod => input.2)
      (𝓝 (parameter, mappingTorusMk (sphereData period hPeriod) anchor))
      (𝓝 (mappingTorusMk (sphereData period hPeriod) anchor)) :=
    continuousAt_snd
  have hRight := hLocal.localInverse_eventuallyEq_right.comp_tendsto hSnd
  filter_upwards [hRight] with input hInputRight
  change phasedNormalRotationFlow period hPeriod axis phase input.1 input.2 =
    mappingTorusMk (sphereData period hPeriod)
      (coverPhasedNormalRotationFlow period hPeriod axis phase
        (input.1, hLocal.localInverse input.2))
  rw [← phasedNormalRotationFlow_mk]
  exact congrArg
    (phasedNormalRotationFlow period hPeriod axis phase input.1)
    hInputRight.symm

/-- Gate marker: every phased normal action is jointly smooth and preserves
the canonical volume at each parameter. -/
theorem canonical_phased_normal_rotation_smooth_gate :
    ∀ (axis : Fin 3) (phase : Fin 2),
      ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
        coverModelWithCorners ∞
        (jointPhasedNormalRotationFlow period hPeriod axis phase) ∧
      ∀ parameter : Real,
        MeasurePreserving
          (phasedNormalRotationFlow period hPeriod axis phase parameter)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  intro axis phase
  exact ⟨jointPhasedNormalRotationFlow_contMDiff period hPeriod axis phase,
    intrinsicCanonicalLorentzVolumeMeasure_phasedNormalRotation_measurePreserving
      period hPeriod axis phase⟩

end
end P0EFTJanusMappingTorusCanonicalPhasedNormalRotationSmooth4D
end JanusFormal
