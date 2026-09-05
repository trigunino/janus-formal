import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhasedNormalRotationMeasure4D

/-! # Complete spatial rotation flows on the canonical mapping torus -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalSpatialRotationQuotient4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

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

theorem ambientSpatialRotationFlow_angle_add
    (axis : Fin 3) (first second : Real) (point : R4Point) :
    ambientSpatialRotationFlow axis (first + second, point) =
      ambientSpatialRotationFlow axis
        (first, ambientSpatialRotationFlow axis (second, point)) := by
  fin_cases axis <;> ext index <;> fin_cases index <;>
    simp [ambientSpatialRotationFlow, Real.sin_add, Real.cos_add] <;> ring

theorem sphereSpatialRotationFlow_angle_add
    (axis : Fin 3) (first second : Real) (point : UnitThreeSphere) :
    sphereSpatialRotationFlow axis (first + second, point) =
      sphereSpatialRotationFlow axis
        (first, sphereSpatialRotationFlow axis (second, point)) := by
  apply Subtype.ext
  simp only [sphereSpatialRotationFlow_coe]
  exact ambientSpatialRotationFlow_angle_add axis first second point.1

theorem coverSpatialRotationFlow_add
    (axis : Fin 3) (first second : Real)
    (point : EffectiveCover period hPeriod) :
    coverSpatialRotationFlow period hPeriod axis (first + second, point) =
      coverSpatialRotationFlow period hPeriod axis
        (first, coverSpatialRotationFlow period hPeriod axis
          (second, point)) := by
  apply MappingTorusCover.ext
  · exact sphereSpatialRotationFlow_angle_add axis first second point.fiber
  · rfl

private theorem coverSpatialRotationFlow_respects_orbit
    (axis : Fin 3) (parameter : Real)
    (first second : EffectiveCover period hPeriod)
    (hOrbit : AddAction.orbitRel Int (EffectiveCover period hPeriod)
      first second) :
    mappingTorusMk (sphereData period hPeriod)
        (coverSpatialRotationFlow period hPeriod axis (parameter, first)) =
      mappingTorusMk (sphereData period hPeriod)
        (coverSpatialRotationFlow period hPeriod axis (parameter, second)) := by
  have hProjection : mappingTorusMk (sphereData period hPeriod) first =
      mappingTorusMk (sphereData period hPeriod) second := Quotient.sound hOrbit
  obtain ⟨winding, hWinding⟩ :=
    (mappingTorusMk_eq_iff_exists_vadd
      (sphereData period hPeriod) first second).1 hProjection
  apply (mappingTorusMk_eq_iff_exists_vadd
    (sphereData period hPeriod) _ _).2
  refine ⟨winding, ?_⟩
  rw [coverSpatialRotationFlow_deck_commutes]
  exact congrArg
    (fun point => coverSpatialRotationFlow period hPeriod axis
      (parameter, point)) hWinding

/-- Genuine spatial rotation on the canonical mapping-torus quotient. -/
def spatialRotationFlow (axis : Fin 3) (parameter : Real) :
    EffectiveQuotient period hPeriod → EffectiveQuotient period hPeriod :=
  Quotient.lift
    (fun point => mappingTorusMk (sphereData period hPeriod)
      (coverSpatialRotationFlow period hPeriod axis (parameter, point)))
    (coverSpatialRotationFlow_respects_orbit period hPeriod axis parameter)

@[simp]
theorem spatialRotationFlow_mk
    (axis : Fin 3) (parameter : Real)
    (point : EffectiveCover period hPeriod) :
    spatialRotationFlow period hPeriod axis parameter
        (mappingTorusMk (sphereData period hPeriod) point) =
      mappingTorusMk (sphereData period hPeriod)
        (coverSpatialRotationFlow period hPeriod axis (parameter, point)) :=
  rfl

theorem spatialRotationFlow_continuous
    (axis : Fin 3) (parameter : Real) :
    Continuous (spatialRotationFlow period hPeriod axis parameter) := by
  apply Continuous.quotient_lift
  exact (mappingTorusMk_isCoveringMap
    (sphereData period hPeriod)).isLocalHomeomorph.continuous.comp
      ((coverSpatialRotationFlow_contMDiff period hPeriod axis)
        |>.continuous.comp (continuous_const.prodMk continuous_id))

@[simp]
theorem spatialRotationFlow_zero
    (axis : Fin 3) (point : EffectiveQuotient period hPeriod) :
    spatialRotationFlow period hPeriod axis 0 point = point := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  rw [spatialRotationFlow_mk, coverSpatialRotationFlow_zero]

theorem spatialRotationFlow_add
    (axis : Fin 3) (first second : Real)
    (point : EffectiveQuotient period hPeriod) :
    spatialRotationFlow period hPeriod axis (first + second) point =
      spatialRotationFlow period hPeriod axis first
        (spatialRotationFlow period hPeriod axis second point) := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  rw [spatialRotationFlow_mk, spatialRotationFlow_mk,
    spatialRotationFlow_mk, coverSpatialRotationFlow_add]

private def spatialRotationHomeomorph
    (axis : Fin 3) (parameter : Real) :
    EffectiveQuotient period hPeriod ≃ₜ EffectiveQuotient period hPeriod where
  toFun := spatialRotationFlow period hPeriod axis parameter
  invFun := spatialRotationFlow period hPeriod axis (-parameter)
  left_inv point := by
    rw [← spatialRotationFlow_add]
    simp
  right_inv point := by
    rw [← spatialRotationFlow_add]
    simp
  continuous_toFun := spatialRotationFlow_continuous period hPeriod axis parameter
  continuous_invFun := spatialRotationFlow_continuous period hPeriod axis
    (-parameter)

theorem spatialRotationFlow_measurableEmbedding
    (axis : Fin 3) (parameter : Real) :
    MeasurableEmbedding (spatialRotationFlow period hPeriod axis parameter) :=
  (spatialRotationHomeomorph period hPeriod axis parameter).measurableEmbedding

/-- The jointly parameterized spatial rotation action. -/
def jointSpatialRotationFlow
    (axis : Fin 3) (input : Real × EffectiveQuotient period hPeriod) :
    EffectiveQuotient period hPeriod :=
  spatialRotationFlow period hPeriod axis input.1 input.2

theorem jointSpatialRotationFlow_contMDiff (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (jointSpatialRotationFlow period hPeriod axis) := by
  have hProjection := reflectedSphere_projection_isLocalDiffeomorph period hPeriod
  have hLift : ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (fun input : Real × EffectiveCover period hPeriod =>
        mappingTorusMk (sphereData period hPeriod)
          (coverSpatialRotationFlow period hPeriod axis input)) :=
    (hProjection.contMDiff.of_le (m := ∞) (by simp)).comp
      (coverSpatialRotationFlow_contMDiff period hPeriod axis)
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
            (coverSpatialRotationFlow period hPeriod axis input)) ∘
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
  change spatialRotationFlow period hPeriod axis input.1 input.2 =
    mappingTorusMk (sphereData period hPeriod)
      (coverSpatialRotationFlow period hPeriod axis
        (input.1, hLocal.localInverse input.2))
  rw [← spatialRotationFlow_mk]
  exact congrArg (spatialRotationFlow period hPeriod axis input.1)
    hInputRight.symm

/-- Gate marker for the three complete smooth quotient rotation flows. -/
theorem canonical_spatial_rotation_quotient_gate :
    ∀ axis : Fin 3,
      ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
        coverModelWithCorners ∞
        (jointSpatialRotationFlow period hPeriod axis) ∧
      ∀ parameter : Real,
        MeasurableEmbedding
          (spatialRotationFlow period hPeriod axis parameter) := by
  intro axis
  exact ⟨jointSpatialRotationFlow_contMDiff period hPeriod axis,
    spatialRotationFlow_measurableEmbedding period hPeriod axis⟩

end
end P0EFTJanusMappingTorusCanonicalSpatialRotationQuotient4D
end JanusFormal
