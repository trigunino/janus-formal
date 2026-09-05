import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D

/-! # Descent of phased normal rotations to the mapping torus -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhasedNormalRotationQuotient4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

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

private def euclideanNormalRotationFlow
    (axis : Fin 3) (input : Real × EuclideanR4) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm
    (ambientNormalRotationFlow axis
      (input.1, EuclideanSpace.equiv (Fin 4) Real input.2))

private theorem euclideanNormalRotationFlow_contDiff (axis : Fin 3) :
    ContDiff Real ∞ (euclideanNormalRotationFlow axis) :=
  (EuclideanSpace.equiv (Fin 4) Real).symm.contDiff.comp
    ((ambientNormalRotationFlow_contDiff axis).comp
      (contDiff_fst.prodMk
        ((EuclideanSpace.equiv (Fin 4) Real).contDiff.comp contDiff_snd)))

private theorem euclideanNormalRotationFlow_mem_sphere
    (axis : Fin 3) (input : Real × StandardSphere) :
    euclideanNormalRotationFlow axis (input.1, input.2.1) ∈
      Metric.sphere (0 : EuclideanR4) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hNorm : ‖input.2.1‖ = 1 := by
    have h := input.2.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h
  have hSquare :
      ‖euclideanNormalRotationFlow axis (input.1, input.2.1)‖ ^ 2 = 1 := by
    rw [euclideanNormalRotationFlow,
      euclidean_norm_sq_eq_radiusSquared,
      ambientNormalRotationFlow_preserves_radius,
      ← euclidean_norm_sq_eq_radiusSquared]
    simp [hNorm]
  nlinarith [norm_nonneg
    (euclideanNormalRotationFlow axis (input.1, input.2.1))]

private def standardSphereNormalRotationFlow
    (axis : Fin 3) (input : Real × StandardSphere) : StandardSphere :=
  ⟨euclideanNormalRotationFlow axis (input.1, input.2.1),
    euclideanNormalRotationFlow_mem_sphere axis input⟩

private theorem standardSphereNormalRotationFlow_contMDiff
    (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod (𝓡 3)) (𝓡 3) ∞
      (standardSphereNormalRotationFlow axis) := by
  letI : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩
  apply ContMDiff.codRestrict_sphere
  exact (euclideanNormalRotationFlow_contDiff axis).comp_contMDiff
    (contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd))

/-- Normal sphere rotation in the transported Janus atlas. -/
def sphereNormalRotationFlow
    (axis : Fin 3) (input : Real × UnitThreeSphere) : UnitThreeSphere :=
  unitThreeSphereHomeomorph.symm
    (standardSphereNormalRotationFlow axis
      (input.1, unitThreeSphereHomeomorph input.2))

theorem sphereNormalRotationFlow_contMDiff (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod (𝓡 3)) (𝓡 3) ∞
      (sphereNormalRotationFlow axis) := by
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  have hInv := chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  exact hInv.comp ((standardSphereNormalRotationFlow_contMDiff axis).comp
    (contMDiff_fst.prodMk (hTo.comp contMDiff_snd)))

@[simp]
theorem sphereNormalRotationFlow_zero
    (axis : Fin 3) (point : UnitThreeSphere) :
    sphereNormalRotationFlow axis (0, point) = point := by
  apply unitThreeSphereHomeomorph.injective
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  simp [sphereNormalRotationFlow, standardSphereNormalRotationFlow,
    euclideanNormalRotationFlow]

@[simp]
theorem sphereNormalRotationFlow_coe
    (axis : Fin 3) (input : Real × UnitThreeSphere) :
    (sphereNormalRotationFlow axis input).1 =
      ambientNormalRotationFlow axis (input.1, input.2.1) := by
  change WithLp.ofLp
      (WithLp.toLp 2
        (ambientNormalRotationFlow axis
          (input.1, WithLp.ofLp (WithLp.toLp 2 input.2.1)))) = _
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp]

theorem sphereNormalRotationFlow_reflection_conjugates
    (axis : Fin 3) (input : Real × UnitThreeSphere) :
    sphereReflection (sphereNormalRotationFlow axis input) =
      sphereNormalRotationFlow axis (-input.1, sphereReflection input.2) := by
  apply Subtype.ext
  change reflectPoint (sphereNormalRotationFlow axis input).1 =
    (sphereNormalRotationFlow axis
      (-input.1, sphereReflection input.2)).1
  rw [sphereNormalRotationFlow_coe, sphereNormalRotationFlow_coe]
  exact ambientNormalRotationFlow_reflection_conjugates axis
    (input.1, input.2.1)

theorem sphereNormalRotationFlow_angle_add
    (axis : Fin 3) (first second : Real) (point : UnitThreeSphere) :
    sphereNormalRotationFlow axis (first + second, point) =
      sphereNormalRotationFlow axis
        (first, sphereNormalRotationFlow axis (second, point)) := by
  apply Subtype.ext
  simp only [sphereNormalRotationFlow_coe]
  exact ambientNormalRotationFlow_angle_add axis first second point.1

private theorem sphereReflection_square :
    sphereReflection * sphereReflection = 1 := by
  apply Homeomorph.ext
  intro point
  apply Subtype.ext
  exact reflect_point_involutive point.1

private theorem sphereReflection_zpow_two :
    sphereReflection ^ (2 : Int) = 1 := by
  simpa only [zpow_two] using sphereReflection_square

private theorem sphereReflection_zpow_apply_parity
    (winding : Int) (point : UnitThreeSphere) :
    (sphereReflection ^ winding) point =
      if Even winding then point else sphereReflection point := by
  rcases Int.even_or_odd' winding with ⟨multiple, rfl | rfl⟩
  · rw [zpow_mul, sphereReflection_zpow_two, one_zpow]
    simp
  · rw [zpow_add_one, zpow_mul, sphereReflection_zpow_two, one_zpow,
      one_mul]
    simp

/-- The deck reflection to any integer power conjugates the rotation angle by
the same sign carried by the antiperiodic phase. -/
theorem sphereNormalRotationFlow_reflection_zpow_conjugates
    (axis : Fin 3) (winding : Int) (angle : Real)
    (point : UnitThreeSphere) :
    (sphereReflection ^ winding)
        (sphereNormalRotationFlow axis (angle, point)) =
      sphereNormalRotationFlow axis
        (((-1 : Real) ^ winding) * angle,
          (sphereReflection ^ winding) point) := by
  rw [sphereReflection_zpow_apply_parity,
    sphereReflection_zpow_apply_parity, neg_one_zpow_eq_ite]
  by_cases hEven : Even winding
  · simp [hEven]
  · simpa [hEven] using
      sphereNormalRotationFlow_reflection_conjugates axis (angle, point)

/-- Phased normal rotation upstairs; time is fixed. -/
def coverPhasedNormalRotationFlow
    (axis : Fin 3) (phase : Fin 2)
    (input : Real × EffectiveCover period hPeriod) :
    EffectiveCover period hPeriod :=
  ⟨sphereNormalRotationFlow axis
      (input.1 * canonicalNormalRotationPhase period phase input.2.time,
        input.2.fiber),
    input.2.time⟩

@[simp]
theorem coverPhasedNormalRotationFlow_zero
    (axis : Fin 3) (phase : Fin 2)
    (point : EffectiveCover period hPeriod) :
    coverPhasedNormalRotationFlow period hPeriod axis phase (0, point) =
      point := by
  apply MappingTorusCover.ext
  · simp [coverPhasedNormalRotationFlow]
  · rfl

theorem coverPhasedNormalRotationFlow_contMDiff
    (axis : Fin 3) (phase : Fin 2) :
    ContMDiff (𝓘(Real, Real).prod coverModelWithCorners)
      coverModelWithCorners ∞
      (coverPhasedNormalRotationFlow period hPeriod axis phase) := by
  let productEquiv := coverHomeomorphProd (sphereData period hPeriod)
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
    productEquiv
  have hInv := chartedSpacePullback_invFun_contMDiff coverModelWithCorners ∞
    productEquiv
  have hFiber : ContMDiff coverModelWithCorners (𝓡 3) ∞
      (fun point : EffectiveCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hTo
  have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : EffectiveCover period hPeriod => point.time) :=
    contMDiff_snd.comp hTo
  have hPhase : ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point : EffectiveCover period hPeriod =>
        canonicalNormalRotationPhase period phase point.time) :=
    (canonicalNormalRotationPhase_contDiff period phase).contMDiff.comp hTime
  have hAngle : ContMDiff
      (𝓘(Real, Real).prod coverModelWithCorners) 𝓘(Real, Real) ∞
      (fun input : Real × EffectiveCover period hPeriod =>
        input.1 * canonicalNormalRotationPhase period phase input.2.time) :=
    contMDiff_fst.mul (hPhase.comp contMDiff_snd)
  have hSphere := (sphereNormalRotationFlow_contMDiff axis).comp
    (hAngle.prodMk (hFiber.comp contMDiff_snd))
  have hProduct := hSphere.prodMk (hTime.comp contMDiff_snd)
  exact hInv.comp hProduct

/-- The phased flow commutes with every integer deck transformation. -/
theorem coverPhasedNormalRotationFlow_deck_commutes
    (axis : Fin 3) (phase : Fin 2) (winding : Int)
    (input : Real × EffectiveCover period hPeriod) :
    winding +ᵥ coverPhasedNormalRotationFlow period hPeriod axis phase input =
      coverPhasedNormalRotationFlow period hPeriod axis phase
        (input.1, winding +ᵥ input.2) := by
  apply MappingTorusCover.ext
  · change (sphereReflection ^ winding)
        (sphereNormalRotationFlow axis
          (input.1 * canonicalNormalRotationPhase period phase input.2.time,
            input.2.fiber)) =
      sphereNormalRotationFlow axis
        (input.1 * canonicalNormalRotationPhase period phase
            (input.2.time + (winding : Real) * period),
          (sphereReflection ^ winding) input.2.fiber)
    rw [sphereNormalRotationFlow_reflection_zpow_conjugates,
      canonicalNormalRotationPhase_add_winding period hPeriod]
    congr 2
    ring
  · simp [coverPhasedNormalRotationFlow]

private theorem coverPhasedNormalRotationFlow_add
    (axis : Fin 3) (phase : Fin 2) (first second : Real)
    (point : EffectiveCover period hPeriod) :
    coverPhasedNormalRotationFlow period hPeriod axis phase
        (first + second, point) =
      coverPhasedNormalRotationFlow period hPeriod axis phase
        (first, coverPhasedNormalRotationFlow period hPeriod axis phase
          (second, point)) := by
  apply MappingTorusCover.ext
  · change sphereNormalRotationFlow axis
        ((first + second) *
            canonicalNormalRotationPhase period phase point.time,
          point.fiber) =
      sphereNormalRotationFlow axis
        (first * canonicalNormalRotationPhase period phase point.time,
          sphereNormalRotationFlow axis
            (second * canonicalNormalRotationPhase period phase point.time,
              point.fiber))
    rw [show (first + second) *
        canonicalNormalRotationPhase period phase point.time =
      first * canonicalNormalRotationPhase period phase point.time +
        second * canonicalNormalRotationPhase period phase point.time by ring]
    exact sphereNormalRotationFlow_angle_add axis _ _ point.fiber
  · rfl

private theorem coverPhasedNormalRotationFlow_respects_orbit
    (axis : Fin 3) (phase : Fin 2) (parameter : Real)
    (first second : EffectiveCover period hPeriod)
    (hOrbit : AddAction.orbitRel Int (EffectiveCover period hPeriod)
      first second) :
    mappingTorusMk (sphereData period hPeriod)
        (coverPhasedNormalRotationFlow period hPeriod axis phase
          (parameter, first)) =
      mappingTorusMk (sphereData period hPeriod)
        (coverPhasedNormalRotationFlow period hPeriod axis phase
          (parameter, second)) := by
  have hProjection : mappingTorusMk (sphereData period hPeriod) first =
      mappingTorusMk (sphereData period hPeriod) second := Quotient.sound hOrbit
  obtain ⟨winding, hWinding⟩ :=
    (mappingTorusMk_eq_iff_exists_vadd
      (sphereData period hPeriod) first second).1 hProjection
  apply (mappingTorusMk_eq_iff_exists_vadd
    (sphereData period hPeriod) _ _).2
  refine ⟨winding, ?_⟩
  rw [coverPhasedNormalRotationFlow_deck_commutes]
  exact congrArg
    (fun point => coverPhasedNormalRotationFlow period hPeriod axis phase
      (parameter, point)) hWinding

/-- Genuine phased normal rotation on the mapping-torus quotient. -/
def phasedNormalRotationFlow
    (axis : Fin 3) (phase : Fin 2) (parameter : Real) :
    EffectiveQuotient period hPeriod → EffectiveQuotient period hPeriod :=
  Quotient.lift
    (fun point => mappingTorusMk (sphereData period hPeriod)
      (coverPhasedNormalRotationFlow period hPeriod axis phase
        (parameter, point)))
    (coverPhasedNormalRotationFlow_respects_orbit period hPeriod axis phase
      parameter)

@[simp]
theorem phasedNormalRotationFlow_mk
    (axis : Fin 3) (phase : Fin 2) (parameter : Real)
    (point : EffectiveCover period hPeriod) :
    phasedNormalRotationFlow period hPeriod axis phase parameter
        (mappingTorusMk (sphereData period hPeriod) point) =
      mappingTorusMk (sphereData period hPeriod)
        (coverPhasedNormalRotationFlow period hPeriod axis phase
          (parameter, point)) :=
  rfl

theorem phasedNormalRotationFlow_continuous
    (axis : Fin 3) (phase : Fin 2) (parameter : Real) :
    Continuous
      (phasedNormalRotationFlow period hPeriod axis phase parameter) := by
  apply Continuous.quotient_lift
  exact (mappingTorusMk_isCoveringMap
    (sphereData period hPeriod)).isLocalHomeomorph.continuous.comp
      ((coverPhasedNormalRotationFlow_contMDiff period hPeriod axis phase)
        |>.continuous.comp (continuous_const.prodMk continuous_id))

@[simp]
theorem phasedNormalRotationFlow_zero
    (axis : Fin 3) (phase : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    phasedNormalRotationFlow period hPeriod axis phase 0 point = point := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  rw [phasedNormalRotationFlow_mk, coverPhasedNormalRotationFlow_zero]

theorem phasedNormalRotationFlow_add
    (axis : Fin 3) (phase : Fin 2) (first second : Real)
    (point : EffectiveQuotient period hPeriod) :
    phasedNormalRotationFlow period hPeriod axis phase (first + second) point =
      phasedNormalRotationFlow period hPeriod axis phase first
        (phasedNormalRotationFlow period hPeriod axis phase second point) := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  rw [phasedNormalRotationFlow_mk, phasedNormalRotationFlow_mk,
    phasedNormalRotationFlow_mk, coverPhasedNormalRotationFlow_add]

private def phasedNormalRotationHomeomorph
    (axis : Fin 3) (phase : Fin 2) (parameter : Real) :
    EffectiveQuotient period hPeriod ≃ₜ EffectiveQuotient period hPeriod where
  toFun := phasedNormalRotationFlow period hPeriod axis phase parameter
  invFun := phasedNormalRotationFlow period hPeriod axis phase (-parameter)
  left_inv point := by
    rw [← phasedNormalRotationFlow_add]
    simp
  right_inv point := by
    rw [← phasedNormalRotationFlow_add]
    simp
  continuous_toFun := phasedNormalRotationFlow_continuous period hPeriod axis
    phase parameter
  continuous_invFun := phasedNormalRotationFlow_continuous period hPeriod axis
    phase (-parameter)

theorem phasedNormalRotationFlow_measurableEmbedding
    (axis : Fin 3) (phase : Fin 2) (parameter : Real) :
    MeasurableEmbedding
      (phasedNormalRotationFlow period hPeriod axis phase parameter) :=
  (phasedNormalRotationHomeomorph period hPeriod axis phase parameter
    ).measurableEmbedding

/-- Gate marker: all six phased normal rotations descend to complete
homeomorphic flows on the quotient. -/
theorem canonical_phased_normal_rotation_quotient_gate :
    ∀ (axis : Fin 3) (phase : Fin 2),
      (∀ point : EffectiveQuotient period hPeriod,
        phasedNormalRotationFlow period hPeriod axis phase 0 point = point) ∧
      (∀ parameter : Real,
        MeasurableEmbedding
          (phasedNormalRotationFlow period hPeriod axis phase parameter)) := by
  intro axis phase
  exact ⟨phasedNormalRotationFlow_zero period hPeriod axis phase,
    phasedNormalRotationFlow_measurableEmbedding period hPeriod axis phase⟩

end
end P0EFTJanusMappingTorusCanonicalPhasedNormalRotationQuotient4D
end JanusFormal
