import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusInvariantMeasureFlowIPP4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatGlobalZeroBoundaryIPP4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

/-!
# Canonical divergence-free LL frame on the fixed throat

This gate replaces the unrelated partition-of-unity generators by the three
canonical rotations of `S²` and the quotient-time generator.  The flows commute
with the identity throat deck action and preserve the intrinsic product
measure.  The old POU-specialized IPP statement remains unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff ENNReal BigOperators Pointwise InnerProductSpace
open MeasureTheory Bundle
open P0EFTJanusInvariantMeasureFlowIPP4D
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalThroatGeometricStokes4D
open P0EFTJanusMappingTorusCanonicalThroatGlobalZeroBoundaryIPP4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EuclideanR3 := EuclideanSpace Real (Fin 3)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR3) 1

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance canonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-! ## Round-sphere rotations and measure preservation -/

private def euclideanRotation
    (axis : Fin 3) (angle : Real) (point : EuclideanR3) : EuclideanR3 :=
  (EuclideanSpace.equiv (Fin 3) Real).symm <|
    match axis with
    | 0 => ![(EuclideanSpace.equiv (Fin 3) Real point) 0,
        Real.cos angle * (EuclideanSpace.equiv (Fin 3) Real point) 1 -
          Real.sin angle * (EuclideanSpace.equiv (Fin 3) Real point) 2,
        Real.sin angle * (EuclideanSpace.equiv (Fin 3) Real point) 1 +
          Real.cos angle * (EuclideanSpace.equiv (Fin 3) Real point) 2]
    | 1 => ![Real.cos angle * (EuclideanSpace.equiv (Fin 3) Real point) 0 +
          Real.sin angle * (EuclideanSpace.equiv (Fin 3) Real point) 2,
        (EuclideanSpace.equiv (Fin 3) Real point) 1,
        -Real.sin angle * (EuclideanSpace.equiv (Fin 3) Real point) 0 +
          Real.cos angle * (EuclideanSpace.equiv (Fin 3) Real point) 2]
    | 2 => ![Real.cos angle * (EuclideanSpace.equiv (Fin 3) Real point) 0 -
          Real.sin angle * (EuclideanSpace.equiv (Fin 3) Real point) 1,
        Real.sin angle * (EuclideanSpace.equiv (Fin 3) Real point) 0 +
          Real.cos angle * (EuclideanSpace.equiv (Fin 3) Real point) 1,
        (EuclideanSpace.equiv (Fin 3) Real point) 2]

private theorem euclideanRotation_add
    (axis : Fin 3) (angle : Real) (first second : EuclideanR3) :
    euclideanRotation axis angle (first + second) =
      euclideanRotation axis angle first + euclideanRotation axis angle second := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [euclideanRotation] <;> ring

private theorem euclideanRotation_smul
    (axis : Fin 3) (angle scalar : Real) (point : EuclideanR3) :
    euclideanRotation axis angle (scalar • point) =
      scalar • euclideanRotation axis angle point := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [euclideanRotation] <;> ring

private theorem euclideanRotation_angle_add
    (axis : Fin 3) (first second : Real) (point : EuclideanR3) :
    euclideanRotation axis (first + second) point =
      euclideanRotation axis first (euclideanRotation axis second point) := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [euclideanRotation, Real.sin_add, Real.cos_add] <;> ring

private theorem euclideanRotation_norm_sq
    (axis : Fin 3) (angle : Real) (point : EuclideanR3) :
    ‖euclideanRotation axis angle point‖ ^ 2 = ‖point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  fin_cases axis <;>
    simp [euclideanRotation, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq angle]

private theorem euclideanRotation_norm
    (axis : Fin 3) (angle : Real) (point : EuclideanR3) :
    ‖euclideanRotation axis angle point‖ = ‖point‖ := by
  nlinarith [euclideanRotation_norm_sq axis angle point,
    norm_nonneg (euclideanRotation axis angle point), norm_nonneg point]

private def euclideanRotationLinearIsometry
    (axis : Fin 3) (angle : Real) : EuclideanR3 →ₗᵢ[Real] EuclideanR3 where
  toFun := euclideanRotation axis angle
  map_add' := euclideanRotation_add axis angle
  map_smul' := euclideanRotation_smul axis angle
  norm_map' := euclideanRotation_norm axis angle

private def euclideanRotationLinearIsometryEquiv
    (axis : Fin 3) (angle : Real) : EuclideanR3 ≃ₗᵢ[Real] EuclideanR3 :=
  LinearIsometryEquiv.ofSurjective
    (euclideanRotationLinearIsometry axis angle)
    ((euclideanRotationLinearIsometry axis angle).toLinearMap
      |>.surjective_of_injective
        (euclideanRotationLinearIsometry axis angle).injective)

def standardSphereRotation
    (axis : Fin 3) (angle : Real) (point : StandardSphere) :
    StandardSphere :=
  ⟨euclideanRotationLinearIsometryEquiv axis angle point.1, by
    rw [Metric.mem_sphere, dist_zero_right,
      LinearIsometryEquiv.norm_map]
    simpa [Metric.mem_sphere, dist_zero_right] using point.2⟩

theorem standardSphereRotation_continuous (axis : Fin 3) (angle : Real) :
    Continuous (standardSphereRotation axis angle) :=
  ((euclideanRotationLinearIsometryEquiv axis angle).continuous.comp
    continuous_subtype_val).subtype_mk _

private theorem standardSphereRotation_cone_preimage
    (axis : Fin 3) (angle : Real) (s : Set StandardSphere) :
    (euclideanRotationLinearIsometryEquiv axis angle) ⁻¹'
        (Ioo (0 : Real) 1 •
          ((fun point : StandardSphere => (point : EuclideanR3)) '' s)) =
      Ioo (0 : Real) 1 •
        ((fun point : StandardSphere => (point : EuclideanR3)) ''
          (standardSphereRotation axis angle ⁻¹' s)) := by
  ext point
  constructor
  · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, hPoint⟩
    let inverseDirection : StandardSphere :=
      ⟨(euclideanRotationLinearIsometryEquiv axis angle).symm direction.1, by
        rw [Metric.mem_sphere, dist_zero_right,
          LinearIsometryEquiv.norm_map]
        simpa [Metric.mem_sphere, dist_zero_right] using direction.2⟩
    refine ⟨scalar, hScalar, inverseDirection, ?_, ?_⟩
    · refine ⟨inverseDirection, ?_, rfl⟩
      simpa [standardSphereRotation, inverseDirection] using hDirection
    · have hInverse := congrArg
        (euclideanRotationLinearIsometryEquiv axis angle).symm hPoint
      simpa [inverseDirection] using hInverse
  · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, rfl⟩
    refine ⟨scalar, hScalar,
      (standardSphereRotation axis angle direction : EuclideanR3), ?_, ?_⟩
    · exact ⟨standardSphereRotation axis angle direction, hDirection, rfl⟩
    · simp [standardSphereRotation, map_smul]

private theorem measurableSet_standardSphere_cone {s : Set StandardSphere}
    (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : Real) 1 •
      ((fun point : StandardSphere => (point : EuclideanR3)) '' s)) := by
  let radialUpper : Set (Ioi (0 : Real)) :=
    Iio ⟨1, mem_Ioi.2 one_pos⟩
  have hCone :
      Ioo (0 : Real) 1 •
          ((fun point : StandardSphere => (point : EuclideanR3)) '' s) =
        (Subtype.val ∘ (homeomorphUnitSphereProd EuclideanR3).symm) ''
          (s ×ˢ radialUpper) := by
    ext point
    constructor
    · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, rfl⟩
      refine ⟨(direction, ⟨scalar, hScalar.1⟩), ⟨hDirection, hScalar.2⟩, ?_⟩
      simp [Function.comp_apply]
    · rintro ⟨⟨direction, scalar⟩, ⟨hDirection, hScalar⟩, rfl⟩
      refine ⟨scalar.1, ⟨scalar.2, hScalar⟩, direction.1,
        ⟨direction, hDirection, rfl⟩, ?_⟩
      simp [Function.comp_apply]
  rw [hCone]
  have hEmbedding : MeasurableEmbedding
      (Subtype.val ∘ (homeomorphUnitSphereProd EuclideanR3).symm) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton (0 : EuclideanR3)).compl).comp
        (homeomorphUnitSphereProd EuclideanR3).symm.measurableEmbedding
  exact hEmbedding.measurableSet_image.mpr (hs.prod measurableSet_Iio)

theorem standardSphereRotation_measurePreserving
    (axis : Fin 3) (angle : Real) :
    MeasurePreserving (standardSphereRotation axis angle)
      (volume : Measure EuclideanR3).toSphere
      (volume : Measure EuclideanR3).toSphere := by
  refine ⟨(standardSphereRotation_continuous axis angle).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply
    (standardSphereRotation_continuous axis angle).measurable hs]
  rw [(volume : Measure EuclideanR3).toSphere_apply' hs,
    (volume : Measure EuclideanR3).toSphere_apply'
      ((standardSphereRotation_continuous axis angle).measurable hs)]
  rw [← standardSphereRotation_cone_preimage axis angle]
  have hAmbient := LinearIsometryEquiv.measurePreserving
    (euclideanRotationLinearIsometryEquiv axis angle)
  rw [← Measure.map_apply hAmbient.measurable
    (measurableSet_standardSphere_cone hs)]
  rw [hAmbient.map_eq]

/-! ## Descent of spatial rotations to the throat quotient -/

private theorem throatCoverSpatialRotation_respects_orbit
    (axis : Fin 3) (angle : Real)
    (first second : EffectiveThroatCover period hPeriod)
    (hOrbit : AddAction.orbitRel Int
      (EffectiveThroatCover period hPeriod) first second) :
    mappingTorusMk (throatData period hPeriod)
        (throatCoverSpatialRotationFlow period hPeriod axis (angle, first)) =
      mappingTorusMk (throatData period hPeriod)
        (throatCoverSpatialRotationFlow period hPeriod axis
          (angle, second)) := by
  have hProjection : mappingTorusMk (throatData period hPeriod) first =
      mappingTorusMk (throatData period hPeriod) second :=
    Quotient.sound hOrbit
  obtain ⟨winding, hWinding⟩ :=
    (mappingTorusMk_eq_iff_exists_vadd
      (throatData period hPeriod) first second).1 hProjection
  apply (mappingTorusMk_eq_iff_exists_vadd
    (throatData period hPeriod) _ _).2
  refine ⟨winding, ?_⟩
  rw [throatCoverSpatialRotationFlow_deck_commutes]
  exact congrArg
    (fun point => throatCoverSpatialRotationFlow period hPeriod axis
      (angle, point)) hWinding

/-- The canonical spatial rotation flow on the actual throat quotient. -/
def throatSpatialRotationFlow
    (axis : Fin 3) (angle : Real) :
    EffectiveThroat period hPeriod → EffectiveThroat period hPeriod :=
  Quotient.lift
    (fun point => mappingTorusMk (throatData period hPeriod)
      (throatCoverSpatialRotationFlow period hPeriod axis (angle, point)))
    (throatCoverSpatialRotation_respects_orbit period hPeriod axis angle)

@[simp]
theorem throatSpatialRotationFlow_mk
    (axis : Fin 3) (angle : Real)
    (point : EffectiveThroatCover period hPeriod) :
    throatSpatialRotationFlow period hPeriod axis angle
        (mappingTorusMk (throatData period hPeriod) point) =
      mappingTorusMk (throatData period hPeriod)
        (throatCoverSpatialRotationFlow period hPeriod axis
          (angle, point)) :=
  rfl

theorem throatSpatialRotationFlow_continuous
    (axis : Fin 3) (angle : Real) :
    Continuous (throatSpatialRotationFlow period hPeriod axis angle) := by
  apply Continuous.quotient_lift
  exact (mappingTorusMk_isCoveringMap
    (throatData period hPeriod)).isLocalHomeomorph.continuous.comp
      ((throatCoverSpatialRotationFlow_contMDiff period hPeriod axis)
        |>.continuous.comp (continuous_const.prodMk continuous_id))

/-- The joint angle-point spatial rotation action on the throat quotient. -/
def throatJointSpatialRotationFlow
    (axis : Fin 3) (input : Real × EffectiveThroat period hPeriod) :
    EffectiveThroat period hPeriod :=
  throatSpatialRotationFlow period hPeriod axis input.1 input.2

theorem throatJointSpatialRotationFlow_contMDiff
    (axis : Fin 3) :
    ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ∞
      (throatJointSpatialRotationFlow period hPeriod axis) := by
  have hProjection := fixedThroat_projection_isLocalDiffeomorph period hPeriod
  have hLift : ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ∞
      (fun input : Real × EffectiveThroatCover period hPeriod ↦
        mappingTorusMk (throatData period hPeriod)
          (throatCoverSpatialRotationFlow period hPeriod axis input)) :=
    (hProjection.contMDiff.of_le (m := ∞) (by simp)).comp
      (throatCoverSpatialRotationFlow_contMDiff period hPeriod axis)
  rintro ⟨angle, quotientPoint⟩
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) quotientPoint
  have hLocal := hProjection anchor
  have hInput : ContMDiffAt
      (𝓘(Real, Real).prod throatCoverModelWithCorners)
      (𝓘(Real, Real).prod throatCoverModelWithCorners) ∞
      (fun input : Real × EffectiveThroat period hPeriod ↦
        (input.1, hLocal.localInverse input.2))
      (angle, mappingTorusMk (throatData period hPeriod) anchor) :=
    contMDiffAt_fst.prodMk
      ((hLocal.localInverse_contMDiffAt.of_le (m := ∞) (by simp)).comp
        (angle, mappingTorusMk (throatData period hPeriod) anchor)
        contMDiffAt_snd)
  have hLocalLift : ContMDiffAt
      (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ∞
      ((fun input : Real × EffectiveThroatCover period hPeriod ↦
          mappingTorusMk (throatData period hPeriod)
            (throatCoverSpatialRotationFlow period hPeriod axis input)) ∘
        (fun input : Real × EffectiveThroat period hPeriod ↦
          (input.1, hLocal.localInverse input.2)))
      (angle, mappingTorusMk (throatData period hPeriod) anchor) :=
    hLift.contMDiffAt.comp _ hInput
  apply hLocalLift.congr_of_eventuallyEq
  have hSnd : Filter.Tendsto
      (fun input : Real × EffectiveThroat period hPeriod ↦ input.2)
      (𝓝 (angle, mappingTorusMk (throatData period hPeriod) anchor))
      (𝓝 (mappingTorusMk (throatData period hPeriod) anchor)) :=
    continuousAt_snd
  have hRight := hLocal.localInverse_eventuallyEq_right.comp_tendsto hSnd
  filter_upwards [hRight] with input hInputRight
  change throatSpatialRotationFlow period hPeriod axis input.1 input.2 =
    mappingTorusMk (throatData period hPeriod)
      (throatCoverSpatialRotationFlow period hPeriod axis
        (input.1, hLocal.localInverse input.2))
  rw [← throatSpatialRotationFlow_mk]
  exact congrArg (throatSpatialRotationFlow period hPeriod axis input.1)
    hInputRight.symm

private theorem equatorial_rotation_to_standard
    (axis : Fin 3) (angle : Real) (point : EquatorialTwoSphere) :
    equatorialTwoSphereHomeomorph
        (equatorialSpatialRotationFlow axis (angle, point)) =
      standardSphereRotation axis angle
        (equatorialTwoSphereHomeomorph point) := by
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;> rfl

def canonicalLatitudeBaseRotation
    (axis : Fin 3) (angle : Real) (base : CanonicalLatitudeBase) :
    CanonicalLatitudeBase :=
  (standardSphereRotation axis angle base.1, base.2)

theorem canonicalLatitudeBaseRotation_measurePreserving
    (axis : Fin 3) (angle : Real) :
    MeasurePreserving (canonicalLatitudeBaseRotation axis angle)
      (canonicalLatitudeBaseMeasure period)
      (canonicalLatitudeBaseMeasure period) := by
  change MeasurePreserving
    (Prod.map (standardSphereRotation axis angle) id)
    (((volume : Measure EuclideanR3).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
    (((volume : Measure EuclideanR3).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact (standardSphereRotation_measurePreserving axis angle).prod
    (MeasurePreserving.id
      (volume.restrict (canonicalLatitudeTimeInterval period)))

theorem throatSpatialRotationFlow_canonicalLatitudeThroatMap
    (axis : Fin 3) (angle : Real) (base : CanonicalLatitudeBase) :
    throatSpatialRotationFlow period hPeriod axis angle
        (canonicalLatitudeThroatMap period hPeriod base) =
      canonicalLatitudeThroatMap period hPeriod
        (canonicalLatitudeBaseRotation axis angle base) := by
  rw [canonicalLatitudeThroatMap, throatSpatialRotationFlow_mk]
  apply congrArg (mappingTorusMk (throatData period hPeriod))
  apply MappingTorusCover.ext
  · change equatorialSpatialRotationFlow axis
        (angle, equatorialTwoSphereHomeomorph.symm base.1) =
      equatorialTwoSphereHomeomorph.symm
        (standardSphereRotation axis angle base.1)
    apply equatorialTwoSphereHomeomorph.injective
    rw [equatorial_rotation_to_standard]
    simp
  · rfl

theorem intrinsicCanonicalThroatVolumeMeasure_spatialRotation_measurePreserving
    (axis : Fin 3) (angle : Real) :
    MeasurePreserving (throatSpatialRotationFlow period hPeriod axis angle)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
  apply MeasurePreserving.of_semiconj
    ((canonicalLatitudeThroatMap_continuous period hPeriod).measurable.measurePreserving
      (canonicalLatitudeBaseMeasure period))
    (canonicalLatitudeBaseRotation_measurePreserving period axis angle)
  · intro base
    exact (throatSpatialRotationFlow_canonicalLatitudeThroatMap
      period hPeriod axis angle base).symm
  · exact (throatSpatialRotationFlow_continuous
      period hPeriod axis angle).measurable

/-! ## Quotient-time translations and measure preservation -/

private theorem canonicalLatitudeTimeInterval_eq_absFundamentalDomain :
    canonicalLatitudeTimeInterval period =
      Ioc (min 0 period) (min 0 period + |period|) := by
  unfold canonicalLatitudeTimeInterval
  congr 1
  by_cases hNonnegative : 0 ≤ period
  · simp [min_eq_left hNonnegative, max_eq_right hNonnegative,
      abs_of_nonneg hNonnegative]
  · have hNonpositive : period ≤ 0 := le_of_not_ge hNonnegative
    simp [min_eq_right hNonpositive, max_eq_left hNonpositive,
      abs_of_nonpos hNonpositive]

private def canonicalLatitudeTimeWrap
    (shift time : Real) : Real :=
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  (AddCircle.equivIoc |period| (min 0 period)
    ((time : AddCircle |period|) + (shift : AddCircle |period|))).1

def canonicalLatitudeBaseTimeTranslation
    (shift : Real) (base : CanonicalLatitudeBase) : CanonicalLatitudeBase :=
  (base.1, canonicalLatitudeTimeWrap period hPeriod shift base.2)

attribute [local instance] Measure.Subtype.measureSpace in
private theorem canonicalLatitudeTimeWrap_measurePreserving (shift : Real) :
    MeasurePreserving (canonicalLatitudeTimeWrap period hPeriod shift)
      (volume.restrict (canonicalLatitudeTimeInterval period))
      (volume.restrict (canonicalLatitudeTimeInterval period)) := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  rw [canonicalLatitudeTimeInterval_eq_absFundamentalDomain period]
  let circleShift : AddCircle |period| := shift
  have hMk := AddCircle.measurePreserving_mk |period| (min 0 period)
  have hAdd := measurePreserving_add_right
    (volume : Measure (AddCircle |period|)) circleShift
  have hIoc := AddCircle.measurePreserving_equivIoc
    (T := |period|) (a := min 0 period)
  have hCoe := measurePreserving_subtype_coe (μa := volume)
    (measurableSet_Ioc : MeasurableSet
      (Ioc (min 0 period) (min 0 period + |period|)))
  convert hCoe.comp (hIoc.comp (hAdd.comp hMk)) using 1
  funext time
  rfl

theorem canonicalLatitudeBaseTimeTranslation_measurePreserving
    (shift : Real) :
    MeasurePreserving (canonicalLatitudeBaseTimeTranslation period hPeriod shift)
      (canonicalLatitudeBaseMeasure period)
      (canonicalLatitudeBaseMeasure period) := by
  change MeasurePreserving
    (Prod.map id (canonicalLatitudeTimeWrap period hPeriod shift))
    (((volume : Measure EuclideanR3).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
    (((volume : Measure EuclideanR3).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact (MeasurePreserving.id
    ((volume : Measure EuclideanR3).toSphere)).prod
      (canonicalLatitudeTimeWrap_measurePreserving period hPeriod shift)

private theorem canonicalLatitudeTimeWrap_deck
    (shift time : Real) :
    ∃ winding : Int,
      canonicalLatitudeTimeWrap period hPeriod shift time +
          (winding : Real) * period =
        time + shift := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  let wrapped := canonicalLatitudeTimeWrap period hPeriod shift time
  have hCircle : (wrapped : AddCircle |period|) =
      ((time + shift : Real) : AddCircle |period|) := by
    change ((AddCircle.equivIoc |period| (min 0 period)
      ((time : AddCircle |period|) + (shift : AddCircle |period|))).1 :
        AddCircle |period|) = _
    rw [AddCircle.coe_equivIoc]
    rfl
  have hMem : wrapped - (time + shift) ∈
      AddSubgroup.zmultiples |period| :=
    QuotientAddGroup.eq_iff_sub_mem.mp hCircle
  obtain ⟨winding, hWinding⟩ :=
    AddSubgroup.mem_zmultiples_iff.mp hMem
  have hWinding' : (winding : Real) * |period| =
      wrapped - (time + shift) := by
    simpa only [zsmul_eq_mul] using hWinding
  clear hWinding
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · refine ⟨winding, ?_⟩
    rw [abs_of_neg hNegative] at hWinding'
    dsimp [wrapped] at hWinding' ⊢
    linarith
  · refine ⟨-winding, ?_⟩
    rw [abs_of_pos hPositive] at hWinding'
    dsimp [wrapped] at hWinding' ⊢
    push_cast
    linarith

theorem throatTimeFlow_canonicalLatitudeThroatMap_wrapped
    (shift : Real) (base : CanonicalLatitudeBase) :
    throatTimeFlow period hPeriod shift
        (canonicalLatitudeThroatMap period hPeriod base) =
      canonicalLatitudeThroatMap period hPeriod
        (canonicalLatitudeBaseTimeTranslation period hPeriod shift base) := by
  change throatTimeFlow period hPeriod shift
      (mappingTorusMk (throatData period hPeriod)
        (canonicalLatitudeAnchor period hPeriod base)) =
    mappingTorusMk (throatData period hPeriod)
      (canonicalLatitudeAnchor period hPeriod
        (canonicalLatitudeBaseTimeTranslation period hPeriod shift base))
  rw [throatTimeFlow_mk, mappingTorusMk_eq_iff_exists_vadd]
  obtain ⟨winding, hWinding⟩ :=
    canonicalLatitudeTimeWrap_deck period hPeriod shift base.2
  refine ⟨winding, ?_⟩
  apply MappingTorusCover.ext
  · change (Homeomorph.refl EquatorialTwoSphere ^ winding)
        (equatorialTwoSphereHomeomorph.symm base.1) =
      equatorialTwoSphereHomeomorph.symm base.1
    have hIdentity :
        (Homeomorph.refl EquatorialTwoSphere ^ winding) =
          (1 : Homeomorph EquatorialTwoSphere EquatorialTwoSphere) := by
      change (1 : Homeomorph EquatorialTwoSphere EquatorialTwoSphere) ^
        winding = 1
      simp
    rw [hIdentity]
    rfl
  · change canonicalLatitudeTimeWrap period hPeriod shift base.2 +
        (winding : Real) * period = base.2 + shift
    exact hWinding

theorem intrinsicCanonicalThroatVolumeMeasure_timeTranslation_measurePreserving
    (shift : Real) :
    MeasurePreserving (throatTimeFlow period hPeriod shift)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
  apply MeasurePreserving.of_semiconj
    ((canonicalLatitudeThroatMap_continuous period hPeriod).measurable.measurePreserving
      (canonicalLatitudeBaseMeasure period))
    (canonicalLatitudeBaseTimeTranslation_measurePreserving
      period hPeriod shift)
  · intro base
    exact (throatTimeFlow_canonicalLatitudeThroatMap_wrapped
      period hPeriod shift base).symm
  · exact (throatTimeFlow_contMDiff period hPeriod shift).continuous.measurable

/-! ## Smooth infinitesimal time generator -/

/-- The quotient time action with time and throat point as one input. -/
def throatJointTimeFlow
    (input : Real × EffectiveThroat period hPeriod) :
    EffectiveThroat period hPeriod :=
  throatTimeFlow period hPeriod input.1 input.2

theorem throatCoverJointTimeTranslation_contMDiff :
    ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ω
      (fun input : Real × EffectiveThroatCover period hPeriod =>
        coverTimeTranslation (throatData period hPeriod) input.1 input.2) := by
  let productEquiv := coverHomeomorphProd (throatData period hPeriod)
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ω productEquiv
  have hInv := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ω productEquiv
  have hFiber : ContMDiff throatCoverModelWithCorners (𝓡 2) ω
      (fun point : EffectiveThroatCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hTo
  have hTime : ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ω
      (fun point : EffectiveThroatCover period hPeriod => point.time) :=
    contMDiff_snd.comp hTo
  have hFiberInput :
      ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners) (𝓡 2) ω
        (fun input : Real × EffectiveThroatCover period hPeriod =>
          input.2.fiber) :=
    hFiber.comp contMDiff_snd
  have hTimeInput :
      ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners)
        𝓘(Real, Real) ω
        (fun input : Real × EffectiveThroatCover period hPeriod =>
          input.2.time + input.1) :=
    (hTime.comp contMDiff_snd).add contMDiff_fst
  exact hInv.comp (hFiberInput.prodMk hTimeInput)

theorem throatJointTimeFlow_contMDiff :
    ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ω
      (throatJointTimeFlow period hPeriod) := by
  have hProjection := fixedThroat_projection_isLocalDiffeomorph period hPeriod
  have hLift : ContMDiff (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ω
      (fun input : Real × EffectiveThroatCover period hPeriod =>
        mappingTorusMk (throatData period hPeriod)
          (coverTimeTranslation (throatData period hPeriod)
            input.1 input.2)) :=
    hProjection.contMDiff.comp
      (throatCoverJointTimeTranslation_contMDiff period hPeriod)
  rintro ⟨shift, quotientPoint⟩
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) quotientPoint
  have hLocal := hProjection anchor
  have hInput : ContMDiffAt
      (𝓘(Real, Real).prod throatCoverModelWithCorners)
      (𝓘(Real, Real).prod throatCoverModelWithCorners) ω
      (fun input : Real × EffectiveThroat period hPeriod =>
        (input.1, hLocal.localInverse input.2))
      (shift, mappingTorusMk (throatData period hPeriod) anchor) :=
    contMDiffAt_fst.prodMk
      (hLocal.localInverse_contMDiffAt.comp
        (shift, mappingTorusMk (throatData period hPeriod) anchor)
        contMDiffAt_snd)
  have hLocalLift : ContMDiffAt
      (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners ω
      ((fun input : Real × EffectiveThroatCover period hPeriod =>
          mappingTorusMk (throatData period hPeriod)
            (coverTimeTranslation (throatData period hPeriod)
              input.1 input.2)) ∘
        (fun input : Real × EffectiveThroat period hPeriod =>
          (input.1, hLocal.localInverse input.2)))
      (shift, mappingTorusMk (throatData period hPeriod) anchor) :=
    hLift.contMDiffAt.comp _ hInput
  apply hLocalLift.congr_of_eventuallyEq
  have hSnd : Filter.Tendsto
      (fun input : Real × EffectiveThroat period hPeriod => input.2)
      (𝓝 (shift, mappingTorusMk (throatData period hPeriod) anchor))
      (𝓝 (mappingTorusMk (throatData period hPeriod) anchor)) :=
    continuousAt_snd
  have hRight := hLocal.localInverse_eventuallyEq_right.comp_tendsto hSnd
  filter_upwards [hRight] with input hInputRight
  change throatTimeFlow period hPeriod input.1 input.2 =
    mappingTorusMk (throatData period hPeriod)
      (coverTimeTranslation (throatData period hPeriod)
        input.1 (hLocal.localInverse input.2))
  rw [← throatTimeFlow_mk]
  exact congrArg (throatTimeFlow period hPeriod input.1) hInputRight.symm

private def throatTimeFlowInputBundle
    (point : EffectiveThroat period hPeriod) :
    TangentBundle (𝓘(Real, Real).prod throatCoverModelWithCorners)
      (Real × EffectiveThroat period hPeriod) :=
  (equivTangentBundleProd 𝓘(Real, Real) Real throatCoverModelWithCorners
      (EffectiveThroat period hPeriod)).symm
    (⟨0, 1⟩, ⟨point, 0⟩)

private theorem throatTimeFlowInputBundle_contMDiff :
    ContMDiff throatCoverModelWithCorners
      (𝓘(Real, Real).prod throatCoverModelWithCorners).tangent ∞
      (throatTimeFlowInputBundle period hPeriod) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (M := Real) (M' := EffectiveThroat period hPeriod)).comp
  exact contMDiff_const.prodMk
    (Bundle.contMDiff_zeroSection (n := ∞) Real
      (TangentSpace throatCoverModelWithCorners :
        EffectiveThroat period hPeriod → Type _))

private def rawThroatTimeTranslationBundle
    (point : EffectiveThroat period hPeriod) :
    TangentBundle throatCoverModelWithCorners
      (EffectiveThroat period hPeriod) :=
  tangentMap (𝓘(Real, Real).prod throatCoverModelWithCorners)
    throatCoverModelWithCorners (throatJointTimeFlow period hPeriod)
    (throatTimeFlowInputBundle period hPeriod point)

private theorem rawThroatTimeTranslationBundle_contMDiff :
    ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners.tangent ∞
      (rawThroatTimeTranslationBundle period hPeriod) :=
  ((throatJointTimeFlow_contMDiff period hPeriod)
      |>.contMDiff_tangentMap (m := ∞) (by simp)).comp
    (throatTimeFlowInputBundle_contMDiff period hPeriod)

private theorem rawThroatTimeTranslationBundle_base
    (point : EffectiveThroat period hPeriod) :
    (rawThroatTimeTranslationBundle period hPeriod point).1 = point := by
  simpa [rawThroatTimeTranslationBundle, throatTimeFlowInputBundle, tangentMap,
    throatJointTimeFlow] using
      (throatTimeFlow_zero period hPeriod point)

/-- Velocity field generated by quotient time translation. -/
def throatTimeTranslationVelocity
    (point : EffectiveThroat period hPeriod) :
    TangentSpace throatCoverModelWithCorners point :=
  (rawThroatTimeTranslationBundle_base period hPeriod point) ▸
    (rawThroatTimeTranslationBundle period hPeriod point).2

private theorem throatTimeTranslationVelocity_bundle
    (point : EffectiveThroat period hPeriod) :
    (⟨point, throatTimeTranslationVelocity period hPeriod point⟩ :
        TangentBundle throatCoverModelWithCorners
          (EffectiveThroat period hPeriod)) =
      rawThroatTimeTranslationBundle period hPeriod point := by
  let raw := rawThroatTimeTranslationBundle period hPeriod point
  have hBase : raw.1 = point :=
    rawThroatTimeTranslationBundle_base period hPeriod point
  change (⟨point, hBase ▸ raw.2⟩ :
      TangentBundle throatCoverModelWithCorners
        (EffectiveThroat period hPeriod)) = raw
  rcases raw with ⟨base, vector⟩
  simp only at hBase
  subst base
  rfl

/-- Smooth tangent ghost generated by the quotient time action. -/
def throatTimeTranslationGhost :
    CInfinityThroatGhost period hPeriod where
  toFun := throatTimeTranslationVelocity period hPeriod
  contMDiff_toFun :=
    (rawThroatTimeTranslationBundle_contMDiff period hPeriod).congr
      (throatTimeTranslationVelocity_bundle period hPeriod)

private def throatTimeTranslationCurve
    (point : EffectiveThroat period hPeriod) (parameter : Real) :
    EffectiveThroat period hPeriod :=
  throatTimeFlow period hPeriod parameter point

private theorem throatTimeTranslationCurve_contMDiff
    (point : EffectiveThroat period hPeriod) :
    ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ω
      (throatTimeTranslationCurve period hPeriod point) := by
  exact ((throatJointTimeFlow_contMDiff period hPeriod).comp
    (contMDiff_id.prodMk contMDiff_const)).congr (fun _ => rfl)

private theorem rawThroatTimeTranslationBundle_eq_curve
    (point : EffectiveThroat period hPeriod) :
    rawThroatTimeTranslationBundle period hPeriod point =
      tangentMap 𝓘(Real, Real) throatCoverModelWithCorners
        (throatTimeTranslationCurve period hPeriod point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) := by
  let slice : Real → Real × EffectiveThroat period hPeriod :=
    fun parameter => (parameter, point)
  have hFlowAt : MDifferentiableAt
      (𝓘(Real, Real).prod throatCoverModelWithCorners)
      throatCoverModelWithCorners
      (throatJointTimeFlow period hPeriod) (0, point) :=
    (throatJointTimeFlow_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      (𝓘(Real, Real).prod throatCoverModelWithCorners) slice 0 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := 𝓘(Real, Real).prod throatCoverModelWithCorners)
    (I'' := throatCoverModelWithCorners)
    (f := slice) (g := throatJointTimeFlow period hPeriod)
    (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hFlowAt hSliceAt
  rw [tangentMap_prod_left] at hComp
  change tangentMap 𝓘(Real, Real) throatCoverModelWithCorners
      (throatTimeTranslationCurve period hPeriod point)
      (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) =
    rawThroatTimeTranslationBundle period hPeriod point at hComp
  exact hComp.symm

theorem throatTimeTranslationVelocity_eq_curve_mfderiv
    (point : EffectiveThroat period hPeriod) :
    throatTimeTranslationVelocity period hPeriod point =
      mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        (throatTimeTranslationCurve period hPeriod point) 0 1 := by
  apply (TotalSpace.mk_injective
    (F := ThroatCoverCoordinates) (b := point))
  calc
    (⟨point, throatTimeTranslationVelocity period hPeriod point⟩ :
        TangentBundle throatCoverModelWithCorners
          (EffectiveThroat period hPeriod)) =
      rawThroatTimeTranslationBundle period hPeriod point :=
        throatTimeTranslationVelocity_bundle period hPeriod point
    _ = tangentMap 𝓘(Real, Real) throatCoverModelWithCorners
        (throatTimeTranslationCurve period hPeriod point)
        (⟨0, 1⟩ : TangentBundle 𝓘(Real, Real) Real) :=
      rawThroatTimeTranslationBundle_eq_curve period hPeriod point
    _ = (⟨point,
          mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
            (throatTimeTranslationCurve period hPeriod point) 0 1⟩ :
        TangentBundle throatCoverModelWithCorners
          (EffectiveThroat period hPeriod)) := by
      simp [tangentMap, throatTimeTranslationCurve]
      exact HEq.rfl

private def throatCoverTimeTranslationCurve
    (point : EffectiveThroatCover period hPeriod) (parameter : Real) :
    EffectiveThroatCover period hPeriod :=
  coverTimeTranslation (throatData period hPeriod) parameter point

private theorem throatCoverTimeTranslationCurve_contMDiff
    (point : EffectiveThroatCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ω
      (throatCoverTimeTranslationCurve period hPeriod point) := by
  exact ((throatCoverJointTimeTranslation_contMDiff period hPeriod).comp
    (contMDiff_id.prodMk contMDiff_const)).congr (fun _ => rfl)

private def throatCoverTimeTranslationValue
    (point : EffectiveThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners point :=
  mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
    (throatCoverTimeTranslationCurve period hPeriod point) 0 1

private theorem throatProjection_mfderiv_time
    (point : EffectiveThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (throatData period hPeriod)) point
        (throatCoverTimeTranslationValue period hPeriod point) =
      throatTimeTranslationVelocity period hPeriod
        (mappingTorusMk (throatData period hPeriod) point) := by
  rw [throatTimeTranslationVelocity_eq_curve_mfderiv]
  have hProjectionAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners
      (mappingTorusMk (throatData period hPeriod)) point :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners
      (throatCoverTimeTranslationCurve period hPeriod point) 0 :=
    (throatCoverTimeTranslationCurve_contMDiff period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (I'' := throatCoverModelWithCorners)
    (f := throatCoverTimeTranslationCurve period hPeriod point)
    (g := mappingTorusMk (throatData period hPeriod))
    (x := (0 : Real)) (y := point)
    hProjectionAt hCurveAt (by simp [throatCoverTimeTranslationCurve])
    (1 : Real)
  calc
    _ = mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        ((mappingTorusMk (throatData period hPeriod)) ∘
          throatCoverTimeTranslationCurve period hPeriod point) 0 1 :=
      hComp.symm
    _ = mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        (throatTimeTranslationCurve period hPeriod
          (mappingTorusMk (throatData period hPeriod) point)) 0 1 := by
      congr 2

private theorem throatCoverRadialMap_mfderiv_time
    (point : EffectiveThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod) point
        (throatCoverTimeTranslationValue period hPeriod point) =
      throatCoverRadialMap period hPeriod point := by
  have hRadialAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, EuclideanR3) (throatCoverRadialMap period hPeriod) point :=
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners
      (throatCoverTimeTranslationCurve period hPeriod point) 0 :=
    (throatCoverTimeTranslationCurve_contMDiff period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (I'' := 𝓘(Real, EuclideanR3))
    (f := throatCoverTimeTranslationCurve period hPeriod point)
    (g := throatCoverRadialMap period hPeriod)
    (x := (0 : Real)) (y := point)
    hRadialAt hCurveAt (by simp [throatCoverTimeTranslationCurve])
    (1 : Real)
  have hMap :
      throatCoverRadialMap period hPeriod ∘
          throatCoverTimeTranslationCurve period hPeriod point =
        fun parameter : Real => Real.exp parameter •
          throatCoverRadialMap period hPeriod point := by
    funext parameter
    rw [Function.comp_apply, throatCoverRadialMap_apply,
      throatCoverRadialMap_apply]
    simp [throatCoverTimeTranslationCurve, coverTimeTranslation,
      Real.exp_add, smul_smul, mul_comm]
  have hDerivative : HasDerivAt
      (fun parameter : Real => Real.exp parameter •
        throatCoverRadialMap period hPeriod point)
      (throatCoverRadialMap period hPeriod point) 0 := by
    simpa using (Real.hasDerivAt_exp 0).smul_const
      (throatCoverRadialMap period hPeriod point)
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod ∘
          throatCoverTimeTranslationCurve period hPeriod point) 0 1 :=
      hComp.symm
    _ = _ := by
      rw [hMap, mfderiv_eq_fderiv]
      exact hDerivative.deriv

private def canonicalRotationVelocity
    (axis : Fin 3) (point : EuclideanR3) : EuclideanR3 :=
  (EuclideanSpace.equiv (Fin 3) Real).symm <|
    match axis with
    | 0 => ![0, -(EuclideanSpace.equiv (Fin 3) Real point) 2,
        (EuclideanSpace.equiv (Fin 3) Real point) 1]
    | 1 => ![(EuclideanSpace.equiv (Fin 3) Real point) 2, 0,
        -(EuclideanSpace.equiv (Fin 3) Real point) 0]
    | 2 => ![-(EuclideanSpace.equiv (Fin 3) Real point) 1,
        (EuclideanSpace.equiv (Fin 3) Real point) 0, 0]

private theorem canonicalRotationVelocity_smul
    (axis : Fin 3) (scalar : Real) (point : EuclideanR3) :
    canonicalRotationVelocity axis (scalar • point) =
      scalar • canonicalRotationVelocity axis point := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [canonicalRotationVelocity]

private theorem euclideanRotation_hasDerivAt_zero
    (axis : Fin 3) (point : EuclideanR3) :
    HasDerivAt (fun angle : Real => euclideanRotation axis angle point)
      (canonicalRotationVelocity axis point) 0 := by
  have hCosMul (value : Real) :
      HasDerivAt (fun angle : Real => Real.cos angle * value) 0 0 := by
    simpa using (Real.hasDerivAt_cos 0).mul_const value
  have hSinMul (value : Real) :
      HasDerivAt (fun angle : Real => Real.sin angle * value) value 0 := by
    simpa using (Real.hasDerivAt_sin 0).mul_const value
  have hCosSubSin (first second : Real) :
      HasDerivAt (fun angle : Real =>
        Real.cos angle * first - Real.sin angle * second) (-second) 0 := by
    refine (((hCosMul first).sub (hSinMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hSinAddCos (first second : Real) :
      HasDerivAt (fun angle : Real =>
        Real.sin angle * first + Real.cos angle * second) first 0 := by
    refine (((hSinMul first).add (hCosMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hCosAddSin (first second : Real) :
      HasDerivAt (fun angle : Real =>
        Real.cos angle * first + Real.sin angle * second) second 0 := by
    refine (((hCosMul first).add (hSinMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  have hNegSinAddCos (first second : Real) :
      HasDerivAt (fun angle : Real =>
        -(Real.sin angle * first) + Real.cos angle * second) (-first) 0 := by
    refine ((((hSinMul first).neg).add (hCosMul second)).congr_deriv (by simp))
      |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun _ => rfl
  apply (EuclideanSpace.equiv (Fin 3) Real).symm.hasFDerivAt.comp_hasDerivAt
  rw [hasDerivAt_pi]
  intro index
  fin_cases axis
  · fin_cases index
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        (hasDerivAt_const (x := (0 : Real))
          (c := (EuclideanSpace.equiv (Fin 3) Real point) 0))
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        hCosSubSin ((EuclideanSpace.equiv (Fin 3) Real point) 1)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        hSinAddCos ((EuclideanSpace.equiv (Fin 3) Real point) 1)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
  · fin_cases index
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        hCosAddSin ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        (hasDerivAt_const (x := (0 : Real))
          (c := (EuclideanSpace.equiv (Fin 3) Real point) 1))
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        hNegSinAddCos ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 2)
  · fin_cases index
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        hCosSubSin ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 1)
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        hSinAddCos ((EuclideanSpace.equiv (Fin 3) Real point) 0)
          ((EuclideanSpace.equiv (Fin 3) Real point) 1)
    · simpa [euclideanRotation, canonicalRotationVelocity] using
        (hasDerivAt_const (x := (0 : Real))
          (c := (EuclideanSpace.equiv (Fin 3) Real point) 2))

private theorem equatorial_rotation_to_euclidean
    (axis : Fin 3) (angle : Real) (point : EquatorialTwoSphere) :
    (equatorialTwoSphereHomeomorph
      (equatorialSpatialRotationFlow axis (angle, point))).1 =
      euclideanRotation axis angle
        (equatorialTwoSphereHomeomorph point).1 := by
  apply (EuclideanSpace.equiv (Fin 3) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;> rfl

private theorem equatorialSpatialRotationFlow_add
    (axis : Fin 3) (first second : Real) (point : EquatorialTwoSphere) :
    equatorialSpatialRotationFlow axis (first + second, point) =
      equatorialSpatialRotationFlow axis
        (first, equatorialSpatialRotationFlow axis (second, point)) := by
  apply equatorialTwoSphereHomeomorph.injective
  apply Subtype.ext
  rw [equatorial_rotation_to_euclidean,
    equatorial_rotation_to_euclidean,
    equatorial_rotation_to_euclidean]
  exact euclideanRotation_angle_add axis first second
    (equatorialTwoSphereHomeomorph point).1

private theorem throatCoverSpatialRotationFlow_add
    (axis : Fin 3) (first second : Real)
    (point : EffectiveThroatCover period hPeriod) :
    throatCoverSpatialRotationFlow period hPeriod axis (first + second, point) =
      throatCoverSpatialRotationFlow period hPeriod axis
        (first, throatCoverSpatialRotationFlow period hPeriod axis
          (second, point)) := by
  apply MappingTorusCover.ext
  · exact equatorialSpatialRotationFlow_add axis first second point.fiber
  · rfl

@[simp]
theorem throatSpatialRotationFlow_zero
    (axis : Fin 3) (point : EffectiveThroat period hPeriod) :
    throatSpatialRotationFlow period hPeriod axis 0 point = point := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) point
  rw [throatSpatialRotationFlow_mk,
    throatCoverSpatialRotationFlow_zero]

theorem throatSpatialRotationFlow_add
    (axis : Fin 3) (first second : Real)
    (point : EffectiveThroat period hPeriod) :
    throatSpatialRotationFlow period hPeriod axis (first + second) point =
      throatSpatialRotationFlow period hPeriod axis first
        (throatSpatialRotationFlow period hPeriod axis second point) := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) point
  rw [throatSpatialRotationFlow_mk, throatSpatialRotationFlow_mk,
    throatSpatialRotationFlow_mk, throatCoverSpatialRotationFlow_add]

theorem throatSpatialRotationFlow_injective
    (axis : Fin 3) (angle : Real) :
    Function.Injective (throatSpatialRotationFlow period hPeriod axis angle) := by
  intro first second hEqual
  have hInverse := congrArg
    (throatSpatialRotationFlow period hPeriod axis (-angle)) hEqual
  simpa only [← throatSpatialRotationFlow_add, neg_add_cancel,
    throatSpatialRotationFlow_zero] using hInverse

private def throatSpatialRotationHomeomorph
    (axis : Fin 3) (angle : Real) :
    EffectiveThroat period hPeriod ≃ₜ EffectiveThroat period hPeriod where
  toFun := throatSpatialRotationFlow period hPeriod axis angle
  invFun := throatSpatialRotationFlow period hPeriod axis (-angle)
  left_inv point := by
    rw [← throatSpatialRotationFlow_add]
    simp
  right_inv point := by
    rw [← throatSpatialRotationFlow_add]
    simp
  continuous_toFun := throatSpatialRotationFlow_continuous
    period hPeriod axis angle
  continuous_invFun := throatSpatialRotationFlow_continuous
    period hPeriod axis (-angle)

theorem throatSpatialRotationFlow_measurableEmbedding
    (axis : Fin 3) (angle : Real) :
    MeasurableEmbedding
      (throatSpatialRotationFlow period hPeriod axis angle) :=
  (throatSpatialRotationHomeomorph period hPeriod axis angle).measurableEmbedding

private def throatSpatialRotationCurve
    (axis : Fin 3) (point : EffectiveThroat period hPeriod)
    (angle : Real) : EffectiveThroat period hPeriod :=
  throatSpatialRotationFlow period hPeriod axis angle point

private theorem throatSpatialRotationCurve_contMDiff
    (axis : Fin 3) (point : EffectiveThroat period hPeriod) :
    ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ∞
      (throatSpatialRotationCurve period hPeriod axis point) := by
  exact ((throatJointSpatialRotationFlow_contMDiff period hPeriod axis).comp
    (contMDiff_id.prodMk contMDiff_const)).congr (fun _ => rfl)

private def canonicalThroatCoverSpatialRotationCurve
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod)
    (angle : Real) : EffectiveThroatCover period hPeriod :=
  throatCoverSpatialRotationFlow period hPeriod axis (angle, point)

private theorem canonicalThroatCoverSpatialRotationCurve_contMDiff
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ∞
      (canonicalThroatCoverSpatialRotationCurve
        period hPeriod axis point) :=
  (throatCoverSpatialRotationFlow_contMDiff period hPeriod axis).comp
    (contMDiff_id.prodMk contMDiff_const)

private theorem throatCoverSpatialRotationValue_eq_canonicalCurve_mfderiv
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    throatCoverSpatialRotationValue period hPeriod axis point =
      mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        (canonicalThroatCoverSpatialRotationCurve
          period hPeriod axis point) 0 1 := by
  exact throatCoverSpatialRotationValue_eq_curve_mfderiv
    period hPeriod axis point

private theorem throatCoverRadialMap_mfderiv_rotation
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod) point
        (throatCoverSpatialRotationValue period hPeriod axis point) =
      canonicalRotationVelocity axis
        (throatCoverRadialMap period hPeriod point) := by
  rw [throatCoverSpatialRotationValue_eq_canonicalCurve_mfderiv]
  have hRadialAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, EuclideanR3) (throatCoverRadialMap period hPeriod) point :=
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod point)
      |>.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners
      (canonicalThroatCoverSpatialRotationCurve
        period hPeriod axis point) 0 :=
    (canonicalThroatCoverSpatialRotationCurve_contMDiff
      period hPeriod axis point).mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (I'' := 𝓘(Real, EuclideanR3))
    (f := canonicalThroatCoverSpatialRotationCurve
      period hPeriod axis point)
    (g := throatCoverRadialMap period hPeriod)
    (x := (0 : Real)) (y := point)
    hRadialAt hCurveAt (by
      simp [canonicalThroatCoverSpatialRotationCurve]) (1 : Real)
  have hMap :
      throatCoverRadialMap period hPeriod ∘
          canonicalThroatCoverSpatialRotationCurve
            period hPeriod axis point =
        fun angle : Real => Real.exp point.time •
          euclideanRotation axis angle
            (equatorialTwoSphereHomeomorph point.fiber).1 := by
    funext angle
    rw [Function.comp_apply, throatCoverRadialMap_apply]
    change Real.exp point.time •
        (equatorialTwoSphereHomeomorph
          (equatorialSpatialRotationFlow axis
            (angle, point.fiber))).1 = _
    rw [equatorial_rotation_to_euclidean]
  have hDerivative : HasDerivAt
      (fun angle : Real => Real.exp point.time •
        euclideanRotation axis angle
          (equatorialTwoSphereHomeomorph point.fiber).1)
      (Real.exp point.time • canonicalRotationVelocity axis
        (equatorialTwoSphereHomeomorph point.fiber).1) 0 :=
    (euclideanRotation_hasDerivAt_zero axis
      (equatorialTwoSphereHomeomorph point.fiber).1).const_smul
        (Real.exp point.time)
  calc
    _ = mfderiv 𝓘(Real, Real) 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod ∘
          canonicalThroatCoverSpatialRotationCurve
            period hPeriod axis point) 0 1 := hComp.symm
    _ = Real.exp point.time • canonicalRotationVelocity axis
        (equatorialTwoSphereHomeomorph point.fiber).1 := by
      rw [hMap, mfderiv_eq_fderiv]
      exact hDerivative.deriv
    _ = _ := by
      rw [throatCoverRadialMap_apply, canonicalRotationVelocity_smul]

private def canonicalEuclideanGenerator
    (point : EuclideanR3) : Fin 4 → EuclideanR3 :=
  Fin.lastCases point (fun axis => canonicalRotationVelocity axis point)

private theorem canonicalEuclideanGenerator_spans
    (point : EuclideanR3) (hPoint : point ≠ 0) :
    Submodule.span Real (Set.range (canonicalEuclideanGenerator point)) = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro vector hVector
  have hOrthogonal (index : Fin 4) :
      ⟪vector, canonicalEuclideanGenerator point index⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal'
      (Submodule.span Real (Set.range (canonicalEuclideanGenerator point)))
      vector).mp hVector _
        (Submodule.subset_span (Set.mem_range_self index))
  have hRadial := hOrthogonal (Fin.last 3)
  have hRotationZero := hOrthogonal (Fin.castSucc (0 : Fin 3))
  have hRotationOne := hOrthogonal (Fin.castSucc (1 : Fin 3))
  have hRotationTwo := hOrthogonal (Fin.castSucc (2 : Fin 3))
  have hNorm : 0 < ⟪point, point⟫_ℝ := real_inner_self_pos.mpr hPoint
  simp only [canonicalEuclideanGenerator, Fin.lastCases_last] at hRadial
  simp only [canonicalEuclideanGenerator, Fin.lastCases_castSucc] at hRotationZero hRotationOne hRotationTwo
  simp [PiLp.inner_apply, canonicalRotationVelocity, Fin.sum_univ_succ] at hRadial hRotationZero hRotationOne hRotationTwo hNorm
  let a := point.ofLp 0
  let b := point.ofLp 1
  let c := point.ofLp 2
  let u := vector.ofLp 0
  let v := vector.ofLp 1
  let w := vector.ofLp 2
  have hRadial' : u * a + v * b + w * c = 0 := by
    dsimp [u, v, w, a, b, c]
    convert hRadial using 1 <;> ring
  have hRotationZero' : -(v * c) + w * b = 0 := by
    dsimp [u, v, w, a, b, c]
    convert hRotationZero using 1 <;> ring
  have hRotationOne' : u * c - w * a = 0 := by
    dsimp [u, v, w, a, b, c]
    convert hRotationOne using 1 <;> ring
  have hRotationTwo' : -(u * b) + v * a = 0 := by
    dsimp [u, v, w, a, b, c]
    convert hRotationTwo using 1 <;> ring
  have hNorm' : 0 < a * a + b * b + c * c := by
    rw [EuclideanSpace.real_norm_sq_eq] at hNorm
    simpa [a, b, c, Fin.sum_univ_succ, pow_two, add_assoc] using hNorm
  have hUScale : (a * a + b * b + c * c) * u = 0 := by
    calc
      _ = a * (u * a + v * b + w * c) -
          b * (-(u * b) + v * a) +
          c * (u * c - w * a) := by ring
      _ = 0 := by rw [hRadial', hRotationTwo', hRotationOne']; ring
  have hVScale : (a * a + b * b + c * c) * v = 0 := by
    calc
      _ = b * (u * a + v * b + w * c) +
          a * (-(u * b) + v * a) -
          c * (-(v * c) + w * b) := by ring
      _ = 0 := by rw [hRadial', hRotationTwo', hRotationZero']; ring
  have hWScale : (a * a + b * b + c * c) * w = 0 := by
    calc
      _ = c * (u * a + v * b + w * c) -
          a * (u * c - w * a) +
          b * (-(v * c) + w * b) := by ring
      _ = 0 := by rw [hRadial', hRotationOne', hRotationZero']; ring
  have hNormNe : a * a + b * b + c * c ≠ 0 := ne_of_gt hNorm'
  have hu : u = 0 := (mul_eq_zero.mp hUScale).resolve_left hNormNe
  have hv : v = 0 := (mul_eq_zero.mp hVScale).resolve_left hNormNe
  have hw : w = 0 := (mul_eq_zero.mp hWScale).resolve_left hNormNe
  apply PiLp.ext
  intro index
  fin_cases index
  · exact hu
  · exact hv
  · exact hw

private def canonicalThroatProjectionDerivativeEquiv
    (point : EffectiveThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners point ≃L[Real]
      TangentSpace throatCoverModelWithCorners
        (mappingTorusMk (throatData period hPeriod) point) :=
  (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
private theorem canonicalThroatProjectionDerivativeEquiv_coe
    (point : EffectiveThroatCover period hPeriod) :
    (canonicalThroatProjectionDerivativeEquiv period hPeriod point :
      TangentSpace throatCoverModelWithCorners point →L[Real]
        TangentSpace throatCoverModelWithCorners
          (mappingTorusMk (throatData period hPeriod) point)) =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (throatData period hPeriod)) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point

private def canonicalThroatRadialDerivativeEquiv
    (point : EffectiveThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners point ≃L[Real] EuclideanR3 :=
  (throatCoverRadialMap_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
private theorem canonicalThroatRadialDerivativeEquiv_coe
    (point : EffectiveThroatCover period hPeriod) :
    (canonicalThroatRadialDerivativeEquiv period hPeriod point :
      TangentSpace throatCoverModelWithCorners point →L[Real] EuclideanR3) =
      mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod)
      (by simp) point

private def canonicalQuotientRadialDerivativeEquiv
    (point : EffectiveThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners
        (mappingTorusMk (throatData period hPeriod) point) ≃L[Real]
      EuclideanR3 :=
  (canonicalThroatProjectionDerivativeEquiv period hPeriod point).symm.trans
    (canonicalThroatRadialDerivativeEquiv period hPeriod point)

private theorem canonicalQuotientRadialDerivativeEquiv_projection
    (point : EffectiveThroatCover period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    canonicalQuotientRadialDerivativeEquiv period hPeriod point
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (throatData period hPeriod)) point vector) =
      mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod) point vector := by
  change canonicalThroatRadialDerivativeEquiv period hPeriod point
      ((canonicalThroatProjectionDerivativeEquiv period hPeriod point).symm
        (canonicalThroatProjectionDerivativeEquiv period hPeriod point vector)) =
    canonicalThroatRadialDerivativeEquiv period hPeriod point vector
  simp

private theorem throatProjection_mfderiv_rotation
    (axis : Fin 3) (point : EffectiveThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (throatData period hPeriod)) point
        (throatCoverSpatialRotationValue period hPeriod axis point) =
      throatSpatialRotationGhost period hPeriod axis
        (mappingTorusMk (throatData period hPeriod) point) := by
  rw [throatSpatialRotationGhost,
    descendSmoothDeckEquivariantThroatCoverGhost_mk]
  rfl

private theorem throatSpatialRotationGhost_eq_curve_mfderiv
    (axis : Fin 3) (point : EffectiveThroat period hPeriod) :
    throatSpatialRotationGhost period hPeriod axis point =
      mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        (throatSpatialRotationCurve period hPeriod axis point) 0 1 := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) point
  rw [← throatProjection_mfderiv_rotation period hPeriod axis anchor]
  rw [throatCoverSpatialRotationValue_eq_canonicalCurve_mfderiv]
  have hProjectionAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners
      (mappingTorusMk (throatData period hPeriod)) anchor :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners
      (canonicalThroatCoverSpatialRotationCurve
        period hPeriod axis anchor) 0 :=
    (canonicalThroatCoverSpatialRotationCurve_contMDiff
      period hPeriod axis anchor).mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply_of_eq
    (I := 𝓘(Real, Real)) (I' := throatCoverModelWithCorners)
    (I'' := throatCoverModelWithCorners)
    (f := canonicalThroatCoverSpatialRotationCurve
      period hPeriod axis anchor)
    (g := mappingTorusMk (throatData period hPeriod))
    (x := (0 : Real)) (y := anchor)
    hProjectionAt hCurveAt
    (by simp [canonicalThroatCoverSpatialRotationCurve]) (1 : Real)
  calc
    _ = mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        ((mappingTorusMk (throatData period hPeriod)) ∘
          canonicalThroatCoverSpatialRotationCurve
            period hPeriod axis anchor) 0 1 := hComp.symm
    _ = mfderiv 𝓘(Real, Real) throatCoverModelWithCorners
        (throatSpatialRotationCurve period hPeriod axis
          (mappingTorusMk (throatData period hPeriod) anchor)) 0 1 := by
      congr 2

private theorem smoothThroatField_hasDerivAt_along_curve_zero
    {Fiber : Type*} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [ContinuousSMul Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (curve : Real → EffectiveThroat period hPeriod)
    (hCurve : ContMDiff 𝓘(Real, Real) throatCoverModelWithCorners ∞ curve) :
    HasDerivAt (fun parameter => field (curve parameter))
      (mvfderiv throatCoverModelWithCorners field.toFun (curve 0)
        (mfderiv 𝓘(Real, Real) throatCoverModelWithCorners curve 0 1)) 0 := by
  have hCurveAt : MDifferentiableAt 𝓘(Real, Real)
      throatCoverModelWithCorners curve 0 :=
    hCurve.mdifferentiableAt (by simp)
  have hFieldAt : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, Fiber) field.toFun (curve 0) :=
    field.contMDiff_toFun.mdifferentiableAt (by simp)
  have hComp := hFieldAt.hasMFDerivAt.comp 0 hCurveAt.hasMFDerivAt
  have hCompF : HasFDerivAt (field.toFun ∘ curve)
      ((mfderiv throatCoverModelWithCorners 𝓘(Real, Fiber)
        field.toFun (curve 0)).comp
          (mfderiv 𝓘(Real, Real) throatCoverModelWithCorners curve 0)) 0 :=
    hComp.hasFDerivAt
  have hDeriv : HasDerivAt (field.toFun ∘ curve)
      (((mfderiv throatCoverModelWithCorners 𝓘(Real, Fiber)
        field.toFun (curve 0)).comp
          (mfderiv 𝓘(Real, Real) throatCoverModelWithCorners curve 0)) 1) 0 :=
    hasFDerivAt_iff_hasDerivAt.mp hCompF
  change HasDerivAt (field.toFun ∘ curve) _ 0
  convert hDeriv using 1
  simp only [ContinuousLinearMap.comp_apply]
  rfl

private def canonicalThroatGeneratorAt
    (point : EffectiveThroat period hPeriod) :
    Fin 4 → TangentSpace throatCoverModelWithCorners point :=
  Fin.lastCases (throatTimeTranslationGhost period hPeriod point)
    (fun axis => throatSpatialRotationGhost period hPeriod axis point)

@[simp]
private theorem canonicalThroatGeneratorAt_last
    (point : EffectiveThroat period hPeriod) :
    canonicalThroatGeneratorAt period hPeriod point (Fin.last 3) =
      throatTimeTranslationGhost period hPeriod point := by
  exact Fin.lastCases_last

@[simp]
private theorem canonicalThroatGeneratorAt_castSucc
    (point : EffectiveThroat period hPeriod) (axis : Fin 3) :
    canonicalThroatGeneratorAt period hPeriod point (Fin.castSucc axis) =
      throatSpatialRotationGhost period hPeriod axis point := by
  exact Fin.lastCases_castSucc axis

private theorem canonicalQuotientRadialDerivativeEquiv_generator
    (point : EffectiveThroatCover period hPeriod) (index : Fin 4) :
    canonicalQuotientRadialDerivativeEquiv period hPeriod point
        (canonicalThroatGeneratorAt period hPeriod
          (mappingTorusMk (throatData period hPeriod) point) index) =
      canonicalEuclideanGenerator
        (throatCoverRadialMap period hPeriod point) index := by
  refine Fin.lastCases ?_ (fun axis => ?_) index
  · simp only [canonicalThroatGeneratorAt, canonicalEuclideanGenerator,
      Fin.lastCases_last]
    change canonicalQuotientRadialDerivativeEquiv period hPeriod point
        (throatTimeTranslationVelocity period hPeriod
          (mappingTorusMk (throatData period hPeriod) point)) = _
    rw [← throatProjection_mfderiv_time period hPeriod point]
    exact (canonicalQuotientRadialDerivativeEquiv_projection
      period hPeriod point _).trans
        (throatCoverRadialMap_mfderiv_time period hPeriod point)
  · simp only [canonicalThroatGeneratorAt, canonicalEuclideanGenerator,
      Fin.lastCases_castSucc]
    rw [← throatProjection_mfderiv_rotation period hPeriod axis point]
    exact (canonicalQuotientRadialDerivativeEquiv_projection
      period hPeriod point _).trans
        (throatCoverRadialMap_mfderiv_rotation period hPeriod axis point)

private theorem throatCoverRadialMap_ne_zero
    (point : EffectiveThroatCover period hPeriod) :
    throatCoverRadialMap period hPeriod point ≠ 0 := by
  rw [throatCoverRadialMap_apply]
  exact smul_ne_zero (Real.exp_ne_zero point.time)
    (ne_zero_of_mem_unit_sphere
      (equatorialTwoSphereHomeomorph point.fiber))

private theorem canonicalThroatGeneratorAt_spans_mk
    (point : EffectiveThroatCover period hPeriod) :
    Submodule.span Real
        (Set.range (canonicalThroatGeneratorAt period hPeriod
          (mappingTorusMk (throatData period hPeriod) point))) = ⊤ := by
  let generator := canonicalThroatGeneratorAt period hPeriod
    (mappingTorusMk (throatData period hPeriod) point)
  let euclideanGenerator := canonicalEuclideanGenerator
    (throatCoverRadialMap period hPeriod point)
  let derivative := canonicalQuotientRadialDerivativeEquiv period hPeriod point
  have hImage : derivative.toLinearMap '' Set.range generator =
      Set.range euclideanGenerator := by
    ext vector
    constructor
    · rintro ⟨_, ⟨index, rfl⟩, rfl⟩
      exact ⟨index, (canonicalQuotientRadialDerivativeEquiv_generator
        period hPeriod point index).symm⟩
    · rintro ⟨index, rfl⟩
      exact ⟨generator index, ⟨index, rfl⟩,
        canonicalQuotientRadialDerivativeEquiv_generator
          period hPeriod point index⟩
  have hMapped :
      (Submodule.span Real (Set.range generator)).map derivative.toLinearMap = ⊤ := by
    rw [Submodule.map_span, hImage]
    exact canonicalEuclideanGenerator_spans
      (throatCoverRadialMap period hPeriod point)
      (throatCoverRadialMap_ne_zero period hPeriod point)
  apply top_unique
  intro vector _
  have hImage : derivative vector ∈
      (Submodule.span Real (Set.range generator)).map derivative.toLinearMap := by
    rw [hMapped]
    exact Submodule.mem_top
  rcases hImage with ⟨preimage, hPreimage, hEqual⟩
  have hPreimageEq : preimage = vector := derivative.injective hEqual
  simpa [hPreimageEq] using hPreimage

/-- The quotient-time generator and the three spatial rotations form a smooth
finite generating frame on the fixed throat. -/
def canonicalDivergenceFreeLLFrame :
    SmoothThroatGeneratingFrame period hPeriod where
  count := 4
  vectorAt := canonicalThroatGeneratorAt period hPeriod
  spansAt := by
    intro point
    obtain ⟨anchor, rfl⟩ :=
      mappingTorusMk_surjective (throatData period hPeriod) point
    exact canonicalThroatGeneratorAt_spans_mk period hPeriod anchor
  contMDiff_vector := by
    intro index
    refine Fin.lastCases ?_ (fun axis => ?_) index
    · convert (throatTimeTranslationGhost period hPeriod).contMDiff_toFun using 1 <;>
        rfl
    · convert (throatSpatialRotationGhost period hPeriod axis).contMDiff_toFun using 1 <;>
        try rfl
      funext point
      simp [canonicalThroatGeneratorAt]
      change (throatSpatialRotationGhost period hPeriod axis).toFun point =
        (throatSpatialRotationGhost period hPeriod axis).toFun point
      rfl

private def throatTimeFlowHomeomorph
    (shift : Real) :
    EffectiveThroat period hPeriod ≃ₜ EffectiveThroat period hPeriod where
  toFun := throatTimeFlow period hPeriod shift
  invFun := throatTimeFlow period hPeriod (-shift)
  left_inv point := by
    rw [← throatTimeFlow_add]
    simp
  right_inv point := by
    rw [← throatTimeFlow_add]
    simp
  continuous_toFun :=
    (throatTimeFlow_contMDiff period hPeriod shift).continuous
  continuous_invFun :=
    (throatTimeFlow_contMDiff period hPeriod (-shift)).continuous

private theorem throatTimeFlow_measurableEmbedding
    (shift : Real) :
    MeasurableEmbedding (throatTimeFlow period hPeriod shift) :=
  (throatTimeFlowHomeomorph period hPeriod shift).measurableEmbedding

private theorem smoothThroatField_timeFlow_hasDerivAt_zero
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    HasDerivAt
      (fun parameter => field (throatTimeFlow period hPeriod parameter point))
      (throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field point
        (Fin.last 3)) 0 := by
  rw [throatFrameDerivative_eq_mvfderiv]
  have hVector :
      (canonicalDivergenceFreeLLFrame period hPeriod).vectorAt point
          (Fin.last 3) =
        throatTimeTranslationVelocity period hPeriod point := by
    change canonicalThroatGeneratorAt period hPeriod point (Fin.last 3) = _
    rw [canonicalThroatGeneratorAt_last]
    rfl
  rw [hVector]
  have h := smoothThroatField_hasDerivAt_along_curve_zero
    period hPeriod field (throatTimeTranslationCurve period hPeriod point)
      ((throatTimeTranslationCurve_contMDiff period hPeriod point).of_le
        (by simp))
  have hCurveZero :
      throatTimeTranslationCurve period hPeriod point 0 = point :=
    throatTimeFlow_zero period hPeriod point
  have hVelocity := throatTimeTranslationVelocity_eq_curve_mfderiv
    period hPeriod point
  rw [hCurveZero] at h
  rw [hCurveZero] at hVelocity
  rw [← hVelocity] at h
  change HasDerivAt
    (fun parameter => field (throatTimeFlow period hPeriod parameter point))
    _ 0 at h
  exact h

private theorem smoothThroatField_rotationFlow_hasDerivAt_zero
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (axis : Fin 3) (point : EffectiveThroat period hPeriod) :
    HasDerivAt
      (fun parameter => field
        (throatSpatialRotationFlow period hPeriod axis parameter point))
      (throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field point
        (Fin.castSucc axis)) 0 := by
  rw [throatFrameDerivative_eq_mvfderiv]
  have hVector :
      (canonicalDivergenceFreeLLFrame period hPeriod).vectorAt point
          (Fin.castSucc axis) =
        throatSpatialRotationGhost period hPeriod axis point := by
    change canonicalThroatGeneratorAt period hPeriod point
      (Fin.castSucc axis) = _
    exact canonicalThroatGeneratorAt_castSucc period hPeriod point axis
  rw [hVector]
  have h := smoothThroatField_hasDerivAt_along_curve_zero
    period hPeriod field
      (throatSpatialRotationCurve period hPeriod axis point)
      (throatSpatialRotationCurve_contMDiff period hPeriod axis point)
  have hCurveZero :
      throatSpatialRotationCurve period hPeriod axis point 0 = point :=
    throatSpatialRotationFlow_zero period hPeriod axis point
  have hVelocity := throatSpatialRotationGhost_eq_curve_mfderiv
    period hPeriod axis point
  rw [hCurveZero] at h
  rw [hCurveZero] at hVelocity
  rw [← hVelocity] at h
  change HasDerivAt
    (fun parameter => field
      (throatSpatialRotationFlow period hPeriod axis parameter point))
    _ 0 at h
  exact h

private theorem smoothThroatField_timeFlow_hasDerivAt
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (parameter : Real) (point : EffectiveThroat period hPeriod) :
    HasDerivAt
      (fun t => field (throatTimeFlow period hPeriod t point))
      (throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field
        (throatTimeFlow period hPeriod parameter point) (Fin.last 3))
      parameter := by
  have hZero := smoothThroatField_timeFlow_hasDerivAt_zero
    period hPeriod field (throatTimeFlow period hPeriod parameter point)
  have hShift : HasDerivAt (fun t : Real => t - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have hComp := hZero.scomp_of_eq parameter hShift (by simp)
  have hEventually :
      (fun t => field (throatTimeFlow period hPeriod t point)) =ᶠ[𝓝 parameter]
        ((fun offset => field
          (throatTimeFlow period hPeriod offset
            (throatTimeFlow period hPeriod parameter point))) ∘
          fun t => t - parameter) := by
    filter_upwards with t
    simp only [Function.comp_apply]
    rw [← throatTimeFlow_add]
    congr 2
    ring
  exact (hComp.congr_of_eventuallyEq hEventually).congr_deriv
    (one_smul Real _)

private theorem smoothThroatField_rotationFlow_hasDerivAt
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (axis : Fin 3) (parameter : Real)
    (point : EffectiveThroat period hPeriod) :
    HasDerivAt
      (fun t => field
        (throatSpatialRotationFlow period hPeriod axis t point))
      (throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) field
        (throatSpatialRotationFlow period hPeriod axis parameter point)
        (Fin.castSucc axis)) parameter := by
  have hZero := smoothThroatField_rotationFlow_hasDerivAt_zero
    period hPeriod field axis
      (throatSpatialRotationFlow period hPeriod axis parameter point)
  have hShift : HasDerivAt (fun t : Real => t - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have hComp := hZero.scomp_of_eq parameter hShift (by simp)
  have hEventually :
      (fun t => field
        (throatSpatialRotationFlow period hPeriod axis t point)) =ᶠ[𝓝 parameter]
        ((fun offset => field
          (throatSpatialRotationFlow period hPeriod axis offset
            (throatSpatialRotationFlow period hPeriod axis parameter point))) ∘
          fun t => t - parameter) := by
    filter_upwards with t
    simp only [Function.comp_apply]
    rw [← throatSpatialRotationFlow_add]
    congr 2
    ring
  exact (hComp.congr_of_eventuallyEq hEventually).congr_deriv
    (one_smul Real _)

private theorem canonicalTimeGenerator_integral_inner_derivative_eq_neg
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    (∫ point, inner Real (first point)
      (throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) second point
        (Fin.last 3))
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      -∫ point, inner Real
        (throatFrameDerivative period hPeriod LLFieldFiber
          (canonicalDivergenceFreeLLFrame period hPeriod) first point
          (Fin.last 3))
        (second point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  refine integral_inner_derivative_eq_neg
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (throatTimeFlow period hPeriod)
    ?_ ?_ ?_ ?_
    first.toFun second.toFun
    (fun point => throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) first point
      (Fin.last 3))
    (fun point => throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) second point
      (Fin.last 3))
    ?_ ?_ ?_ ?_ ?_ ?_
  · change Continuous (throatJointTimeFlow period hPeriod)
    exact (throatJointTimeFlow_contMDiff period hPeriod).continuous
  · exact throatTimeFlow_zero period hPeriod
  · exact throatTimeFlow_measurableEmbedding period hPeriod
  · exact
      intrinsicCanonicalThroatVolumeMeasure_timeTranslation_measurePreserving
        period hPeriod
  · exact first.contMDiff_toFun.continuous
  · exact second.contMDiff_toFun.continuous
  · exact (continuous_apply (Fin.last 3)).comp
      (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) first).continuous
  · exact (continuous_apply (Fin.last 3)).comp
      (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) second).continuous
  · exact smoothThroatField_timeFlow_hasDerivAt period hPeriod first
  · exact smoothThroatField_timeFlow_hasDerivAt period hPeriod second

private theorem canonicalRotationGenerator_integral_inner_derivative_eq_neg
    (axis : Fin 3)
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    (∫ point, inner Real (first point)
      (throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) second point
        (Fin.castSucc axis))
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      -∫ point, inner Real
        (throatFrameDerivative period hPeriod LLFieldFiber
          (canonicalDivergenceFreeLLFrame period hPeriod) first point
          (Fin.castSucc axis))
        (second point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  refine integral_inner_derivative_eq_neg
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (throatSpatialRotationFlow period hPeriod axis)
    ?_ ?_ ?_ ?_
    first.toFun second.toFun
    (fun point => throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) first point
      (Fin.castSucc axis))
    (fun point => throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) second point
      (Fin.castSucc axis))
    ?_ ?_ ?_ ?_ ?_ ?_
  · change Continuous (throatJointSpatialRotationFlow period hPeriod axis)
    exact (throatJointSpatialRotationFlow_contMDiff
      period hPeriod axis).continuous
  · exact throatSpatialRotationFlow_zero period hPeriod axis
  · exact throatSpatialRotationFlow_measurableEmbedding period hPeriod axis
  · exact
      intrinsicCanonicalThroatVolumeMeasure_spatialRotation_measurePreserving
        period hPeriod axis
  · exact first.contMDiff_toFun.continuous
  · exact second.contMDiff_toFun.continuous
  · exact (continuous_apply (Fin.castSucc axis)).comp
      (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) first).continuous
  · exact (continuous_apply (Fin.castSucc axis)).comp
      (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) second).continuous
  · exact smoothThroatField_rotationFlow_hasDerivAt
      period hPeriod first axis
  · exact smoothThroatField_rotationFlow_hasDerivAt
      period hPeriod second axis

private theorem canonicalGenerator_integral_inner_derivative_eq_neg
    (index : Fin 4)
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    (∫ point, inner Real (first point)
      (throatFrameDerivative period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod) second point index)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      -∫ point, inner Real
        (throatFrameDerivative period hPeriod LLFieldFiber
          (canonicalDivergenceFreeLLFrame period hPeriod) first point index)
        (second point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  refine Fin.lastCases ?_ (fun axis => ?_) index
  · exact canonicalTimeGenerator_integral_inner_derivative_eq_neg
      period hPeriod first second
  · exact canonicalRotationGenerator_integral_inner_derivative_eq_neg
      period hPeriod axis first second

/-- Raw global integration by parts for the canonical divergence-free frame. -/
theorem canonicalDivergenceFreeLLFrame_rawGlobalIPP
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod))
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    globalDifferentialLLFluxFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      ∫ point, inner Real
        (strongDifferentialLLEulerField period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) regularity
          fields point)
        (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let flux := scalarWeightedLLFrameFlux period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
  let derivative := fun
      (field : SmoothThroatField period hPeriod LLFieldFiber)
      (point : EffectiveThroat period hPeriod)
      (index : Fin (canonicalDivergenceFreeLLFrame period hPeriod).count) =>
    throatFrameDerivative period hPeriod LLFieldFiber
      (canonicalDivergenceFreeLLFrame period hPeriod) field point index
  let kinetic := fun
      (index : Fin (canonicalDivergenceFreeLLFrame period hPeriod).count)
      (point : EffectiveThroat period hPeriod) =>
    inner Real (flux index point) (derivative direction point index)
  let divergence := fun
      (index : Fin (canonicalDivergenceFreeLLFrame period hPeriod).count)
      (point : EffectiveThroat period hPeriod) =>
    inner Real (derivative (flux index) point index) (direction point)
  let algebraic := fun point : EffectiveThroat period hPeriod =>
    2 * fields.llMeasure point *
      inner Real (fields.llField point) (direction point)
  have hKinetic
      (index : Fin (canonicalDivergenceFreeLLFrame period hPeriod).count) :
      Integrable (kinetic index) mu := by
    apply Continuous.integrable_of_hasCompactSupport _
      (HasCompactSupport.of_compactSpace _)
    exact (flux index).contMDiff_toFun.continuous.inner
      ((continuous_apply index).comp
        (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
          (canonicalDivergenceFreeLLFrame period hPeriod) direction).continuous)
  have hDivergence
      (index : Fin (canonicalDivergenceFreeLLFrame period hPeriod).count) :
      Integrable (divergence index) mu := by
    apply Continuous.integrable_of_hasCompactSupport _
      (HasCompactSupport.of_compactSpace _)
    exact ((continuous_apply index).comp
      (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (flux index)).continuous).inner
      direction.contMDiff_toFun.continuous
  have hAlgebraic : Integrable algebraic mu := by
    apply Continuous.integrable_of_hasCompactSupport _
      (HasCompactSupport.of_compactSpace _)
    exact ((continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
      (fields.llField.contMDiff_toFun.continuous.inner
        direction.contMDiff_toFun.continuous))
  have hKineticSum : Integrable
      (fun point => ∑ index, kinetic index point) mu :=
    integrable_finsetSum Finset.univ (fun index _ => hKinetic index)
  have hDivergenceSum : Integrable
      (fun point => ∑ index, divergence index point) mu :=
    integrable_finsetSum Finset.univ (fun index _ => hDivergence index)
  have hWeakPoint (point : EffectiveThroat period hPeriod) :
      differentialLLFluxFirstVariationDensity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields direction point =
        (∑ index, kinetic index point) + algebraic point := by
    unfold differentialLLFluxFirstVariationDensity algebraic kinetic flux
      derivative
    rw [scalarWeightedLLFrameFlux_contracts_to_action period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
      direction point]
  have hStrongPoint (point : EffectiveThroat period hPeriod) :
      inner Real
          (strongDifferentialLLEulerField period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
            point)
          (direction point) =
        -(∑ index, divergence index point) + algebraic point := by
    rw [strongDifferentialLLEulerField_pairing period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
      direction point]
    have hLaplacian :
        scalarWeightedLLFrameLaplacian period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
            point =
          ∑ index, derivative (flux index) point index := by
      exact throatFrameDivergence_apply period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) regularity
        (scalarWeightedLLFrameFlux period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields)
        point
    rw [hLaplacian]
    simp only [sum_inner]
    rfl
  unfold globalDifferentialLLFluxFirstVariation
  calc
    (∫ point, differentialLLFluxFirstVariationDensity period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields direction point
        ∂mu) =
        ∫ point, (∑ index, kinetic index point) + algebraic point
          ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact hWeakPoint point
    _ = (∑ index, ∫ point, kinetic index point ∂mu) +
        ∫ point, algebraic point ∂mu := by
      rw [integral_add hKineticSum hAlgebraic,
        integral_finsetSum Finset.univ (fun index _ => hKinetic index)]
    _ = (∑ index, -∫ point, divergence index point ∂mu) +
        ∫ point, algebraic point ∂mu := by
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      change Fin 4 at index
      exact canonicalGenerator_integral_inner_derivative_eq_neg
        period hPeriod index (flux index) direction
    _ = ∫ point, -(∑ index, divergence index point) +
        algebraic point ∂mu := by
      symm
      calc
        (∫ point, -(∑ index, divergence index point) +
            algebraic point ∂mu) =
            (∫ point, -(∑ index, divergence index point) ∂mu) +
              ∫ point, algebraic point ∂mu :=
          integral_add hDivergenceSum.neg hAlgebraic
        _ = -(∫ point, ∑ index, divergence index point ∂mu) +
              ∫ point, algebraic point ∂mu := by rw [integral_neg]
        _ = -(∑ index, ∫ point, divergence index point ∂mu) +
              ∫ point, algebraic point ∂mu := by
          rw [integral_finsetSum Finset.univ
            (fun index _ => hDivergence index)]
        _ = (∑ index, -∫ point, divergence index point ∂mu) +
              ∫ point, algebraic point ∂mu := by
          rw [Finset.sum_neg_distrib]
    _ = ∫ point, inner Real
        (strongDifferentialLLEulerField period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
          point) (direction point) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with point
      exact (hStrongPoint point).symm

/-- The canonical frame supplies the unconditional PT-averaged global IPP. -/
theorem canonicalDivergenceFreeLLFrame_globalIPP
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) :
    CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) fields regularity := by
  intro direction
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let rawStrong := strongDifferentialLLEulerField period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) regularity fields
  let ptRawStrong := strongDifferentialLLEulerField period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) regularity
    (llPTPullback period hPeriod fields)
  let pulledPtRaw := differentialLLFluxDirectionPT period hPeriod ptRawStrong
  have hChangeVariable :
      (∫ point, inner Real (ptRawStrong point)
          (differentialLLFluxDirectionPT period hPeriod direction point) ∂mu) =
        ∫ point, inner Real (pulledPtRaw point) (direction point) ∂mu := by
    have hMap :=
      (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
        period hPeriod).integral_comp'
        (fun point => inner Real (ptRawStrong point)
          (differentialLLFluxDirectionPT period hPeriod direction point))
    calc
      (∫ point, inner Real (ptRawStrong point)
          (differentialLLFluxDirectionPT period hPeriod direction point) ∂mu) =
          ∫ point, inner Real
            (ptRawStrong (fixedThroatPT period hPeriod point))
            (differentialLLFluxDirectionPT period hPeriod direction
              (fixedThroatPT period hPeriod point)) ∂mu := hMap.symm
      _ = ∫ point, inner Real (pulledPtRaw point) (direction point) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with point
        change inner Real
            (ptRawStrong (fixedThroatPT period hPeriod point))
            (direction (fixedThroatPT period hPeriod
              (fixedThroatPT period hPeriod point))) =
          inner Real
            (ptRawStrong (fixedThroatPT period hPeriod point))
            (direction point)
        rw [fixedThroatPT_involutive]
  have hRawIntegrable : Integrable
      (fun point => inner Real (rawStrong point) (direction point)) mu :=
    (rawStrong.contMDiff_toFun.continuous.inner
      direction.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPulledIntegrable : Integrable
      (fun point => inner Real (pulledPtRaw point) (direction point)) mu :=
    (pulledPtRaw.contMDiff_toFun.continuous.inner
      direction.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  unfold globalPTSymmetricDifferentialLLFluxFirstVariation
  rw [canonicalDivergenceFreeLLFrame_rawGlobalIPP period hPeriod fields
      regularity direction,
    canonicalDivergenceFreeLLFrame_rawGlobalIPP period hPeriod
      (llPTPullback period hPeriod fields) regularity
      (differentialLLFluxDirectionPT period hPeriod direction),
    hChangeVariable]
  rw [← integral_add hRawIntegrable hPulledIntegrable,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [ptSymmetricStrongDifferentialLLEulerField_apply,
    inner_add_left, real_inner_smul_left]
  rfl

end

end P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
end JanusFormal
