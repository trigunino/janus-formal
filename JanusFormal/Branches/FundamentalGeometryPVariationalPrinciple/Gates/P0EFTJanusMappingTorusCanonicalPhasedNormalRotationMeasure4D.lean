import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhasedNormalRotationQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

/-! # Canonical volume invariance of phased normal rotations -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhasedNormalRotationMeasure4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff Pointwise
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationFlow4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

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

/-! ## Orthogonal rotations preserve Mathlib's sphere measure -/

private def euclideanNormalRotation
    (axis : Fin 3) (angle : Real) (point : EuclideanR4) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm
    (ambientNormalRotationFlow axis
      (angle, EuclideanSpace.equiv (Fin 4) Real point))

private theorem euclideanNormalRotation_add
    (axis : Fin 3) (angle : Real) (first second : EuclideanR4) :
    euclideanNormalRotation axis angle (first + second) =
      euclideanNormalRotation axis angle first +
        euclideanNormalRotation axis angle second := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [euclideanNormalRotation, ambientNormalRotationFlow] <;> ring

private theorem euclideanNormalRotation_smul
    (axis : Fin 3) (angle scalar : Real) (point : EuclideanR4) :
    euclideanNormalRotation axis angle (scalar • point) =
      scalar • euclideanNormalRotation axis angle point := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [euclideanNormalRotation, ambientNormalRotationFlow] <;> ring

private theorem euclideanNormalRotation_norm
    (axis : Fin 3) (angle : Real) (point : EuclideanR4) :
    ‖euclideanNormalRotation axis angle point‖ = ‖point‖ := by
  have hSquare : ‖euclideanNormalRotation axis angle point‖ ^ 2 =
      ‖point‖ ^ 2 := by
    calc
      ‖euclideanNormalRotation axis angle point‖ ^ 2 =
          radiusSquared (ambientNormalRotationFlow axis
            (angle, EuclideanSpace.equiv (Fin 4) Real point)) := by
            exact euclidean_norm_sq_eq_radiusSquared _
      _ = radiusSquared (EuclideanSpace.equiv (Fin 4) Real point) :=
        ambientNormalRotationFlow_preserves_radius axis _
      _ = ‖point‖ ^ 2 := by
        rw [← euclidean_norm_sq_eq_radiusSquared]
        simp
  nlinarith [norm_nonneg (euclideanNormalRotation axis angle point),
    norm_nonneg point]

private def euclideanNormalRotationLinearIsometry
    (axis : Fin 3) (angle : Real) : EuclideanR4 →ₗᵢ[Real] EuclideanR4 where
  toFun := euclideanNormalRotation axis angle
  map_add' := euclideanNormalRotation_add axis angle
  map_smul' := euclideanNormalRotation_smul axis angle
  norm_map' := euclideanNormalRotation_norm axis angle

private def euclideanNormalRotationLinearIsometryEquiv
    (axis : Fin 3) (angle : Real) : EuclideanR4 ≃ₗᵢ[Real] EuclideanR4 :=
  LinearIsometryEquiv.ofSurjective
    (euclideanNormalRotationLinearIsometry axis angle)
    ((euclideanNormalRotationLinearIsometry axis angle).toLinearMap
      |>.surjective_of_injective
        (euclideanNormalRotationLinearIsometry axis angle).injective)

def standardSphereLinearIsometry
    (equiv : EuclideanR4 ≃ₗᵢ[Real] EuclideanR4)
    (point : StandardSphere) : StandardSphere :=
  ⟨equiv point.1, by
    rw [Metric.mem_sphere, dist_zero_right, equiv.norm_map]
    simpa [Metric.mem_sphere, dist_zero_right] using point.2⟩

private theorem standardSphereLinearIsometry_continuous
    (equiv : EuclideanR4 ≃ₗᵢ[Real] EuclideanR4) :
    Continuous (standardSphereLinearIsometry equiv) :=
  (equiv.continuous.comp continuous_subtype_val).subtype_mk _

private theorem standardSphereLinearIsometry_cone_preimage
    (equiv : EuclideanR4 ≃ₗᵢ[Real] EuclideanR4)
    (s : Set StandardSphere) :
    equiv ⁻¹'
        (Ioo (0 : Real) 1 •
          ((fun point : StandardSphere => (point : EuclideanR4)) '' s)) =
      Ioo (0 : Real) 1 •
        ((fun point : StandardSphere => (point : EuclideanR4)) ''
          (standardSphereLinearIsometry equiv ⁻¹' s)) := by
  ext point
  constructor
  · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, hPoint⟩
    let inverseDirection : StandardSphere :=
      ⟨equiv.symm direction.1, by
        rw [Metric.mem_sphere, dist_zero_right, equiv.symm.norm_map]
        simpa [Metric.mem_sphere, dist_zero_right] using direction.2⟩
    refine ⟨scalar, hScalar, inverseDirection, ?_, ?_⟩
    · refine ⟨inverseDirection, ?_, rfl⟩
      simpa [standardSphereLinearIsometry, inverseDirection] using hDirection
    · have hInverse := congrArg equiv.symm hPoint
      simpa [inverseDirection] using hInverse
  · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, rfl⟩
    refine ⟨scalar, hScalar,
      (standardSphereLinearIsometry equiv direction : EuclideanR4), ?_, ?_⟩
    · exact ⟨standardSphereLinearIsometry equiv direction, hDirection, rfl⟩
    · simp [standardSphereLinearIsometry, map_smul]

private theorem measurableSet_standardSphere_cone
    {s : Set StandardSphere} (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : Real) 1 •
      ((fun point : StandardSphere => (point : EuclideanR4)) '' s)) := by
  let radialUpper : Set (Ioi (0 : Real)) :=
    Iio ⟨1, mem_Ioi.2 one_pos⟩
  have hCone :
      Ioo (0 : Real) 1 •
          ((fun point : StandardSphere => (point : EuclideanR4)) '' s) =
        (Subtype.val ∘ (homeomorphUnitSphereProd EuclideanR4).symm) ''
          (s ×ˢ radialUpper) := by
    ext point
    constructor
    · rintro ⟨scalar, hScalar, _, ⟨direction, hDirection, rfl⟩, rfl⟩
      refine ⟨(direction, ⟨scalar, hScalar.1⟩),
        ⟨hDirection, hScalar.2⟩, ?_⟩
      simp [Function.comp_apply]
    · rintro ⟨⟨direction, scalar⟩, ⟨hDirection, hScalar⟩, rfl⟩
      refine ⟨scalar.1, ⟨scalar.2, hScalar⟩, direction.1,
        ⟨direction, hDirection, rfl⟩, ?_⟩
      simp [Function.comp_apply]
  rw [hCone]
  have hEmbedding : MeasurableEmbedding
      (Subtype.val ∘ (homeomorphUnitSphereProd EuclideanR4).symm) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton (0 : EuclideanR4)).compl).comp
        (homeomorphUnitSphereProd EuclideanR4).symm.measurableEmbedding
  exact hEmbedding.measurableSet_image.mpr (hs.prod measurableSet_Iio)

theorem standardSphereLinearIsometry_measurePreserving
    (equiv : EuclideanR4 ≃ₗᵢ[Real] EuclideanR4) :
    MeasurePreserving (standardSphereLinearIsometry equiv)
      (volume : Measure EuclideanR4).toSphere
      (volume : Measure EuclideanR4).toSphere := by
  refine ⟨(standardSphereLinearIsometry_continuous equiv).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply
    (standardSphereLinearIsometry_continuous equiv).measurable hs]
  rw [(volume : Measure EuclideanR4).toSphere_apply' hs,
    (volume : Measure EuclideanR4).toSphere_apply'
      ((standardSphereLinearIsometry_continuous equiv).measurable hs)]
  rw [← standardSphereLinearIsometry_cone_preimage equiv s]
  have hAmbient := LinearIsometryEquiv.measurePreserving equiv
  rw [← Measure.map_apply hAmbient.measurable
    (measurableSet_standardSphere_cone hs)]
  rw [hAmbient.map_eq]

/-! ## Time-modulated rotations on the canonical spacetime base -/

private def standardNormalRotation
    (axis : Fin 3) (angle : Real) (point : StandardSphere) : StandardSphere :=
  unitThreeSphereHomeomorph
    (sphereNormalRotationFlow axis
      (angle, unitThreeSphereHomeomorph.symm point))

private theorem standardNormalRotation_eq_linear
    (axis : Fin 3) (angle : Real) :
    standardNormalRotation axis angle =
      standardSphereLinearIsometry
        (euclideanNormalRotationLinearIsometryEquiv axis angle) := by
  funext point
  apply Subtype.ext
  change (EuclideanSpace.equiv (Fin 4) Real).symm
      (ambientNormalRotationFlow axis
        (angle, EuclideanSpace.equiv (Fin 4) Real point.1)) = _
  simp [standardSphereLinearIsometry,
    euclideanNormalRotationLinearIsometryEquiv,
    euclideanNormalRotationLinearIsometry,
    euclideanNormalRotation]

private theorem standardNormalRotation_measurePreserving
    (axis : Fin 3) (angle : Real) :
    MeasurePreserving (standardNormalRotation axis angle)
      (volume : Measure EuclideanR4).toSphere
      (volume : Measure EuclideanR4).toSphere := by
  rw [standardNormalRotation_eq_linear axis angle]
  exact standardSphereLinearIsometry_measurePreserving _

private theorem standardJointNormalRotation_continuous (axis : Fin 3) :
    Continuous (fun input : Real × StandardSphere =>
      standardNormalRotation axis input.1 input.2) := by
  unfold standardNormalRotation
  exact unitThreeSphereHomeomorph.continuous.comp
    ((sphereNormalRotationFlow_contMDiff axis).continuous.comp
      (continuous_fst.prodMk
        (unitThreeSphereHomeomorph.symm.continuous.comp continuous_snd)))

/-- Rotation of the sphere factor by a time-dependent antiperiodic angle. -/
def spacetimeBasePhasedNormalRotation
    (axis : Fin 3) (phase : Fin 2) (parameter : Real)
    (base : SpacetimeBase) : SpacetimeBase :=
  (standardNormalRotation axis
      (parameter * canonicalNormalRotationPhase period phase base.2) base.1,
    base.2)

theorem spacetimeBasePhasedNormalRotation_measurePreserving
    (axis : Fin 3) (phase : Fin 2) (parameter : Real) :
    MeasurePreserving
      (spacetimeBasePhasedNormalRotation period axis phase parameter)
      (spacetimeBaseMeasure period) (spacetimeBaseMeasure period) := by
  let sphereMeasure := (volume : Measure EuclideanR4).toSphere
  let timeMeasure := volume.restrict (canonicalLatitudeTimeInterval period)
  have hAngle : Continuous (fun input : Real × StandardSphere =>
      parameter * canonicalNormalRotationPhase period phase input.1) :=
    continuous_const.mul
      ((canonicalNormalRotationPhase_contDiff period phase).continuous.comp
        continuous_fst)
  have hJoint : Measurable (Function.uncurry fun time point =>
      standardNormalRotation axis
        (parameter * canonicalNormalRotationPhase period phase time) point) := by
    exact ((standardJointNormalRotation_continuous axis).comp
      (hAngle.prodMk continuous_snd)).measurable
  have hSkew : MeasurePreserving
      (fun input : Real × StandardSphere =>
        (input.1, standardNormalRotation axis
          (parameter * canonicalNormalRotationPhase period phase input.1)
          input.2))
      (timeMeasure.prod sphereMeasure) (timeMeasure.prod sphereMeasure) := by
    refine MeasurePreserving.skew_product
      (μa := timeMeasure) (μb := timeMeasure)
      (μc := sphereMeasure) (μd := sphereMeasure)
      (f := id)
      (g := fun time point => standardNormalRotation axis
        (parameter * canonicalNormalRotationPhase period phase time) point)
      (MeasurePreserving.id timeMeasure) hJoint ?_
    exact Filter.Eventually.of_forall fun time =>
      (standardNormalRotation_measurePreserving axis
        (parameter * canonicalNormalRotationPhase period phase time)).map_eq
  change MeasurePreserving
    (fun base : StandardSphere × Real =>
      (standardNormalRotation axis
          (parameter * canonicalNormalRotationPhase period phase base.2)
          base.1,
        base.2))
    (sphereMeasure.prod timeMeasure) (sphereMeasure.prod timeMeasure)
  have hSwapForward : MeasurePreserving Prod.swap
      (sphereMeasure.prod timeMeasure) (timeMeasure.prod sphereMeasure) :=
    Measure.measurePreserving_swap
  have hSwapBackward : MeasurePreserving Prod.swap
      (timeMeasure.prod sphereMeasure) (sphereMeasure.prod timeMeasure) :=
    Measure.measurePreserving_swap
  simpa [Function.comp_def] using
    (hSwapBackward.comp (hSkew.comp hSwapForward))

theorem phasedNormalRotationFlow_spacetimeFundamentalDomainMap
    (axis : Fin 3) (phase : Fin 2) (parameter : Real)
    (base : SpacetimeBase) :
    phasedNormalRotationFlow period hPeriod axis phase parameter
        (spacetimeFundamentalDomainMap period hPeriod base) =
      spacetimeFundamentalDomainMap period hPeriod
        (spacetimeBasePhasedNormalRotation period axis phase parameter base) := by
  unfold spacetimeFundamentalDomainMap spacetimeBasePhasedNormalRotation
  rw [phasedNormalRotationFlow_mk]
  congr 1

/-- Every phased normal rotation preserves the actual canonical Lorentz
volume on the quotient. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_phasedNormalRotation_measurePreserving
    (axis : Fin 3) (phase : Fin 2) (parameter : Real) :
    MeasurePreserving
      (phasedNormalRotationFlow period hPeriod axis phase parameter)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_spacetimeBase]
  apply MeasurePreserving.of_semiconj
    ((spacetimeFundamentalDomainMap_continuous period hPeriod).measurable
      |>.measurePreserving (spacetimeBaseMeasure period))
    (spacetimeBasePhasedNormalRotation_measurePreserving period axis phase
      parameter)
  · intro base
    exact (phasedNormalRotationFlow_spacetimeFundamentalDomainMap period hPeriod
      axis phase parameter base).symm
  · exact (phasedNormalRotationFlow_continuous period hPeriod axis phase
      parameter).measurable

/-- Gate marker for all six canonical-volume-preserving normal flows. -/
theorem canonical_phased_normal_rotation_measure_gate :
    ∀ (axis : Fin 3) (phase : Fin 2) (parameter : Real),
      MeasurePreserving
        (phasedNormalRotationFlow period hPeriod axis phase parameter)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_phasedNormalRotation_measurePreserving
    period hPeriod

end
end P0EFTJanusMappingTorusCanonicalPhasedNormalRotationMeasure4D
end JanusFormal
