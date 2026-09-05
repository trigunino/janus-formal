import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalSpatialRotationQuotient4D

/-! # Canonical volume invariance of spatial rotations -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalSpatialRotationMeasure4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D
open P0EFTJanusMappingTorusCanonicalPhasedNormalRotationMeasure4D
open P0EFTJanusMappingTorusCanonicalSpatialRotationQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
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

private def euclideanSpatialRotation
    (axis : Fin 3) (angle : Real) (point : EuclideanR4) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm
    (ambientSpatialRotationFlow axis
      (angle, EuclideanSpace.equiv (Fin 4) Real point))

private theorem euclideanSpatialRotation_add
    (axis : Fin 3) (angle : Real) (first second : EuclideanR4) :
    euclideanSpatialRotation axis angle (first + second) =
      euclideanSpatialRotation axis angle first +
        euclideanSpatialRotation axis angle second := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [euclideanSpatialRotation, ambientSpatialRotationFlow] <;> ring

private theorem euclideanSpatialRotation_smul
    (axis : Fin 3) (angle scalar : Real) (point : EuclideanR4) :
    euclideanSpatialRotation axis angle (scalar • point) =
      scalar • euclideanSpatialRotation axis angle point := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases axis <;> fin_cases index <;>
    simp [euclideanSpatialRotation, ambientSpatialRotationFlow] <;> ring

private theorem euclideanSpatialRotation_norm
    (axis : Fin 3) (angle : Real) (point : EuclideanR4) :
    ‖euclideanSpatialRotation axis angle point‖ = ‖point‖ := by
  have hSquare : ‖euclideanSpatialRotation axis angle point‖ ^ 2 =
      ‖point‖ ^ 2 := by
    calc
      ‖euclideanSpatialRotation axis angle point‖ ^ 2 =
          radiusSquared (ambientSpatialRotationFlow axis
            (angle, EuclideanSpace.equiv (Fin 4) Real point)) := by
            exact euclidean_norm_sq_eq_radiusSquared _
      _ = radiusSquared (EuclideanSpace.equiv (Fin 4) Real point) :=
        ambientSpatialRotationFlow_preserves_radius axis _
      _ = ‖point‖ ^ 2 := by
        rw [← euclidean_norm_sq_eq_radiusSquared]
        simp
  nlinarith [norm_nonneg (euclideanSpatialRotation axis angle point),
    norm_nonneg point]

private def euclideanSpatialRotationLinearIsometry
    (axis : Fin 3) (angle : Real) : EuclideanR4 →ₗᵢ[Real] EuclideanR4 where
  toFun := euclideanSpatialRotation axis angle
  map_add' := euclideanSpatialRotation_add axis angle
  map_smul' := euclideanSpatialRotation_smul axis angle
  norm_map' := euclideanSpatialRotation_norm axis angle

private def euclideanSpatialRotationLinearIsometryEquiv
    (axis : Fin 3) (angle : Real) : EuclideanR4 ≃ₗᵢ[Real] EuclideanR4 :=
  LinearIsometryEquiv.ofSurjective
    (euclideanSpatialRotationLinearIsometry axis angle)
    ((euclideanSpatialRotationLinearIsometry axis angle).toLinearMap
      |>.surjective_of_injective
        (euclideanSpatialRotationLinearIsometry axis angle).injective)

private def standardSpatialRotation
    (axis : Fin 3) (angle : Real) (point : StandardSphere) : StandardSphere :=
  unitThreeSphereHomeomorph
    (sphereSpatialRotationFlow axis
      (angle, unitThreeSphereHomeomorph.symm point))

private theorem standardSpatialRotation_eq_linear
    (axis : Fin 3) (angle : Real) :
    standardSpatialRotation axis angle =
      standardSphereLinearIsometry
        (euclideanSpatialRotationLinearIsometryEquiv axis angle) := by
  funext point
  apply Subtype.ext
  change (EuclideanSpace.equiv (Fin 4) Real).symm
      (ambientSpatialRotationFlow axis
        (angle, EuclideanSpace.equiv (Fin 4) Real point.1)) = _
  simp [standardSphereLinearIsometry,
    euclideanSpatialRotationLinearIsometryEquiv,
    euclideanSpatialRotationLinearIsometry,
    euclideanSpatialRotation]

private theorem standardSpatialRotation_measurePreserving
    (axis : Fin 3) (angle : Real) :
    MeasurePreserving (standardSpatialRotation axis angle)
      (volume : Measure EuclideanR4).toSphere
      (volume : Measure EuclideanR4).toSphere := by
  rw [standardSpatialRotation_eq_linear axis angle]
  exact standardSphereLinearIsometry_measurePreserving _

/-- Rotation of the sphere factor on the canonical spacetime base. -/
def spacetimeBaseSpatialRotation
    (axis : Fin 3) (angle : Real) (base : SpacetimeBase) : SpacetimeBase :=
  (standardSpatialRotation axis angle base.1, base.2)

theorem spacetimeBaseSpatialRotation_measurePreserving
    (axis : Fin 3) (angle : Real) :
    MeasurePreserving (spacetimeBaseSpatialRotation axis angle)
      (spacetimeBaseMeasure period) (spacetimeBaseMeasure period) := by
  change MeasurePreserving
    (Prod.map (standardSpatialRotation axis angle) id)
    (((volume : Measure EuclideanR4).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
    (((volume : Measure EuclideanR4).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact (standardSpatialRotation_measurePreserving axis angle).prod
    (MeasurePreserving.id
      (volume.restrict (canonicalLatitudeTimeInterval period)))

theorem spatialRotationFlow_spacetimeFundamentalDomainMap
    (axis : Fin 3) (angle : Real) (base : SpacetimeBase) :
    spatialRotationFlow period hPeriod axis angle
        (spacetimeFundamentalDomainMap period hPeriod base) =
      spacetimeFundamentalDomainMap period hPeriod
        (spacetimeBaseSpatialRotation axis angle base) := by
  unfold spacetimeFundamentalDomainMap spacetimeBaseSpatialRotation
  rw [spatialRotationFlow_mk]
  congr 1

/-- Every spatial rotation preserves the canonical Lorentz volume. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_spatialRotation_measurePreserving
    (axis : Fin 3) (angle : Real) :
    MeasurePreserving
      (spatialRotationFlow period hPeriod axis angle)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_spacetimeBase]
  apply MeasurePreserving.of_semiconj
    ((spacetimeFundamentalDomainMap_continuous period hPeriod).measurable
      |>.measurePreserving (spacetimeBaseMeasure period))
    (spacetimeBaseSpatialRotation_measurePreserving period axis angle)
  · intro base
    exact (spatialRotationFlow_spacetimeFundamentalDomainMap period hPeriod
      axis angle base).symm
  · exact (spatialRotationFlow_continuous period hPeriod axis angle).measurable

/-- Gate marker for the three canonical-volume-preserving spatial flows. -/
theorem canonical_spatial_rotation_measure_gate :
    ∀ (axis : Fin 3) (angle : Real),
      MeasurePreserving
        (spatialRotationFlow period hPeriod axis angle)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_spatialRotation_measurePreserving
    period hPeriod

end
end P0EFTJanusMappingTorusCanonicalSpatialRotationMeasure4D
end JanusFormal
