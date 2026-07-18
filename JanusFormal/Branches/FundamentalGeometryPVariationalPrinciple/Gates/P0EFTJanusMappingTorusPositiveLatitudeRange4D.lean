import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveLatitudeJacobian4D

/-!
# The exact range of positive latitude coordinates

This gate identifies the measured latitude collar with the corresponding
coordinate band in the round three-sphere.  The inverse is the elementary
`arcsin` latitude together with normalization of the last three coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPositiveLatitudeRange4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusMeasureToSphereLatitudeReduction4D
open P0EFTJanusMappingTorusPositiveLatitudeJacobian4D

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev StandardEquatorialSphere :=
  Metric.sphere (0 : EuclideanR3) 1

/-- The positive latitude band in the round three-sphere. -/
def canonicalPositiveLatitudeBand : Set StandardSphere :=
  {point | (EuclideanSpace.equiv (Fin 4) Real point.1) 0 ∈
    Set.Ioc (0 : Real) (Real.sin 1)}

private theorem sin_one_lt_one : Real.sin 1 < 1 := by
  have hOne : (1 : Real) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  have hPi : Real.pi / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  simpa using Real.strictMonoOn_sin hOne hPi (by linarith [Real.pi_gt_three])

private theorem sin_maps_unitIoc
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    Real.sin normal ∈ Set.Ioc (0 : Real) (Real.sin 1) := by
  have hZero : (0 : Real) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hNormalRange : normal ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hNormal.1, hNormal.2, Real.pi_gt_three]
  have hOne : (1 : Real) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_gt_three]
  constructor
  · simpa using Real.strictMonoOn_sin hZero hNormalRange hNormal.1
  · exact Real.monotoneOn_sin hNormalRange hOne hNormal.2

private theorem arcsin_mem_unitIoc
    {coordinate : Real}
    (hCoordinate : coordinate ∈ Set.Ioc (0 : Real) (Real.sin 1)) :
    Real.arcsin coordinate ∈ Set.Ioc (0 : Real) 1 := by
  constructor
  · exact Real.arcsin_pos.mpr hCoordinate.1
  · have hBound := Real.arcsin_le_arcsin hCoordinate.2
    have hArcSinOne : Real.arcsin (Real.sin 1) = 1 :=
      Real.arcsin_sin (by linarith [Real.pi_gt_three])
        (by linarith [Real.pi_gt_three])
    rwa [hArcSinOne] at hBound

private def positiveLatitudeTail
    (point : StandardSphere) (normal : Real) : EuclideanR3 :=
  (EuclideanSpace.equiv (Fin 3) Real).symm
    (fun index =>
      (EuclideanSpace.equiv (Fin 4) Real point.1) index.succ /
        Real.cos normal)

private theorem positiveLatitudeTail_mem_sphere
    (point : StandardSphere)
    (hPoint : point ∈ canonicalPositiveLatitudeBand) :
    positiveLatitudeTail point
        (Real.arcsin
          ((EuclideanSpace.equiv (Fin 4) Real point.1) 0)) ∈
      Metric.sphere (0 : EuclideanR3) 1 := by
  let coordinate := (EuclideanSpace.equiv (Fin 4) Real point.1) 0
  let normal := Real.arcsin coordinate
  have hNormal : normal ∈ Set.Ioc (0 : Real) 1 :=
    arcsin_mem_unitIoc hPoint
  have hCos : Real.cos normal ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_le_one (by
      rw [abs_of_pos hNormal.1]
      exact hNormal.2))
  have hSphere : ‖point.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using point.2
  have hCoordinate : Real.sin normal = coordinate := by
    exact Real.sin_arcsin (by linarith [hPoint.1])
      (hPoint.2.trans sin_one_lt_one.le)
  rw [Metric.mem_sphere, dist_zero_right]
  have hFour := EuclideanSpace.real_norm_sq_eq point.1
  rw [hSphere] at hFour
  change ‖positiveLatitudeTail point normal‖ = 1
  have hThree := EuclideanSpace.real_norm_sq_eq
    (positiveLatitudeTail point normal)
  have hNormSq : ‖positiveLatitudeTail point normal‖ ^ 2 = 1 := by
    rw [hThree]
    unfold positiveLatitudeTail
    rw [Fin.sum_univ_four] at hFour
    rw [Fin.sum_univ_three]
    change 1 ^ 2 =
      (EuclideanSpace.equiv (Fin 4) Real point.1) 0 ^ 2 +
      (EuclideanSpace.equiv (Fin 4) Real point.1) 1 ^ 2 +
      (EuclideanSpace.equiv (Fin 4) Real point.1) 2 ^ 2 +
      (EuclideanSpace.equiv (Fin 4) Real point.1) 3 ^ 2 at hFour
    change
      ((EuclideanSpace.equiv (Fin 4) Real point.1) 1 /
          Real.cos normal) ^ 2 +
        ((EuclideanSpace.equiv (Fin 4) Real point.1) 2 /
          Real.cos normal) ^ 2 +
        ((EuclideanSpace.equiv (Fin 4) Real point.1) 3 /
          Real.cos normal) ^ 2 = 1
    field_simp
    change Real.sin normal =
      (EuclideanSpace.equiv (Fin 4) Real point.1) 0 at hCoordinate
    rw [← hCoordinate] at hFour
    nlinarith [Real.sin_sq_add_cos_sq normal]
  nlinarith [norm_nonneg (positiveLatitudeTail point normal)]

/-- Explicit inverse coordinates on the positive latitude band. -/
def canonicalPositiveLatitudeInverse
    (point : {point : StandardSphere //
      point ∈ canonicalPositiveLatitudeBand}) :
    StandardEquatorialSphere × Real :=
  (⟨positiveLatitudeTail point.1
      (Real.arcsin
        ((EuclideanSpace.equiv (Fin 4) Real point.1.1) 0)),
    positiveLatitudeTail_mem_sphere point.1 point.2⟩,
   Real.arcsin ((EuclideanSpace.equiv (Fin 4) Real point.1.1) 0))

theorem canonicalPositiveLatitudeInverse_mem_domain
    (point : {point : StandardSphere //
      point ∈ canonicalPositiveLatitudeBand}) :
    canonicalPositiveLatitudeInverse point ∈
      canonicalPositiveLatitudeDomain := by
  exact ⟨Set.mem_univ _, arcsin_mem_unitIoc point.2⟩

@[simp]
theorem canonicalPositiveLatitudeMap_inverse
    (point : {point : StandardSphere //
      point ∈ canonicalPositiveLatitudeBand}) :
    canonicalPositiveLatitudeMap
        (canonicalPositiveLatitudeInverse point) = point.1 := by
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · change Real.sin (Real.arcsin _) = _
    exact Real.sin_arcsin (by linarith [point.2.1])
      (point.2.2.trans sin_one_lt_one.le)
  · change Real.cos (Real.arcsin _) *
        ((EuclideanSpace.equiv (Fin 4) Real point.1.1) tail.succ /
          Real.cos (Real.arcsin _)) = _
    have hCos : Real.cos (Real.arcsin
        ((EuclideanSpace.equiv (Fin 4) Real point.1.1) 0)) ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_le_one (by
        rw [abs_of_pos (arcsin_mem_unitIoc point.2).1]
        exact (arcsin_mem_unitIoc point.2).2))
    field_simp [hCos]

theorem canonicalPositiveLatitudeInverse_continuous :
    Continuous canonicalPositiveLatitudeInverse := by
  have hCoordinate (index : Fin 4) : Continuous
      (fun point : {point : StandardSphere //
          point ∈ canonicalPositiveLatitudeBand} =>
        (EuclideanSpace.equiv (Fin 4) Real point.1.1) index) :=
    (continuous_apply index).comp
      ((EuclideanSpace.equiv (Fin 4) Real).continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val))
  have hNormal : Continuous
      (fun point : {point : StandardSphere //
          point ∈ canonicalPositiveLatitudeBand} =>
        Real.arcsin
          ((EuclideanSpace.equiv (Fin 4) Real point.1.1) 0)) :=
    Real.continuous_arcsin.comp (hCoordinate 0)
  have hCos : ∀ point : {point : StandardSphere //
      point ∈ canonicalPositiveLatitudeBand},
      Real.cos (Real.arcsin
        ((EuclideanSpace.equiv (Fin 4) Real point.1.1) 0)) ≠ 0 := by
    intro point
    exact ne_of_gt (Real.cos_pos_of_le_one (by
      rw [abs_of_pos (arcsin_mem_unitIoc point.2).1]
      exact (arcsin_mem_unitIoc point.2).2))
  have hTailCoordinates : Continuous
      (fun point : {point : StandardSphere //
          point ∈ canonicalPositiveLatitudeBand} =>
        fun index : Fin 3 =>
          (EuclideanSpace.equiv (Fin 4) Real point.1.1) index.succ /
            Real.cos (Real.arcsin
              ((EuclideanSpace.equiv (Fin 4) Real point.1.1) 0))) := by
    apply continuous_pi
    intro index
    exact (hCoordinate index.succ).div
      (Real.continuous_cos.comp hNormal) hCos
  have hTail : Continuous
      (fun point : {point : StandardSphere //
          point ∈ canonicalPositiveLatitudeBand} =>
        positiveLatitudeTail point.1
          (Real.arcsin
            ((EuclideanSpace.equiv (Fin 4) Real point.1.1) 0))) := by
    exact (EuclideanSpace.equiv (Fin 3) Real).symm.continuous.comp
      hTailCoordinates
  exact (hTail.subtype_mk _).prodMk hNormal

/-- Positive latitude coordinates have exactly the expected coordinate band
as their image. -/
theorem canonicalPositiveLatitudeMap_image :
    canonicalPositiveLatitudeMap '' canonicalPositiveLatitudeDomain =
      canonicalPositiveLatitudeBand := by
  ext point
  constructor
  · rintro ⟨parameter, hParameter, rfl⟩
    exact sin_maps_unitIoc hParameter.2
  · intro hPoint
    let bandPoint : {point : StandardSphere //
        point ∈ canonicalPositiveLatitudeBand} := ⟨point, hPoint⟩
    let parameter := canonicalPositiveLatitudeInverse bandPoint
    exact ⟨parameter, canonicalPositiveLatitudeInverse_mem_domain bandPoint,
      canonicalPositiveLatitudeMap_inverse bandPoint⟩

private abbrev PositiveLatitudeDomain :=
  {parameter : StandardEquatorialSphere × Real //
    parameter ∈ canonicalPositiveLatitudeDomain}

private abbrev PositiveLatitudeBand :=
  {point : StandardSphere // point ∈ canonicalPositiveLatitudeBand}

def canonicalPositiveLatitudeRestrictedMap
    (parameter : PositiveLatitudeDomain) : PositiveLatitudeBand :=
  ⟨canonicalPositiveLatitudeMap parameter.1,
    sin_maps_unitIoc parameter.2.2⟩

def canonicalPositiveLatitudeRestrictedInverse
    (point : PositiveLatitudeBand) : PositiveLatitudeDomain :=
  ⟨canonicalPositiveLatitudeInverse point,
    canonicalPositiveLatitudeInverse_mem_domain point⟩

/-- Latitude coordinates are a homeomorphism from the positive collar onto
the coordinate band. -/
def canonicalPositiveLatitudeHomeomorph :
    PositiveLatitudeDomain ≃ₜ PositiveLatitudeBand where
  toFun := canonicalPositiveLatitudeRestrictedMap
  invFun := canonicalPositiveLatitudeRestrictedInverse
  left_inv parameter := by
    apply Subtype.ext
    apply canonicalPositiveLatitudeMap_injOn
      (canonicalPositiveLatitudeInverse_mem_domain
        (canonicalPositiveLatitudeRestrictedMap parameter)) parameter.2
    exact canonicalPositiveLatitudeMap_inverse
      (canonicalPositiveLatitudeRestrictedMap parameter)
  right_inv point := by
    apply Subtype.ext
    exact canonicalPositiveLatitudeMap_inverse point
  continuous_toFun :=
    (canonicalPositiveLatitudeMap_continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    canonicalPositiveLatitudeInverse_continuous.subtype_mk _

/-- The same exact coordinate identification as a measurable equivalence. -/
def canonicalPositiveLatitudeMeasurableEquiv :
    PositiveLatitudeDomain ≃ᵐ PositiveLatitudeBand :=
  canonicalPositiveLatitudeHomeomorph.toMeasurableEquiv

/-- The coordinate band is Borel measurable. -/
theorem canonicalPositiveLatitudeBand_measurable :
    MeasurableSet canonicalPositiveLatitudeBand := by
  rw [← canonicalPositiveLatitudeMap_image]
  exact canonicalPositiveLatitudeMap_image_measurable

end

end P0EFTJanusMappingTorusPositiveLatitudeRange4D
end JanusFormal
