import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-!
# Equatorial coarea formula for `Measure.toSphere` on the unit three-sphere

Write a point of the unit three-sphere as

`(sin ν, cos ν • u)`, with `u ∈ S²` and `-π/2 < ν < π/2`.

The surface density is `cos² ν`.  The proof compares two decompositions of
four-dimensional Lebesgue measure:

* the radial decomposition of `ℝ⁴` supplied by
  `Measure.measurePreserving_homeomorphUnitSphereProd`;
* the radial decomposition of the last three coordinates, followed by ordinary
  planar polar coordinates for `(ρ,x₀)`.

The planar Jacobian is `r`, while the radial density in `ℝ³` is
`ρ² = r² cos² ν`; hence the total density is `r³ cos² ν`.  The common `r³`
radial factor is removed with a compactly supported radial normalizer of mass
one.
-/

namespace JanusFormal
namespace P0EFTJanusMeasureToSphereEquatorialCoarea4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

private abbrev Sphere2 := Metric.sphere (0 : EuclideanR3) 1
private abbrev Sphere3 := Metric.sphere (0 : EuclideanR4) 1
private abbrev ProductR4 := WithLp 2 (EuclideanR3 × Real)
private abbrev ProductSphere3 := Metric.sphere (0 : ProductR4) 1
private abbrev PositiveRadius := Set.Ioi (0 : Real)
private abbrev LatitudeAngle := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-! ## Splitting the first coordinate from the equatorial three-space -/

/-- Euclidean `ℝ⁴` isometrically split into its equatorial tail and first
coordinate. -/
noncomputable def tailNormalLinearIsometryEquiv :
    EuclideanR4 ≃ₗᵢ[Real] ProductR4 where
  toFun point :=
    WithLp.toLp 2
      ((EuclideanSpace.equiv (Fin 3) Real).symm
          (fun index =>
            (EuclideanSpace.equiv (Fin 4) Real point) index.succ),
        (EuclideanSpace.equiv (Fin 4) Real point) 0)
  invFun point :=
    (EuclideanSpace.equiv (Fin 4) Real).symm
      (Fin.cases
        (WithLp.ofLp point).2
        (fun index =>
          (EuclideanSpace.equiv (Fin 3) Real (WithLp.ofLp point).1) index))
  left_inv point := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index <;> simp
  right_inv point := by
    apply WithLp.toLp_injective
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  map_add' first second := by
    apply WithLp.toLp_injective
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  map_smul' scalar point := by
    apply WithLp.toLp_injective
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  norm_map' point := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      WithLp.prod_norm_sq_eq_of_L2,
      EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    change
      (∑ index : Fin 4,
          (EuclideanSpace.equiv (Fin 4) Real point index) ^ 2) =
        (∑ index : Fin 3,
          (EuclideanSpace.equiv (Fin 4) Real point index.succ) ^ 2) +
        ‖(EuclideanSpace.equiv (Fin 4) Real point) 0‖ ^ 2
    rw [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    ring

/-- The induced equivalence of unit spheres. -/
noncomputable def tailNormalSphereEquiv : Sphere3 ≃ₘ ProductSphere3 where
  toFun point :=
    ⟨tailNormalLinearIsometryEquiv point.1, by
      simpa [Metric.mem_sphere, dist_zero_right] using point.2⟩
  invFun point :=
    ⟨tailNormalLinearIsometryEquiv.symm point.1, by
      simpa [Metric.mem_sphere, dist_zero_right] using point.2⟩
  left_inv point := by
    apply Subtype.ext
    exact tailNormalLinearIsometryEquiv.symm_apply_apply point.1
  right_inv point := by
    apply Subtype.ext
    exact tailNormalLinearIsometryEquiv.apply_symm_apply point.1
  measurable_toFun :=
    (tailNormalLinearIsometryEquiv.continuous.comp
      continuous_subtype_val).measurable.subtype_mk _
  measurable_invFun :=
    (tailNormalLinearIsometryEquiv.symm.continuous.comp
      continuous_subtype_val).measurable.subtype_mk _

/-- Standard equatorial latitude in the split product model. -/
def productEquatorialLatitude
    (parameter : Sphere2 × Real) : ProductSphere3 :=
  ⟨WithLp.toLp 2
      (Real.cos parameter.2 • parameter.1.1, Real.sin parameter.2), by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : Real) ≤ 1),
      WithLp.prod_norm_sq_eq_of_L2]
    have hSphere : ‖parameter.1.1‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using parameter.1.2
    simp [norm_smul, hSphere, Real.norm_eq_abs,
      Real.sin_sq_add_cos_sq]⟩

/-- The existing Janus latitude map becomes the product latitude after splitting
the first coordinate. -/
theorem tailNormalSphereEquiv_standardLatitude
    (parameter : Sphere2 × Real) :
    tailNormalSphereEquiv
        (unitThreeSphereHomeomorph
          (equatorialLatitude
            (equatorialTwoSphereHomeomorph.symm parameter.1)
            parameter.2)) =
      productEquatorialLatitude parameter := by
  apply Subtype.ext
  apply WithLp.toLp_injective
  apply Prod.ext
  · apply (EuclideanSpace.equiv (Fin 3) Real).injective
    funext index
    simp [tailNormalSphereEquiv, tailNormalLinearIsometryEquiv,
      productEquatorialLatitude, equatorialLatitude]
  · simp [tailNormalSphereEquiv, tailNormalLinearIsometryEquiv,
      productEquatorialLatitude, equatorialLatitude]

/-! ## The two-dimensional weighted polar change -/

/-- The polar strip corresponding to positive first Cartesian coordinate. -/
def latitudePolarStrip : Set (Real × Real) :=
  Set.Ioi (0 : Real) ×ˢ LatitudeAngle

/-- The positive Cartesian half-plane. -/
def positiveCartesianHalfPlane : Set (Real × Real) :=
  Set.Ioi (0 : Real) ×ˢ Set.univ

/-- Source density `r³ cos² ν` in latitude-polar variables. -/
def latitudePolarDensity (parameter : Real × Real) : ENNReal :=
  ENNReal.ofReal (parameter.1 ^ 3 * Real.cos parameter.2 ^ 2)

/-- Target density `ρ²` after splitting the three-dimensional radial variable. -/
def cylindricalDensity (parameter : Real × Real) : ENNReal :=
  ENNReal.ofReal (parameter.1 ^ 2)

/-- Measurability of the inverse planar polar map. -/
theorem measurable_polarCoord_symm : Measurable Real.polarCoord.symm := by
  have hFormula : Real.polarCoord.symm =
      fun parameter : Real × Real =>
        (parameter.1 * Real.cos parameter.2,
          parameter.1 * Real.sin parameter.2) := by
    funext parameter
    simpa using Real.polarCoord_symm_apply parameter
  rw [hFormula]
  fun_prop

/-- On the ordinary polar target, positivity of the first Cartesian coordinate
is equivalent to the latitude-angle condition. -/
theorem polarCoord_symm_mem_positiveHalfPlane_iff
    {parameter : Real × Real}
    (hParameter : parameter ∈ Real.polarCoord.target) :
    Real.polarCoord.symm parameter ∈ positiveCartesianHalfPlane ↔
      parameter ∈ latitudePolarStrip := by
  have hRadius : 0 < parameter.1 := hParameter.1
  rw [Real.polarCoord_symm_apply]
  change
    0 < parameter.1 * Real.cos parameter.2 ↔
      0 < parameter.1 ∧ parameter.2 ∈ LatitudeAngle
  simp only [hRadius, true_and]
  exact Real.cos_pos_iff.trans (by
    constructor
    · rintro ⟨integer, hLower, hUpper⟩
      have hAngle := hParameter.2
      have hIntegerZero : integer = 0 := by
        nlinarith [Real.pi_pos]
      subst integer
      simpa using ⟨hLower, hUpper⟩
    · intro hLatitude
      exact ⟨0, by simpa using hLatitude.1, by simpa using hLatitude.2⟩)

/-- Pointwise Jacobian-density identity for the weighted planar polar change. -/
theorem polarCoord_density_identity
    {parameter : Real × Real}
    (hParameter : parameter ∈ Real.polarCoord.target)
    (hLatitude : parameter ∈ latitudePolarStrip) :
    ENNReal.ofReal parameter.1 *
        cylindricalDensity (Real.polarCoord.symm parameter) =
      latitudePolarDensity parameter := by
  have hRadius : 0 ≤ parameter.1 := hParameter.1.le
  rw [Real.polarCoord_symm_apply]
  unfold cylindricalDensity latitudePolarDensity
  simp only [Prod.fst_mul, Complex.ofReal_mul, Complex.ofReal_re,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, sub_zero]
  rw [← ENNReal.ofReal_mul hRadius]
  apply congrArg ENNReal.ofReal
  ring

/-- The exact weighted planar polar measure identity. -/
theorem map_polarCoord_symm_latitudeMeasure :
    Measure.map Real.polarCoord.symm
        ((volume.restrict latitudePolarStrip).withDensity
          latitudePolarDensity) =
      (volume.restrict positiveCartesianHalfPlane).withDensity
        cylindricalDensity := by
  apply Measure.ext
  intro measurableSet hMeasurableSet
  rw [Measure.map_apply measurable_polarCoord_symm hMeasurableSet,
    withDensity_apply _ hMeasurableSet]
  rw [withDensity_apply _
    (measurable_polarCoord_symm hMeasurableSet)]
  have hPolar := Real.lintegral_comp_polarCoord_symm
    (positiveCartesianHalfPlane.indicator
      (fun point => cylindricalDensity point *
        measurableSet.indicator (fun _ => (1 : ENNReal)) point))
  rw [lintegral_indicator measurableSet_positiveCartesianHalfPlane,
    ← setLIntegral_univ] at hPolar
  have hPointwise :
      ∀ parameter ∈ Real.polarCoord.target,
        ENNReal.ofReal parameter.1 *
            positiveCartesianHalfPlane.indicator
              (fun point => cylindricalDensity point *
                measurableSet.indicator (fun _ => (1 : ENNReal)) point)
              (Real.polarCoord.symm parameter) =
          latitudePolarStrip.indicator
            (fun point => latitudePolarDensity point *
              (Real.polarCoord.symm ⁻¹' measurableSet).indicator
                (fun _ => (1 : ENNReal)) point)
            parameter := by
    intro parameter hParameter
    by_cases hLatitude : parameter ∈ latitudePolarStrip
    · have hPositive :=
        (polarCoord_symm_mem_positiveHalfPlane_iff hParameter).2 hLatitude
      simp [hLatitude, hPositive,
        polarCoord_density_identity hParameter hLatitude, mul_assoc]
    · have hNotPositive :
          Real.polarCoord.symm parameter ∉ positiveCartesianHalfPlane :=
        mt (polarCoord_symm_mem_positiveHalfPlane_iff hParameter).1 hLatitude
      simp [hLatitude, hNotPositive]
  have hTargetSubset : latitudePolarStrip ⊆ Real.polarCoord.target := by
    rintro parameter ⟨hRadius, hLatitude⟩
    exact ⟨hRadius, by
      constructor <;> nlinarith [hLatitude.1, hLatitude.2, Real.pi_pos]⟩
  rw [← hPolar]
  rw [setLIntegral_congr_fun Real.polarCoord.open_target.measurableSet hPointwise]
  rw [lintegral_indicator measurableSet_latitudePolarStrip]
  rw [Measure.restrict_restrict measurableSet_latitudePolarStrip]
  rw [inter_eq_left.2 hTargetSubset]
  simp [setLIntegral_one, hMeasurableSet]

/-! ## Radial decompositions in `ℝ³` and split `ℝ⁴` -/

/-- Radial reconstruction in the equatorial three-space. -/
def radialReconstruction3
    (parameter : Sphere2 × PositiveRadius) : EuclideanR3 :=
  parameter.2.1 • parameter.1.1

/-- The generalized polar theorem reconstructs three-dimensional Lebesgue
measure from `S² × (0,∞)`. -/
theorem radialReconstruction3_measurePreserving :
    MeasurePreserving radialReconstruction3
      ((volume : Measure EuclideanR3).toSphere.prod
        (Measure.volumeIoiPow 2))
      (volume : Measure EuclideanR3) := by
  have hPolar :=
    Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (volume : Measure EuclideanR3))
  have hPolarSymm := MeasurePreserving.symm
    (homeomorphUnitSphereProd EuclideanR3).toMeasurableEquiv hPolar
  have hSubtype : MeasurePreserving
      ((↑) : ({0}ᶜ : Set EuclideanR3) → EuclideanR3)
      ((volume : Measure EuclideanR3).comap (↑))
      (volume : Measure EuclideanR3) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_singleton (0 : EuclideanR3)).compl,
      Measure.restrict_compl_singleton]
  simpa [radialReconstruction3,
    homeomorphUnitSphereProd_symm_apply_coe,
    Function.comp_def] using hSubtype.comp hPolarSymm

/-- Cylindrical reconstruction of the split four-space. -/
def cylindricalReconstruction
    (parameter : (Sphere2 × PositiveRadius) × Real) : ProductR4 :=
  WithLp.toLp 2
    (radialReconstruction3 parameter.1, parameter.2)

/-- Cylindrical reconstruction is measure-preserving. -/
theorem cylindricalReconstruction_measurePreserving :
    MeasurePreserving cylindricalReconstruction
      (((volume : Measure EuclideanR3).toSphere.prod
        (Measure.volumeIoiPow 2)).prod volume)
      (volume : Measure ProductR4) := by
  exact (WithLp.volume_preserving_toLp EuclideanR3 Real).comp
    (MeasurePreserving.prod radialReconstruction3_measurePreserving
      (MeasurePreserving.id volume))

/-- Latitude-polar reconstruction with positive radial and latitude subtypes. -/
def latitudePolarReconstruction
    (parameter : PositiveRadius × LatitudeAngle) : PositiveRadius × Real :=
  (⟨parameter.1.1 * Real.cos parameter.2.1, by
      exact mul_pos parameter.1.2
        (Real.cos_pos_of_mem_Ioo parameter.2.2)⟩,
    parameter.1.1 * Real.sin parameter.2.1)

/-- Weighted latitude-angle measure. -/
def latitudeAngleMeasure : Measure LatitudeAngle :=
  (volume.comap ((↑) : LatitudeAngle → Real)).withDensity
    (fun angle => ENNReal.ofReal (Real.cos angle.1 ^ 2))

/-- The subtype form of the weighted planar polar identity. -/
theorem latitudePolarReconstruction_measurePreserving :
    MeasurePreserving latitudePolarReconstruction
      ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure)
      ((Measure.volumeIoiPow 2).prod volume) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext
  intro measurableSet hMeasurableSet
  have hFull := congrArg
    (fun measure : Measure (Real × Real) => measure measurableSet)
    map_polarCoord_symm_latitudeMeasure
  simpa [latitudePolarReconstruction, latitudeAngleMeasure,
    Measure.volumeIoiPow, latitudePolarDensity, cylindricalDensity,
    prod_withDensity, Measure.prod_restrict,
    Measure.map_map, hMeasurableSet] using hFull

/-- Reassociate `S² × ((0,∞) × ℝ)` to `(S² × (0,∞)) × ℝ`. -/
def cylindricalReassociate
    (parameter : Sphere2 × (PositiveRadius × Real)) :
    (Sphere2 × PositiveRadius) × Real :=
  ((parameter.1, parameter.2.1), parameter.2.2)

/-- Reassociation is measure-preserving for product measures. -/
theorem cylindricalReassociate_measurePreserving :
    MeasurePreserving cylindricalReassociate
      ((volume : Measure EuclideanR3).toSphere.prod
        ((Measure.volumeIoiPow 2).prod volume))
      (((volume : Measure EuclideanR3).toSphere.prod
        (Measure.volumeIoiPow 2)).prod volume) := by
  refine ⟨by fun_prop, ?_⟩
  change Measure.map MeasurableEquiv.prodAssoc.symm
      ((volume : Measure EuclideanR3).toSphere.prod
        ((Measure.volumeIoiPow 2).prod volume)) =
    (((volume : Measure EuclideanR3).toSphere.prod
      (Measure.volumeIoiPow 2)).prod volume)
  apply MeasurableEquiv.prodAssoc.map_measurableEquiv_injective
  simp [Measure.prodAssoc_prod]

/-- Full latitude-radial reconstruction of the split four-space. -/
def latitudeRadialReconstruction
    (parameter : Sphere2 × (PositiveRadius × LatitudeAngle)) : ProductR4 :=
  cylindricalReconstruction
    (cylindricalReassociate
      (parameter.1,
        latitudePolarReconstruction parameter.2))

/-- Full latitude-radial reconstruction is measure-preserving. -/
theorem latitudeRadialReconstruction_measurePreserving :
    MeasurePreserving latitudeRadialReconstruction
      ((volume : Measure EuclideanR3).toSphere.prod
        ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure))
      (volume : Measure ProductR4) := by
  exact cylindricalReconstruction_measurePreserving.comp
    (cylindricalReassociate_measurePreserving.comp
      (MeasurePreserving.prod
        (MeasurePreserving.id ((volume : Measure EuclideanR3).toSphere))
        latitudePolarReconstruction_measurePreserving))

/-- Latitude-radial reconstruction is radial scaling of the product-sphere
latitude point. -/
theorem latitudeRadialReconstruction_eq_smul
    (parameter : Sphere2 × (PositiveRadius × LatitudeAngle)) :
    latitudeRadialReconstruction parameter =
      parameter.2.1.1 •
        (productEquatorialLatitude
          (parameter.1, parameter.2.2.1)).1 := by
  apply WithLp.toLp_injective
  apply Prod.ext
  · change
      (parameter.2.1.1 * Real.cos parameter.2.2.1) • parameter.1.1 =
        parameter.2.1.1 •
          (Real.cos parameter.2.2.1 • parameter.1.1)
    module
  · change parameter.2.1.1 * Real.sin parameter.2.2.1 =
      parameter.2.1.1 * Real.sin parameter.2.2.1
    rfl

/-! ## Cancelling the common radial factor -/

/-- Compactly supported radial normalizer of mass one for `volumeIoiPow 3`. -/
def radialNormalizer (radius : PositiveRadius) : ENNReal :=
  if radius.1 < 1 then 4 else 0

/-- The radial normalizer is measurable. -/
theorem radialNormalizer_measurable : Measurable radialNormalizer := by
  unfold radialNormalizer
  fun_prop

/-- The radial normalizer has total mass one. -/
theorem lintegral_radialNormalizer :
    ∫⁻ radius : PositiveRadius, radialNormalizer radius
        ∂Measure.volumeIoiPow 3 = 1 := by
  let oneRadius : PositiveRadius := ⟨1, one_pos⟩
  have hIndicator : radialNormalizer =
      (Set.Iio oneRadius).indicator (fun _ => (4 : ENNReal)) := by
    funext radius
    simp [radialNormalizer, oneRadius]
  rw [hIndicator, lintegral_indicator measurableSet_Iio]
  simp [Measure.volumeIoiPow_apply_Iio, oneRadius]

/-- Probability radial measure used to cancel the common `r³` factor. -/
def normalizedRadialMeasure : Measure PositiveRadius :=
  (Measure.volumeIoiPow 3).withDensity radialNormalizer

@[simp] theorem normalizedRadialMeasure_univ :
    normalizedRadialMeasure Set.univ = 1 := by
  rw [normalizedRadialMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact lintegral_radialNormalizer

/-- Radial reconstruction of the split four-space. -/
def radialReconstruction4
    (parameter : ProductSphere3 × PositiveRadius) : ProductR4 :=
  parameter.2.1 • parameter.1.1

/-- Radial reconstruction is a measurable embedding. -/
theorem radialReconstruction4_measurableEmbedding :
    MeasurableEmbedding radialReconstruction4 := by
  have hFormula : radialReconstruction4 =
      ((↑) : ({0}ᶜ : Set ProductR4) → ProductR4) ∘
        (homeomorphUnitSphereProd ProductR4).symm := by
    funext parameter
    simp [radialReconstruction4,
      homeomorphUnitSphereProd_symm_apply_coe, Function.comp_def]
  rw [hFormula]
  exact (MeasurableEmbedding.subtype_coe
    (measurableSet_singleton (0 : ProductR4)).compl).comp
      (homeomorphUnitSphereProd ProductR4).symm.measurableEmbedding

/-- The generalized polar theorem reconstructs split four-dimensional
Lebesgue measure from its unit sphere and `r³ dr`. -/
theorem radialReconstruction4_measurePreserving :
    MeasurePreserving radialReconstruction4
      ((volume : Measure ProductR4).toSphere.prod
        (Measure.volumeIoiPow 3))
      (volume : Measure ProductR4) := by
  have hPolar :=
    Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (volume : Measure ProductR4))
  have hPolarSymm := MeasurePreserving.symm
    (homeomorphUnitSphereProd ProductR4).toMeasurableEquiv hPolar
  have hSubtype : MeasurePreserving
      ((↑) : ({0}ᶜ : Set ProductR4) → ProductR4)
      ((volume : Measure ProductR4).comap (↑))
      (volume : Measure ProductR4) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe
        (measurableSet_singleton (0 : ProductR4)).compl,
      Measure.restrict_compl_singleton]
  simpa [radialReconstruction4,
    homeomorphUnitSphereProd_symm_apply_coe,
    Function.comp_def] using hSubtype.comp hPolarSymm

/-- Move the radial coordinate to the middle:
`((u,ν),r) ↦ (u,(r,ν))`. -/
def latitudeRadiusReassociate
    (parameter : (Sphere2 × LatitudeAngle) × PositiveRadius) :
    Sphere2 × (PositiveRadius × LatitudeAngle) :=
  (parameter.1.1, (parameter.2, parameter.1.2))

/-- The preceding permutation preserves the corresponding product measures. -/
theorem latitudeRadiusReassociate_measurePreserving :
    MeasurePreserving latitudeRadiusReassociate
      ((((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure).prod
        (Measure.volumeIoiPow 3)))
      ((volume : Measure EuclideanR3).toSphere.prod
        ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure)) := by
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        ((Sphere2 × LatitudeAngle) × PositiveRadius) ≃ₘ
          Sphere2 × (LatitudeAngle × PositiveRadius))
      ((((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure).prod
        (Measure.volumeIoiPow 3)))
      ((volume : Measure EuclideanR3).toSphere.prod
        (latitudeAngleMeasure.prod (Measure.volumeIoiPow 3))) :=
    ⟨MeasurableEquiv.prodAssoc.measurable, Measure.prodAssoc_prod⟩
  have hSwap : MeasurePreserving
      (Prod.map id Prod.swap :
        Sphere2 × (LatitudeAngle × PositiveRadius) →
          Sphere2 × (PositiveRadius × LatitudeAngle))
      ((volume : Measure EuclideanR3).toSphere.prod
        (latitudeAngleMeasure.prod (Measure.volumeIoiPow 3)))
      ((volume : Measure EuclideanR3).toSphere.prod
        ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.map_prod_map
      ((volume : Measure EuclideanR3).toSphere)
      (latitudeAngleMeasure.prod (Measure.volumeIoiPow 3))
      measurable_id measurable_swap]
    simp [Measure.prod_swap]
  simpa [latitudeRadiusReassociate, Function.comp_def] using hSwap.comp hAssoc

/-- Latitude map with the angle subtype exposed. -/
def productEquatorialLatitudeSubtype
    (parameter : Sphere2 × LatitudeAngle) : ProductSphere3 :=
  productEquatorialLatitude (parameter.1, parameter.2.1)

/-- Latitude and radius as a product map. -/
def productLatitudeRadiusMap
    (parameter : (Sphere2 × LatitudeAngle) × PositiveRadius) :
    ProductSphere3 × PositiveRadius :=
  Prod.map productEquatorialLatitudeSubtype id parameter

/-- The radial reconstruction after latitude-radius mapping agrees with the
latitude-radial reconstruction after reassociation. -/
theorem radialReconstruction4_productLatitudeRadiusMap
    (parameter : (Sphere2 × LatitudeAngle) × PositiveRadius) :
    radialReconstruction4 (productLatitudeRadiusMap parameter) =
      latitudeRadialReconstruction (latitudeRadiusReassociate parameter) := by
  rw [latitudeRadialReconstruction_eq_smul]
  rfl

/-- The latitude-radius product map preserves the full radial measures. -/
theorem productLatitudeRadiusMap_measurePreserving :
    MeasurePreserving productLatitudeRadiusMap
      ((((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure).prod
        (Measure.volumeIoiPow 3)))
      ((volume : Measure ProductR4).toSphere.prod
        (Measure.volumeIoiPow 3)) := by
  have hFunction :
      radialReconstruction4 ∘ productLatitudeRadiusMap =
        latitudeRadialReconstruction ∘ latitudeRadiusReassociate := by
    funext parameter
    exact radialReconstruction4_productLatitudeRadiusMap parameter
  have hComposed : MeasurePreserving
      (radialReconstruction4 ∘ productLatitudeRadiusMap)
      ((((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure).prod
        (Measure.volumeIoiPow 3)))
      (volume : Measure ProductR4) := by
    rw [hFunction]
    exact latitudeRadialReconstruction_measurePreserving.comp
      latitudeRadiusReassociate_measurePreserving
  refine ⟨by fun_prop, ?_⟩
  apply radialReconstruction4_measurableEmbedding.map_injective
  rw [Measure.map_map radialReconstruction4_measurableEmbedding.measurable
      (by fun_prop : Measurable productLatitudeRadiusMap),
    hComposed.map_eq,
    radialReconstruction4_measurePreserving.map_eq]

/-- A measure-preserving map remains measure-preserving after installing on the
source the pullback of a measurable target density. -/
private theorem measurePreserving_withDensity
    {Source Target : Type*}
    [MeasurableSpace Source] [MeasurableSpace Target]
    {sourceMeasure : Measure Source} {targetMeasure : Measure Target}
    {map : Source → Target}
    (hMap : MeasurePreserving map sourceMeasure targetMeasure)
    (density : Target → ENNReal) (hDensity : Measurable density) :
    MeasurePreserving map
      (sourceMeasure.withDensity (density ∘ map))
      (targetMeasure.withDensity density) := by
  refine ⟨hMap.measurable, ?_⟩
  apply Measure.ext
  intro measurableSet hMeasurableSet
  rw [Measure.map_apply hMap.measurable hMeasurableSet,
    withDensity_apply _ (hMap.measurable hMeasurableSet),
    withDensity_apply _ hMeasurableSet]
  simpa [Function.comp_def] using
    hMap.setLIntegral_comp_preimage hMeasurableSet hDensity

/-- The weighted latitude measure maps exactly to the split-product sphere
measure. -/
theorem productEquatorialLatitudeSubtype_weighted_map :
    Measure.map productEquatorialLatitudeSubtype
        ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure) =
      (volume : Measure ProductR4).toSphere := by
  let density : ProductSphere3 × PositiveRadius → ENNReal :=
    fun parameter => radialNormalizer parameter.2
  have hDensity : Measurable density :=
    radialNormalizer_measurable.comp measurable_snd
  have hWeighted := measurePreserving_withDensity
    productLatitudeRadiusMap_measurePreserving density hDensity
  have hMapNormalized :
      Measure.map productLatitudeRadiusMap
          (((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure).prod
            normalizedRadialMeasure) =
        (volume : Measure ProductR4).toSphere.prod normalizedRadialMeasure := by
    simpa [density, normalizedRadialMeasure, productLatitudeRadiusMap,
      Function.comp_def, prod_withDensity_right radialNormalizer_measurable]
      using hWeighted.map_eq
  have hProduct :
      (Measure.map productEquatorialLatitudeSubtype
          ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure)).prod
          normalizedRadialMeasure =
        (volume : Measure ProductR4).toSphere.prod normalizedRadialMeasure := by
    calc
      _ = Measure.map productLatitudeRadiusMap
          ((((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure).prod
            normalizedRadialMeasure)) := by
          simpa [productLatitudeRadiusMap] using
            Measure.map_prod_map
              ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure)
              normalizedRadialMeasure
              (by fun_prop : Measurable productEquatorialLatitudeSubtype)
              measurable_id
      _ = _ := hMapNormalized
  have hFirstMarginal := congrArg
    (Measure.map
      (Prod.fst : ProductSphere3 × PositiveRadius → ProductSphere3)) hProduct
  simpa using hFirstMarginal

/-! ## Returning from angle subtypes and the split sphere -/

/-- Real-valued latitude density. -/
def realLatitudeWeight (latitude : Real) : ENNReal :=
  ENNReal.ofReal (Real.cos latitude ^ 2)

theorem realLatitudeWeight_measurable : Measurable realLatitudeWeight := by
  unfold realLatitudeWeight
  fun_prop

/-- Inclusion of the latitude-angle subtype with its weighted measure. -/
theorem latitudeAngleInclusion_measurePreserving :
    MeasurePreserving ((↑) : LatitudeAngle → Real)
      latitudeAngleMeasure
      ((volume.restrict LatitudeAngle).withDensity realLatitudeWeight) := by
  have hBase : MeasurePreserving ((↑) : LatitudeAngle → Real)
      (volume.comap ((↑) : LatitudeAngle → Real))
      (volume.restrict LatitudeAngle) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    exact map_comap_subtype_coe measurableSet_Ioo
  simpa [latitudeAngleMeasure, realLatitudeWeight, Function.comp_def] using
    measurePreserving_withDensity hBase realLatitudeWeight
      realLatitudeWeight_measurable

/-- Inclusion of latitude parameters from the angle subtype to real latitude. -/
def latitudeParameterInclusion
    (parameter : Sphere2 × LatitudeAngle) : Sphere2 × Real :=
  (parameter.1, parameter.2.1)

/-- The inclusion of latitude parameters is measure-preserving. -/
theorem latitudeParameterInclusion_measurePreserving :
    MeasurePreserving latitudeParameterInclusion
      ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure)
      ((volume : Measure EuclideanR3).toSphere.prod
        ((volume.restrict LatitudeAngle).withDensity realLatitudeWeight)) := by
  simpa [latitudeParameterInclusion] using
    MeasurePreserving.prod
      (MeasurePreserving.id ((volume : Measure EuclideanR3).toSphere))
      latitudeAngleInclusion_measurePreserving

/-- The parameter measure written on `S² × ℝ`. -/
def standardLatitudeParameterMeasure : Measure (Sphere2 × Real) :=
  (((volume : Measure EuclideanR3).toSphere.prod
    (volume.restrict LatitudeAngle)).withDensity
      (fun parameter => realLatitudeWeight parameter.2))

/-- The subtype parameter measure pushes to the standard weighted parameter
measure. -/
theorem latitudeParameterInclusion_map :
    Measure.map latitudeParameterInclusion
        ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure) =
      standardLatitudeParameterMeasure := by
  calc
    _ = (volume : Measure EuclideanR3).toSphere.prod
        ((volume.restrict LatitudeAngle).withDensity realLatitudeWeight) :=
      latitudeParameterInclusion_measurePreserving.map_eq
    _ = standardLatitudeParameterMeasure := by
      exact prod_withDensity_right realLatitudeWeight_measurable

/-- Exact coarea formula on the split-product sphere, with real latitude
parameters. -/
theorem productEquatorialLatitude_weighted_map :
    Measure.map productEquatorialLatitude standardLatitudeParameterMeasure =
      (volume : Measure ProductR4).toSphere := by
  calc
    _ = Measure.map productEquatorialLatitude
        (Measure.map latitudeParameterInclusion
          ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure)) := by
      rw [latitudeParameterInclusion_map]
    _ = Measure.map
        (productEquatorialLatitude ∘ latitudeParameterInclusion)
        ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map productEquatorialLatitudeSubtype
        ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure) := by
      congr 1
    _ = _ := productEquatorialLatitudeSubtype_weighted_map

/-- The coordinate-splitting sphere equivalence preserves `Measure.toSphere`. -/
theorem tailNormalSphereEquiv_measurePreserving :
    MeasurePreserving tailNormalSphereEquiv
      (volume : Measure EuclideanR4).toSphere
      (volume : Measure ProductR4).toSphere := by
  refine ⟨tailNormalSphereEquiv.measurable, ?_⟩
  apply Measure.ext
  intro measurableSet hMeasurableSet
  rw [Measure.map_apply tailNormalSphereEquiv.measurable hMeasurableSet]
  rw [(volume : Measure EuclideanR4).toSphere_apply'
      (tailNormalSphereEquiv.measurable hMeasurableSet),
    (volume : Measure ProductR4).toSphere_apply' hMeasurableSet]
  have hVolume := tailNormalLinearIsometryEquiv.measurePreserving.map_eq
  simpa [tailNormalSphereEquiv, Set.image_image,
    LinearIsometryEquiv.norm_map] using congrArg
    (fun measure : Measure ProductR4 =>
      (Module.finrank Real ProductR4 : ENNReal) *
        measure (Set.Ioo (0 : Real) 1 •
          ((↑) '' measurableSet))) hVolume

/-- Measure form of the standard equatorial coarea formula. -/
def standardEquatorialLatitude
    (parameter : Sphere2 × Real) : Sphere3 :=
  unitThreeSphereHomeomorph
    (equatorialLatitude
      (equatorialTwoSphereHomeomorph.symm parameter.1)
      parameter.2)

/-- The weighted latitude pushforward is exactly `Measure.toSphere` on `S³`. -/
theorem standardEquatorialLatitude_weighted_map :
    Measure.map standardEquatorialLatitude
        (((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict LatitudeAngle)).withDensity
          (fun parameter =>
            ENNReal.ofReal (Real.cos parameter.2 ^ 2))) =
      (volume : Measure EuclideanR4).toSphere := by
  have hFactor : standardEquatorialLatitude =
      tailNormalSphereEquiv.symm ∘ productEquatorialLatitude := by
    funext parameter
    apply tailNormalSphereEquiv.injective
    rw [Function.comp_apply, tailNormalSphereEquiv.apply_symm_apply,
      tailNormalSphereEquiv_standardLatitude]
  rw [show (((volume : Measure EuclideanR3).toSphere.prod
      (volume.restrict LatitudeAngle)).withDensity
        (fun parameter => ENNReal.ofReal (Real.cos parameter.2 ^ 2))) =
      standardLatitudeParameterMeasure by rfl]
  rw [hFactor, ← Measure.map_map tailNormalSphereEquiv.symm.measurable
    (by fun_prop : Measurable productEquatorialLatitude)]
  rw [productEquatorialLatitude_weighted_map]
  exact (MeasurePreserving.symm tailNormalSphereEquiv
    tailNormalSphereEquiv_measurePreserving).map_eq

end
end P0EFTJanusMeasureToSphereEquatorialCoarea4D
end JanusFormal
