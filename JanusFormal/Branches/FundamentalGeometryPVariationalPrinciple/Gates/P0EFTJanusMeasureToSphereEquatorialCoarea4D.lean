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
    Measure.withDensity_apply _ hMeasurableSet]
  rw [Measure.withDensity_apply _
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
    Measure.prod_withDensity, Measure.prod_restrict,
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
  exact (Measure.prodAssoc_prod
    (μ := (volume : Measure EuclideanR3).toSphere)
    (ν := Measure.volumeIoiPow 2)
    (τ := volume)).symm

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

/-! ## Removing the common radial factor -/

/-- Compactly supported radial normalizer of mass one for `volumeIoiPow 3`. -/
def radialNormalizer (radius : PositiveRadius) : ENNReal :=
  if radius.1 < 1 then 4 else 0

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

/-- Exact coarea formula in the split product sphere. -/
theorem productEquatorialLatitude_lintegral
    (integrand : ProductSphere3 → ENNReal)
    (hIntegrand : Measurable integrand) :
    ∫⁻ point : ProductSphere3, integrand point
        ∂(volume : Measure ProductR4).toSphere =
      ∫⁻ point : Sphere2,
        ∫⁻ latitude : LatitudeAngle,
          ENNReal.ofReal (Real.cos latitude.1 ^ 2) *
            integrand (productEquatorialLatitude (point, latitude.1))
          ∂(volume.comap ((↑) : LatitudeAngle → Real))
        ∂(volume : Measure EuclideanR3).toSphere := by
  have hPolar4 :=
    Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (volume : Measure ProductR4))
  have hRadialMass := lintegral_radialNormalizer
  calc
    ∫⁻ point : ProductSphere3, integrand point
        ∂(volume : Measure ProductR4).toSphere =
      ∫⁻ point : ProductSphere3,
        ∫⁻ radius : PositiveRadius,
          radialNormalizer radius * integrand point
          ∂Measure.volumeIoiPow 3
        ∂(volume : Measure ProductR4).toSphere := by
          apply lintegral_congr
          intro point
          rw [← ENNReal.one_mul (integrand point), ← hRadialMass,
            lintegral_const_mul]
          exact hIntegrand.const_mul _
    _ = ∫⁻ value : ProductR4,
        radialNormalizer
            ⟨‖value‖, by
              by_cases hValue : value = 0
              · simp [hValue]
              · simpa using norm_pos_iff.mpr hValue⟩ *
          integrand
            ⟨‖value‖⁻¹ • value, by
              by_cases hValue : value = 0
              · simp [hValue]
              · simp [Metric.mem_sphere, dist_zero_right, norm_smul,
                  hValue]⟩ := by
          rw [← hPolar4.lintegral_comp_emb
            (homeomorphUnitSphereProd ProductR4).measurableEmbedding]
          apply lintegral_congr
          intro value
          simp [homeomorphUnitSphereProd_apply_fst_coe,
            homeomorphUnitSphereProd_apply_snd_coe]
    _ = ∫⁻ parameter : Sphere2 × (PositiveRadius × LatitudeAngle),
        radialNormalizer parameter.2.1 *
          integrand
            (productEquatorialLatitude
              (parameter.1, parameter.2.2.1))
        ∂((volume : Measure EuclideanR3).toSphere.prod
          ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure)) := by
          rw [← latitudeRadialReconstruction_measurePreserving.lintegral_comp]
          · apply lintegral_congr
            intro parameter
            rw [latitudeRadialReconstruction_eq_smul]
            have hNorm :
                ‖latitudeRadialReconstruction parameter‖ =
                  parameter.2.1.1 := by
              rw [latitudeRadialReconstruction_eq_smul,
                norm_smul]
              have hSphere :
                  ‖(productEquatorialLatitude
                    (parameter.1, parameter.2.2.1)).1‖ = 1 := by
                simpa [Metric.mem_sphere, dist_zero_right] using
                  (productEquatorialLatitude
                    (parameter.1, parameter.2.2.1)).2
              simp [hSphere, abs_of_pos parameter.2.1.2]
            simp [hNorm, latitudeRadialReconstruction_eq_smul,
              parameter.2.1.2.ne']
          · fun_prop
    _ = ∫⁻ point : Sphere2,
        ∫⁻ latitude : LatitudeAngle,
          ENNReal.ofReal (Real.cos latitude.1 ^ 2) *
            integrand (productEquatorialLatitude (point, latitude.1))
          ∂(volume.comap ((↑) : LatitudeAngle → Real))
        ∂(volume : Measure EuclideanR3).toSphere := by
          rw [lintegral_prod]
          apply lintegral_congr
          intro point
          rw [lintegral_prod]
          rw [Measure.lintegral_withDensity_eq_lintegral_mul]
          · apply lintegral_congr
            intro radius
            rw [mul_assoc, ← lintegral_const_mul]
            · rw [lintegral_radialNormalizer, one_mul]
            · fun_prop
          · fun_prop
          · fun_prop

/-- Exact coarea formula on Mathlib's standard `S³`. -/
theorem standardEquatorialLatitude_lintegral
    (integrand : Sphere3 → ENNReal)
    (hIntegrand : Measurable integrand) :
    ∫⁻ point : Sphere3, integrand point
        ∂(volume : Measure EuclideanR4).toSphere =
      ∫⁻ point : Sphere2,
        ∫⁻ latitude : LatitudeAngle,
          ENNReal.ofReal (Real.cos latitude.1 ^ 2) *
            integrand
              (unitThreeSphereHomeomorph
                (equatorialLatitude
                  (equatorialTwoSphereHomeomorph.symm point)
                  latitude.1))
          ∂(volume.comap ((↑) : LatitudeAngle → Real))
        ∂(volume : Measure EuclideanR3).toSphere := by
  have hSphereMeasure : MeasurePreserving tailNormalSphereEquiv
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
  rw [← hSphereMeasure.lintegral_comp hIntegrand]
  rw [productEquatorialLatitude_lintegral
    (integrand ∘ tailNormalSphereEquiv.symm)
    (hIntegrand.comp tailNormalSphereEquiv.symm.measurable)]
  apply lintegral_congr
  intro point
  apply lintegral_congr
  intro latitude
  rw [Function.comp_apply]
  congr 2
  exact tailNormalSphereEquiv.injective
    (by rw [tailNormalSphereEquiv_standardLatitude,
      tailNormalSphereEquiv.apply_symm_apply])

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
  apply Measure.ext
  intro measurableSet hMeasurableSet
  rw [Measure.map_apply (by fun_prop) hMeasurableSet]
  rw [Measure.withDensity_apply _
    ((by fun_prop : Measurable standardEquatorialLatitude) hMeasurableSet)]
  rw [standardEquatorialLatitude_lintegral
    (measurableSet.indicator (fun _ => (1 : ENNReal)))
    (measurable_const.indicator hMeasurableSet)]
  rw [lintegral_prod]
  apply lintegral_congr
  intro point
  rw [lintegral_restrict]
  · rw [Measure.lintegral_withDensity_eq_lintegral_mul]
    · rfl
    · fun_prop
    · fun_prop
  · exact measurableSet_Ioo

end
end P0EFTJanusMeasureToSphereEquatorialCoarea4D
end JanusFormal
