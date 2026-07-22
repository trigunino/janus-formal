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

open scoped ENNReal Pointwise
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

@[simp] theorem unitThreeSphereHomeomorph_coe
    (point : UnitThreeSphere) :
    (unitThreeSphereHomeomorph point).1 =
      (EuclideanSpace.equiv (Fin 4) Real).symm point.1 :=
  rfl

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
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  map_smul' scalar point := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  norm_map' point := by
    change ‖WithLp.toLp 2
        ((EuclideanSpace.equiv (Fin 3) Real).symm
            (fun index =>
              (EuclideanSpace.equiv (Fin 4) Real point) index.succ),
          (EuclideanSpace.equiv (Fin 4) Real point) 0)‖ = ‖point‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      WithLp.prod_norm_sq_eq_of_L2,
      EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, WithLp.ofLp_toLp]
    change
      (∑ index : Fin 3,
          (EuclideanSpace.equiv (Fin 4) Real point index.succ) ^ 2) +
        ‖(EuclideanSpace.equiv (Fin 4) Real point) 0‖ ^ 2 =
      (∑ index : Fin 4,
        (EuclideanSpace.equiv (Fin 4) Real point index) ^ 2)
    rw [Real.norm_eq_abs, sq_abs]
    conv_rhs => rw [Fin.sum_univ_succ]
    ring

/-- The induced equivalence of unit spheres. -/
noncomputable def tailNormalSphereEquiv : Sphere3 ≃ᵐ ProductSphere3 where
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
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact tailNormalLinearIsometryEquiv.continuous.measurable.comp
      measurable_subtype_coe
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact tailNormalLinearIsometryEquiv.symm.continuous.measurable.comp
      measurable_subtype_coe

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
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply (EuclideanSpace.equiv (Fin 3) Real).injective
    funext index
    simp [tailNormalSphereEquiv, tailNormalLinearIsometryEquiv,
      productEquatorialLatitude, equatorialLatitude,
      equatorialTwoSphereHomeomorph_symm_tail]
  · simp [tailNormalSphereEquiv, tailNormalLinearIsometryEquiv,
      productEquatorialLatitude, equatorialLatitude]

/-! ## The two-dimensional weighted polar change -/

/-- The polar strip corresponding to positive first Cartesian coordinate. -/
def latitudePolarStrip : Set (Real × Real) :=
  Set.Ioi (0 : Real) ×ˢ LatitudeAngle

/-- The positive Cartesian half-plane. -/
def positiveCartesianHalfPlane : Set (Real × Real) :=
  Set.Ioi (0 : Real) ×ˢ Set.univ

theorem measurableSet_latitudePolarStrip :
    MeasurableSet latitudePolarStrip :=
  measurableSet_Ioi.prod measurableSet_Ioo

theorem measurableSet_positiveCartesianHalfPlane :
    MeasurableSet positiveCartesianHalfPlane :=
  measurableSet_Ioi.prod MeasurableSet.univ

/-- Source density `r³ cos² ν` in latitude-polar variables. -/
def latitudePolarDensity (parameter : Real × Real) : ENNReal :=
  ENNReal.ofReal (parameter.1 ^ 3 * Real.cos parameter.2 ^ 2)

/-- Target density `ρ²` after splitting the three-dimensional radial variable. -/
def cylindricalDensity (parameter : Real × Real) : ENNReal :=
  ENNReal.ofReal (parameter.1 ^ 2)

/-- Measurability of the inverse planar polar map. -/
theorem measurable_polarCoord_symm : Measurable polarCoord.symm :=
  continuous_polarCoord_symm.measurable

/-- On the ordinary polar target, positivity of the first Cartesian coordinate
is equivalent to the latitude-angle condition. -/
theorem polarCoord_symm_mem_positiveHalfPlane_iff
    {parameter : Real × Real}
    (hParameter : parameter ∈ polarCoord.target) :
    polarCoord.symm parameter ∈ positiveCartesianHalfPlane ↔
      parameter ∈ latitudePolarStrip := by
  have hRadius : 0 < parameter.1 := hParameter.1
  rw [polarCoord_symm_apply]
  simp only [positiveCartesianHalfPlane, latitudePolarStrip, Set.mem_prod,
    Set.mem_Ioi, Set.mem_univ, and_true]
  simp only [hRadius, true_and]
  constructor
  · intro hProduct
    constructor
    · by_contra hLower
      have hNonpos : Real.cos parameter.2 ≤ 0 := by
        rw [← Real.cos_neg]
        exact Real.cos_nonpos_of_pi_div_two_le_of_le
          (by linarith) (by linarith [hParameter.2.1, Real.pi_pos])
      exact (not_lt_of_ge
        (mul_nonpos_of_nonneg_of_nonpos hRadius.le hNonpos)) hProduct
    · by_contra hUpper
      have hNonpos : Real.cos parameter.2 ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le
          (by linarith) (by linarith [hParameter.2.2, Real.pi_pos])
      exact (not_lt_of_ge
        (mul_nonpos_of_nonneg_of_nonpos hRadius.le hNonpos)) hProduct
  · intro hLatitude
    exact mul_pos hRadius (Real.cos_pos_of_mem_Ioo hLatitude)

/-- Pointwise Jacobian-density identity for the weighted planar polar change. -/
theorem polarCoord_density_identity
    {parameter : Real × Real}
    (hParameter : parameter ∈ polarCoord.target)
    (hLatitude : parameter ∈ latitudePolarStrip) :
    ENNReal.ofReal parameter.1 *
        cylindricalDensity (polarCoord.symm parameter) =
      latitudePolarDensity parameter := by
  have hRadius : 0 ≤ parameter.1 := hParameter.1.le
  rw [polarCoord_symm_apply]
  unfold cylindricalDensity latitudePolarDensity
  simp only [Prod.fst_mul, Complex.ofReal_mul, Complex.ofReal_re,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, sub_zero]
  rw [← ENNReal.ofReal_mul hRadius]
  apply congrArg ENNReal.ofReal
  ring

/-- The exact weighted planar polar measure identity. -/
theorem map_polarCoord_symm_latitudeMeasure :
    Measure.map polarCoord.symm
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
  let targetIntegrand : Real × Real → ENNReal := fun point =>
    positiveCartesianHalfPlane.indicator
      (fun point => cylindricalDensity point *
        measurableSet.indicator (fun _ => (1 : ENNReal)) point) point
  let sourceIntegrand : Real × Real → ENNReal := fun parameter =>
    latitudePolarStrip.indicator
      (fun point => latitudePolarDensity point *
        (polarCoord.symm ⁻¹' measurableSet).indicator
          (fun _ => (1 : ENNReal)) point) parameter
  have hPolar := lintegral_comp_polarCoord_symm targetIntegrand
  have hPointwise : ∀ parameter ∈ polarCoord.target,
      ENNReal.ofReal parameter.1 * targetIntegrand (polarCoord.symm parameter) =
        sourceIntegrand parameter := by
    intro parameter hParameter
    by_cases hLatitude : parameter ∈ latitudePolarStrip
    · have hPositive :=
        (polarCoord_symm_mem_positiveHalfPlane_iff hParameter).2 hLatitude
      simp only [sourceIntegrand, targetIntegrand]
      rw [Set.indicator_of_mem hPositive, Set.indicator_of_mem hLatitude]
      by_cases hSet : polarCoord.symm parameter ∈ measurableSet
      · have hPreimage : parameter ∈ polarCoord.symm ⁻¹' measurableSet := hSet
        rw [Set.indicator_of_mem hSet, Set.indicator_of_mem hPreimage]
        simpa [mul_assoc] using polarCoord_density_identity hParameter hLatitude
      · have hPreimage : parameter ∉ polarCoord.symm ⁻¹' measurableSet := hSet
        rw [Set.indicator_of_notMem hSet, Set.indicator_of_notMem hPreimage]
        simp
    · have hNotPositive :
          polarCoord.symm parameter ∉ positiveCartesianHalfPlane :=
        mt (polarCoord_symm_mem_positiveHalfPlane_iff hParameter).1 hLatitude
      simp only [sourceIntegrand, targetIntegrand]
      rw [Set.indicator_of_notMem hNotPositive,
        Set.indicator_of_notMem hLatitude]
      simp
  have hTargetSubset : latitudePolarStrip ⊆ polarCoord.target := by
    rintro parameter ⟨hRadius, hLatitude⟩
    exact ⟨hRadius, by
      constructor <;> nlinarith [hLatitude.1, hLatitude.2, Real.pi_pos]⟩
  have hSourceSupport : ∀ parameter ∉ polarCoord.target,
      sourceIntegrand parameter = 0 := by
    intro parameter hNotTarget
    simp only [sourceIntegrand]
    rw [Set.indicator_of_notMem]
    exact fun hLatitude => hNotTarget (hTargetSubset hLatitude)
  have hIntegral : (∫⁻ parameter, sourceIntegrand parameter) =
      ∫⁻ point, targetIntegrand point := by
    calc
      _ = ∫⁻ parameter in polarCoord.target, sourceIntegrand parameter := by
        rw [← lintegral_indicator polarCoord.open_target.measurableSet]
        apply lintegral_congr
        intro parameter
        by_cases hTarget : parameter ∈ polarCoord.target
        · rw [Set.indicator_of_mem hTarget]
        · rw [Set.indicator_of_notMem hTarget, hSourceSupport parameter hTarget]
      _ = ∫⁻ parameter in polarCoord.target,
          ENNReal.ofReal parameter.1 *
            targetIntegrand (polarCoord.symm parameter) := by
        exact setLIntegral_congr_fun polarCoord.open_target.measurableSet
          (fun parameter hParameter => (hPointwise parameter hParameter).symm)
      _ = _ := hPolar
  have hPreimageMeasurable : MeasurableSet (polarCoord.symm ⁻¹' measurableSet) :=
    measurable_polarCoord_symm hMeasurableSet
  have hSourceIntegral :
      (∫⁻ parameter in polarCoord.symm ⁻¹' measurableSet,
          latitudePolarDensity parameter ∂volume.restrict latitudePolarStrip) =
        ∫⁻ parameter, sourceIntegrand parameter := by
    calc
      _ = ∫⁻ parameter,
          (polarCoord.symm ⁻¹' measurableSet).indicator
            latitudePolarDensity parameter ∂volume.restrict latitudePolarStrip :=
        (lintegral_indicator hPreimageMeasurable latitudePolarDensity).symm
      _ = ∫⁻ parameter in latitudePolarStrip,
          (polarCoord.symm ⁻¹' measurableSet).indicator
            latitudePolarDensity parameter := rfl
      _ = ∫⁻ parameter in latitudePolarStrip,
          latitudePolarDensity parameter *
            (polarCoord.symm ⁻¹' measurableSet).indicator
              (fun _ => (1 : ENNReal)) parameter := by
        exact setLIntegral_congr_fun measurableSet_latitudePolarStrip
          (fun parameter _ => by
            by_cases hSet : parameter ∈ polarCoord.symm ⁻¹' measurableSet <;>
              simp [hSet])
      _ = _ := by
        simp only [sourceIntegrand]
        exact (lintegral_indicator measurableSet_latitudePolarStrip _).symm
  have hTargetIntegral :
      (∫⁻ point in measurableSet, cylindricalDensity point
          ∂volume.restrict positiveCartesianHalfPlane) =
        ∫⁻ point, targetIntegrand point := by
    calc
      _ = ∫⁻ point, measurableSet.indicator cylindricalDensity point
          ∂volume.restrict positiveCartesianHalfPlane :=
        (lintegral_indicator hMeasurableSet cylindricalDensity).symm
      _ = ∫⁻ point in positiveCartesianHalfPlane,
          measurableSet.indicator cylindricalDensity point := rfl
      _ = ∫⁻ point in positiveCartesianHalfPlane,
          cylindricalDensity point *
            measurableSet.indicator (fun _ => (1 : ENNReal)) point := by
        exact setLIntegral_congr_fun measurableSet_positiveCartesianHalfPlane
          (fun point _ => by
            by_cases hSet : point ∈ measurableSet <;> simp [hSet])
      _ = _ := by
        simp only [targetIntegrand]
        exact (lintegral_indicator measurableSet_positiveCartesianHalfPlane _).symm
  rw [hSourceIntegral, hTargetIntegral]
  exact hIntegral

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
      restrict_compl_singleton]
  change MeasurePreserving
    (fun parameter : Sphere2 × PositiveRadius =>
      parameter.2.1 • parameter.1.1)
    ((volume : Measure EuclideanR3).toSphere.prod (Measure.volumeIoiPow 2))
    (volume : Measure EuclideanR3)
  simpa [homeomorphUnitSphereProd_symm_apply_coe,
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

@[fun_prop] theorem latitudePolarReconstruction_measurable :
    Measurable latitudePolarReconstruction := by
  unfold latitudePolarReconstruction
  fun_prop

/-- Weighted latitude-angle measure. -/
def latitudeAngleMeasure : Measure LatitudeAngle :=
  (volume.comap ((↑) : LatitudeAngle → Real)).withDensity
    (fun angle => ENNReal.ofReal (Real.cos angle.1 ^ 2))

local instance latitudeAngleBaseFinite :
    IsFiniteMeasure (volume.comap ((↑) : LatitudeAngle → Real)) where
  measure_univ_lt_top := by
    rw [comap_subtype_coe_apply measurableSet_Ioo]
    rw [Set.image_univ, Subtype.range_coe_subtype]
    exact measure_Ioo_lt_top

local instance latitudeAngleMeasureSFinite : SFinite latitudeAngleMeasure := by
  unfold latitudeAngleMeasure
  infer_instance

private def latitudePolarSourceInclusion
    (parameter : PositiveRadius × LatitudeAngle) : Real × Real :=
  (parameter.1.1, parameter.2.1)

private def latitudePolarTargetInclusion
    (parameter : PositiveRadius × Real) : Real × Real :=
  (parameter.1.1, parameter.2)

private theorem latitudePolarSourceInclusion_map :
    Measure.map latitudePolarSourceInclusion
        ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure) =
      (volume.restrict latitudePolarStrip).withDensity
        latitudePolarDensity := by
  have hRadialBase : MeasurePreserving ((↑) : PositiveRadius → Real)
      (volume.comap ((↑) : PositiveRadius → Real))
      (volume.restrict (Set.Ioi (0 : Real))) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    exact map_comap_subtype_coe measurableSet_Ioi volume
  have hRadial := measurePreserving_withDensity hRadialBase
    (fun radius : Real => ENNReal.ofReal (radius ^ 3)) (by fun_prop)
  have hRadialMap :
      Measure.map ((↑) : PositiveRadius → Real) (Measure.volumeIoiPow 3) =
        (volume.restrict (Set.Ioi (0 : Real))).withDensity
          (fun radius : Real => ENNReal.ofReal (radius ^ 3)) := by
    simpa [Measure.volumeIoiPow, Function.comp_def] using hRadial.map_eq
  have hAngleBase : MeasurePreserving ((↑) : LatitudeAngle → Real)
      (volume.comap ((↑) : LatitudeAngle → Real))
      (volume.restrict LatitudeAngle) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    exact map_comap_subtype_coe measurableSet_Ioo volume
  have hAngle := measurePreserving_withDensity hAngleBase
    (fun angle : Real => ENNReal.ofReal (Real.cos angle ^ 2)) (by fun_prop)
  have hAngleMap :
      Measure.map ((↑) : LatitudeAngle → Real) latitudeAngleMeasure =
        (volume.restrict LatitudeAngle).withDensity
          (fun angle : Real => ENNReal.ofReal (Real.cos angle ^ 2)) := by
    simpa [latitudeAngleMeasure, Function.comp_def] using hAngle.map_eq
  change Measure.map (Prod.map ((↑) : PositiveRadius → Real)
      ((↑) : LatitudeAngle → Real)) _ = _
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,
    hRadialMap, hAngleMap]
  rw [prod_withDensity (by fun_prop) (by fun_prop), Measure.prod_restrict]
  congr 1
  funext parameter
  unfold latitudePolarDensity
  rw [show parameter.1 ^ 3 * Real.cos parameter.2 ^ 2 =
      Real.cos parameter.2 ^ 2 * parameter.1 ^ 3 by ring,
    ENNReal.ofReal_mul (sq_nonneg _), mul_comm]

private theorem latitudePolarTargetInclusion_map :
    Measure.map latitudePolarTargetInclusion
        ((Measure.volumeIoiPow 2).prod volume) =
      (volume.restrict positiveCartesianHalfPlane).withDensity
        cylindricalDensity := by
  have hRadialBase : MeasurePreserving ((↑) : PositiveRadius → Real)
      (volume.comap ((↑) : PositiveRadius → Real))
      (volume.restrict (Set.Ioi (0 : Real))) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    exact map_comap_subtype_coe measurableSet_Ioi volume
  have hRadial := measurePreserving_withDensity hRadialBase
    (fun radius : Real => ENNReal.ofReal (radius ^ 2)) (by fun_prop)
  have hRadialMap :
      Measure.map ((↑) : PositiveRadius → Real) (Measure.volumeIoiPow 2) =
        (volume.restrict (Set.Ioi (0 : Real))).withDensity
          (fun radius : Real => ENNReal.ofReal (radius ^ 2)) := by
    simpa [Measure.volumeIoiPow, Function.comp_def] using hRadial.map_eq
  change Measure.map (Prod.map ((↑) : PositiveRadius → Real) id) _ = _
  rw [← Measure.map_prod_map _ _ measurable_subtype_coe measurable_id,
    hRadialMap, Measure.map_id]
  rw [prod_withDensity_left (by fun_prop), Measure.restrict_prod_eq_prod_univ]
  congr

/-- The subtype form of the weighted planar polar identity. -/
theorem latitudePolarReconstruction_measurePreserving :
    MeasurePreserving latitudePolarReconstruction
      ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure)
      ((Measure.volumeIoiPow 2).prod volume) := by
  have hTargetEmbedding : MeasurableEmbedding latitudePolarTargetInclusion := by
    change MeasurableEmbedding
      (Prod.map ((↑) : PositiveRadius → Real) id)
    exact MeasurableEmbedding.prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
      (MeasurableEquiv.refl Real).measurableEmbedding
  have hFunction :
      latitudePolarTargetInclusion ∘ latitudePolarReconstruction =
        polarCoord.symm ∘ latitudePolarSourceInclusion := by
    funext parameter
    rw [Function.comp_apply, Function.comp_apply, polarCoord_symm_apply]
    rfl
  have hSourceMeasurable : Measurable latitudePolarSourceInclusion := by
    unfold latitudePolarSourceInclusion
    fun_prop
  refine ⟨latitudePolarReconstruction_measurable, ?_⟩
  apply hTargetEmbedding.map_injective
  calc
    _ = Measure.map
        (latitudePolarTargetInclusion ∘ latitudePolarReconstruction)
        ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure) :=
      Measure.map_map hTargetEmbedding.measurable
        latitudePolarReconstruction_measurable
    _ = Measure.map (polarCoord.symm ∘ latitudePolarSourceInclusion)
        ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure) := by rw [hFunction]
    _ = Measure.map polarCoord.symm
        (Measure.map latitudePolarSourceInclusion
          ((Measure.volumeIoiPow 3).prod latitudeAngleMeasure)) :=
      (Measure.map_map measurable_polarCoord_symm hSourceMeasurable).symm
    _ = (volume.restrict positiveCartesianHalfPlane).withDensity
        cylindricalDensity := by
      rw [latitudePolarSourceInclusion_map,
        map_polarCoord_symm_latitudeMeasure]
    _ = _ := latitudePolarTargetInclusion_map.symm

/-- Reassociate `S² × ((0,∞) × ℝ)` to `(S² × (0,∞)) × ℝ`. -/
def cylindricalReassociate
    (parameter : Sphere2 × (PositiveRadius × Real)) :
    (Sphere2 × PositiveRadius) × Real :=
  ((parameter.1, parameter.2.1), parameter.2.2)

@[fun_prop] theorem cylindricalReassociate_measurable :
    Measurable cylindricalReassociate := by
  unfold cylindricalReassociate
  fun_prop

/-- Reassociation is measure-preserving for product measures. -/
theorem cylindricalReassociate_measurePreserving :
    MeasurePreserving cylindricalReassociate
      ((volume : Measure EuclideanR3).toSphere.prod
        ((Measure.volumeIoiPow 2).prod volume))
      (((volume : Measure EuclideanR3).toSphere.prod
        (Measure.volumeIoiPow 2)).prod volume) := by
  refine ⟨cylindricalReassociate_measurable, ?_⟩
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
  apply WithLp.ofLp_injective 2
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
  exact Measurable.ite
    (measurableSet_lt measurable_subtype_coe measurable_const)
    measurable_const measurable_const

/-- The radial normalizer has total mass one. -/
theorem lintegral_radialNormalizer :
    ∫⁻ radius : PositiveRadius, radialNormalizer radius
        ∂Measure.volumeIoiPow 3 = 1 := by
  let oneRadius : PositiveRadius :=
    ⟨1, by simpa [PositiveRadius] using (zero_lt_one : (0 : Real) < 1)⟩
  have hIndicator : radialNormalizer =
      (Set.Iio oneRadius).indicator (fun _ => (4 : ENNReal)) := by
    funext radius
    unfold radialNormalizer
    by_cases hRadius : radius.1 < 1
    · have hMem : radius ∈ Set.Iio oneRadius := by
        change radius < oneRadius
        exact Subtype.coe_lt_coe.mp (by simpa [oneRadius] using hRadius)
      rw [if_pos hRadius, Set.indicator_of_mem hMem]
    · have hNotMem : radius ∉ Set.Iio oneRadius := by
        intro hMem
        apply hRadius
        change radius < oneRadius at hMem
        have hCoe := Subtype.coe_lt_coe.mpr hMem
        simpa [oneRadius] using hCoe
      rw [if_neg hRadius, Set.indicator_of_notMem hNotMem]
  rw [hIndicator, lintegral_indicator measurableSet_Iio]
  simp [Measure.volumeIoiPow_apply_Iio, oneRadius]
  rw [show (3 + 1 : Real) = 4 by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : Real) < 4)]
  norm_num [ENNReal.mul_inv_cancel]

/-- Probability radial measure used to cancel the common `r³` factor. -/
def normalizedRadialMeasure : Measure PositiveRadius :=
  (Measure.volumeIoiPow 3).withDensity radialNormalizer

local instance normalizedRadialMeasureSFinite :
    SFinite normalizedRadialMeasure := by
  unfold normalizedRadialMeasure
  infer_instance

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

/-- Radial cones over measurable subsets of the split unit sphere are
measurable. -/
theorem measurableSet_productRadialCone
    {s : Set ProductSphere3} (hs : MeasurableSet s) :
    MeasurableSet (Set.Ioo (0 : Real) 1 •
      (((↑) : ProductSphere3 → ProductR4) '' s)) := by
  let oneRadius : PositiveRadius :=
    ⟨1, by simpa [PositiveRadius] using (zero_lt_one : (0 : Real) < 1)⟩
  have hImage :
      Set.Ioo (0 : Real) 1 •
          (((↑) : ProductSphere3 → ProductR4) '' s) =
        radialReconstruction4 '' (s ×ˢ Set.Iio oneRadius) := by
    ext point
    constructor
    · rintro ⟨radius, hRadius, _, ⟨direction, hDirection, rfl⟩, rfl⟩
      let positiveRadius : PositiveRadius := ⟨radius, hRadius.1⟩
      refine ⟨(direction, positiveRadius), ?_, rfl⟩
      refine ⟨hDirection, ?_⟩
      change positiveRadius < oneRadius
      exact Subtype.coe_lt_coe.mp (by
        simpa [oneRadius, positiveRadius] using hRadius.2)
    · rintro ⟨parameter, ⟨hDirection, hRadius⟩, rfl⟩
      refine ⟨parameter.2.1, ?_, parameter.1.1,
        ⟨parameter.1, hDirection, rfl⟩, rfl⟩
      refine ⟨parameter.2.2, ?_⟩
      change parameter.2 < oneRadius at hRadius
      simpa [oneRadius] using Subtype.coe_lt_coe.mpr hRadius
  rw [hImage]
  exact radialReconstruction4_measurableEmbedding.measurableSet_image'
    (hs.prod measurableSet_Iio)

set_option maxHeartbeats 2000000 in
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
  letI : NoAtoms (volume : Measure ProductR4) := ⟨fun point => by
    have hMap := congrArg (fun measure : Measure ProductR4 => measure {point})
      tailNormalLinearIsometryEquiv.measurePreserving.map_eq
    rw [Measure.map_apply tailNormalLinearIsometryEquiv.continuous.measurable
      (measurableSet_singleton point)] at hMap
    calc
      (volume : Measure ProductR4) {point} =
          (volume : Measure EuclideanR4)
            (tailNormalLinearIsometryEquiv ⁻¹' {point}) := hMap.symm
      _ = (volume : Measure EuclideanR4)
          {tailNormalLinearIsometryEquiv.symm point} := by
            congr 1
            ext source
            exact tailNormalLinearIsometryEquiv.toLinearEquiv.toEquiv
              |>.apply_eq_iff_eq_symm_apply
      _ = 0 := measure_singleton _⟩
  have hSubtype : MeasurePreserving
      ((↑) : ({0}ᶜ : Set ProductR4) → ProductR4)
      ((volume : Measure ProductR4).comap (↑))
      (volume : Measure ProductR4) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe
        (measurableSet_singleton (0 : ProductR4)).compl,
      restrict_compl_singleton (μ := (volume : Measure ProductR4))]
  change MeasurePreserving
    (fun parameter : ProductSphere3 × PositiveRadius =>
      parameter.2.1 • parameter.1.1)
    ((volume : Measure ProductR4).toSphere.prod (Measure.volumeIoiPow 3))
    (volume : Measure ProductR4)
  have hFinrank : Module.finrank Real ProductR4 = 4 := by
    calc
      Module.finrank Real ProductR4 =
          Module.finrank Real (EuclideanR3 × Real) :=
        (WithLp.linearEquiv 2 Real (EuclideanR3 × Real)).finrank_eq
      _ = 4 := by simp [EuclideanR3]
  simpa [homeomorphUnitSphereProd_symm_apply_coe,
    Function.comp_def, hFinrank] using hSubtype.comp hPolarSymm

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
        ((Sphere2 × LatitudeAngle) × PositiveRadius) ≃ᵐ
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
  have hFunction :
      (Prod.map id Prod.swap) ∘
          (MeasurableEquiv.prodAssoc :
            ((Sphere2 × LatitudeAngle) × PositiveRadius) ≃ᵐ
              Sphere2 × (LatitudeAngle × PositiveRadius)) =
        latitudeRadiusReassociate := by
    funext parameter
    rfl
  rw [← hFunction]
  exact hSwap.comp hAssoc

/-- Latitude map with the angle subtype exposed. -/
def productEquatorialLatitudeSubtype
    (parameter : Sphere2 × LatitudeAngle) : ProductSphere3 :=
  productEquatorialLatitude (parameter.1, parameter.2.1)

@[fun_prop] theorem productEquatorialLatitude_measurable :
    Measurable productEquatorialLatitude := by
  unfold productEquatorialLatitude
  fun_prop

@[fun_prop] theorem productEquatorialLatitudeSubtype_measurable :
    Measurable productEquatorialLatitudeSubtype := by
  unfold productEquatorialLatitudeSubtype
  exact productEquatorialLatitude_measurable.comp
    (measurable_fst.prodMk measurable_snd.subtype_val)

/-- Latitude and radius as a product map. -/
def productLatitudeRadiusMap
    (parameter : (Sphere2 × LatitudeAngle) × PositiveRadius) :
    ProductSphere3 × PositiveRadius :=
  Prod.map productEquatorialLatitudeSubtype id parameter

@[fun_prop] theorem productLatitudeRadiusMap_measurable :
    Measurable productLatitudeRadiusMap := by
  unfold productLatitudeRadiusMap
  exact (productEquatorialLatitudeSubtype_measurable.comp measurable_fst).prodMk
    measurable_snd

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
  refine ⟨productLatitudeRadiusMap_measurable, ?_⟩
  apply radialReconstruction4_measurableEmbedding.map_injective
  rw [Measure.map_map radialReconstruction4_measurableEmbedding.measurable
      productLatitudeRadiusMap_measurable,
    hComposed.map_eq,
    radialReconstruction4_measurePreserving.map_eq]

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
          change _ = Measure.map
            (Prod.map productEquatorialLatitudeSubtype id)
            (((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure).prod
              normalizedRadialMeasure)
          simpa only [Measure.map_id] using Measure.map_prod_map
            ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure)
            normalizedRadialMeasure
            productEquatorialLatitudeSubtype_measurable
            measurable_id
      _ = _ := hMapNormalized
  have hFirstMarginal := congrArg
    (Measure.map
      (Prod.fst : ProductSphere3 × PositiveRadius → ProductSphere3)) hProduct
  simpa [Measure.map_fst_prod, normalizedRadialMeasure_univ] using hFirstMarginal

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
    exact map_comap_subtype_coe measurableSet_Ioo volume
  simpa [latitudeAngleMeasure, realLatitudeWeight, Function.comp_def] using
    measurePreserving_withDensity hBase realLatitudeWeight
      realLatitudeWeight_measurable

/-- Inclusion of latitude parameters from the angle subtype to real latitude. -/
def latitudeParameterInclusion
    (parameter : Sphere2 × LatitudeAngle) : Sphere2 × Real :=
  (parameter.1, parameter.2.1)

@[fun_prop] theorem latitudeParameterInclusion_measurable :
    Measurable latitudeParameterInclusion := by
  unfold latitudeParameterInclusion
  fun_prop

/-- The inclusion of latitude parameters is measure-preserving. -/
theorem latitudeParameterInclusion_measurePreserving :
    MeasurePreserving latitudeParameterInclusion
      ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure)
      ((volume : Measure EuclideanR3).toSphere.prod
        ((volume.restrict LatitudeAngle).withDensity realLatitudeWeight)) := by
  change MeasurePreserving
    (Prod.map id ((↑) : LatitudeAngle → Real))
    ((volume : Measure EuclideanR3).toSphere.prod latitudeAngleMeasure)
    ((volume : Measure EuclideanR3).toSphere.prod
      ((volume.restrict LatitudeAngle).withDensity realLatitudeWeight))
  exact MeasurePreserving.prod
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
      rw [Measure.map_map productEquatorialLatitude_measurable
        latitudeParameterInclusion_measurable]
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
  let targetCone : Set ProductR4 := Set.Ioo (0 : Real) 1 •
    (((↑) : ProductSphere3 → ProductR4) '' measurableSet)
  let sourceCone : Set EuclideanR4 := Set.Ioo (0 : Real) 1 •
    (((↑) : Sphere3 → EuclideanR4) ''
      (tailNormalSphereEquiv ⁻¹' measurableSet))
  change (Module.finrank Real EuclideanR4 : ENNReal) *
      (volume : Measure EuclideanR4) sourceCone =
    (Module.finrank Real ProductR4 : ENNReal) *
      (volume : Measure ProductR4) targetCone
  have hCone : tailNormalLinearIsometryEquiv ⁻¹' targetCone = sourceCone := by
    ext point
    constructor
    · intro hPoint
      change tailNormalLinearIsometryEquiv point ∈
        Set.Ioo (0 : Real) 1 •
          (((↑) : ProductSphere3 → ProductR4) '' measurableSet) at hPoint
      rcases hPoint with
        ⟨radius, hRadius, _, ⟨direction, hDirection, rfl⟩, hPoint⟩
      refine ⟨radius, hRadius, tailNormalSphereEquiv.symm direction, ?_, ?_⟩
      · refine ⟨tailNormalSphereEquiv.symm direction, ?_, rfl⟩
        change tailNormalSphereEquiv (tailNormalSphereEquiv.symm direction) ∈
          measurableSet
        simpa using hDirection
      · apply tailNormalLinearIsometryEquiv.injective
        simpa [tailNormalSphereEquiv] using hPoint
    · intro hPoint
      rcases hPoint with
        ⟨radius, hRadius, _, ⟨direction, hDirection, rfl⟩, hPoint⟩
      change tailNormalLinearIsometryEquiv point ∈
        Set.Ioo (0 : Real) 1 •
          (((↑) : ProductSphere3 → ProductR4) '' measurableSet)
      refine ⟨radius, hRadius, tailNormalSphereEquiv direction, ?_, ?_⟩
      · refine ⟨tailNormalSphereEquiv direction, hDirection, rfl⟩
      · simpa [tailNormalSphereEquiv] using
          congrArg tailNormalLinearIsometryEquiv hPoint
  have hTargetMeasurable : MeasurableSet targetCone := by
    exact measurableSet_productRadialCone hMeasurableSet
  have hMeasure : (volume : Measure EuclideanR4) sourceCone =
      (volume : Measure ProductR4) targetCone := by
    have hMap := congrArg (fun measure : Measure ProductR4 => measure targetCone)
      tailNormalLinearIsometryEquiv.measurePreserving.map_eq
    rw [Measure.map_apply tailNormalLinearIsometryEquiv.continuous.measurable
      hTargetMeasurable, hCone] at hMap
    exact hMap
  have hEuclideanFinrank : Module.finrank Real EuclideanR4 = 4 := by
    simp [EuclideanR4]
  have hProductFinrank : Module.finrank Real ProductR4 = 4 := by
    calc
      Module.finrank Real ProductR4 =
          Module.finrank Real (EuclideanR3 × Real) :=
        (WithLp.linearEquiv 2 Real (EuclideanR3 × Real)).finrank_eq
      _ = 4 := by simp [EuclideanR3]
  rw [hEuclideanFinrank, hProductFinrank, hMeasure]

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
    simp [Function.comp_apply, standardEquatorialLatitude,
      tailNormalSphereEquiv_standardLatitude]
  rw [show (((volume : Measure EuclideanR3).toSphere.prod
      (volume.restrict LatitudeAngle)).withDensity
        (fun parameter => ENNReal.ofReal (Real.cos parameter.2 ^ 2))) =
      standardLatitudeParameterMeasure by rfl]
  rw [hFactor, ← Measure.map_map tailNormalSphereEquiv.symm.measurable
    productEquatorialLatitude_measurable]
  rw [productEquatorialLatitude_weighted_map]
  exact (MeasurePreserving.symm tailNormalSphereEquiv
    tailNormalSphereEquiv_measurePreserving).map_eq

end
end P0EFTJanusMeasureToSphereEquatorialCoarea4D
end JanusFormal
