import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-!
# Spherical coarea formula in canonical latitude coordinates

For the unit three-sphere, write

`x = (sin ν, cos ν · u)`, `u ∈ S²`, `-π/2 < ν < π/2`.

The surface Jacobian is `cos² ν`.  Hence

`dσ₃ = cos² ν dσ₂ dν`.

The proof below compares two polar decompositions of four-dimensional Lebesgue
measure.  First decompose `ℝ⁴` radially.  Second split off the first coordinate,
use the radial decomposition of the remaining `ℝ³`, and use planar polar
coordinates on `(‖y‖,x₀)`.  The planar Jacobian contributes `r`, the
three-dimensional radial density contributes `(r cos ν)²`, and their product is
`r³ cos² ν`; the common `r³` radial measure cancels.

On the collar `0 < ν ≤ 1`, `cos ν ≥ cos 1 > 0`, so the unweighted latitude
measure is bounded by `cos(1)⁻²` times the spherical surface measure.  Taking the
product with the fundamental time interval and pushing to the mapping torus
proves the exact measure domination required by the physical H1 trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeMeasureToSphereCoarea4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1
private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1
private abbrev PositiveRadius := Set.Ioi (0 : Real)
private abbrev LatitudeAngle := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-- Standard spherical latitude map. -/
def standardEquatorialLatitude
    (parameter : StandardSphere2 × Real) : StandardSphere3 :=
  unitThreeSphereHomeomorph
    (equatorialLatitude
      (equatorialTwoSphereHomeomorph.symm parameter.1) parameter.2)

/-- Latitude weight appearing in the spherical surface measure. -/
def standardEquatorialLatitudeWeight
    (parameter : StandardSphere2 × Real) : ENNReal :=
  ENNReal.ofReal (Real.cos parameter.2 ^ 2)

/-- The standard latitude map is continuous. -/
theorem standardEquatorialLatitude_continuous :
    Continuous standardEquatorialLatitude := by
  exact unitThreeSphereHomeomorph.continuous.comp
    (equatorialLatitude_joint_continuous.comp
      ((equatorialTwoSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
        continuous_snd))

/-- Measurability of the latitude weight. -/
theorem standardEquatorialLatitudeWeight_measurable :
    Measurable standardEquatorialLatitudeWeight := by
  fun_prop

/-- Compactly supported radial normalizer.  Its integral against the
four-dimensional radial measure `r³ dr` is one. -/
def canonicalLatitudeRadialNormalizer
    (radius : PositiveRadius) : ENNReal :=
  if radius.1 < 1 then 4 else 0

/-- The radial normalizer has unit mass for `volumeIoiPow 3`. -/
theorem lintegral_canonicalLatitudeRadialNormalizer :
    ∫⁻ radius : PositiveRadius,
        canonicalLatitudeRadialNormalizer radius
        ∂Measure.volumeIoiPow 3 = 1 := by
  let oneRadius : PositiveRadius := ⟨1, one_pos⟩
  have hIndicator : canonicalLatitudeRadialNormalizer =
      (Set.Iio oneRadius).indicator (fun _ => (4 : ENNReal)) := by
    funext radius
    simp [canonicalLatitudeRadialNormalizer, oneRadius]
  rw [hIndicator, lintegral_indicator measurableSet_Iio]
  simp [Measure.volumeIoiPow_apply_Iio, oneRadius]

/-- The planar polar target restricted by positive first Cartesian coordinate is
exactly the latitude angle strip. -/
theorem polarCoord_positive_first_iff_latitude
    (polar : Real × Real)
    (hPolar : polar ∈ Real.polarCoord.target) :
    0 < (Real.polarCoord.symm polar).1 ↔
      polar.2 ∈ LatitudeAngle := by
  rw [Real.polarCoord_symm_apply]
  have hRadius : 0 < polar.1 := hPolar.1
  constructor
  · intro hPositive
    have hCos : 0 < Real.cos polar.2 := by
      have : 0 < polar.1 * Real.cos polar.2 := by
        simpa using hPositive
      exact (mul_pos_iff.mp this).resolve_right
        (not_and_or.mpr (Or.inl hRadius.not_lt)) |>.2
    exact Real.cos_pos_iff.mp hCos |>.resolve_left (by
      intro hBad
      rcases hBad with ⟨integer, hInteger⟩
      have hRange := hPolar.2
      rw [hInteger] at hRange
      omega)
  · intro hAngle
    have hCos : 0 < Real.cos polar.2 :=
      Real.cos_pos_of_mem_Ioo hAngle
    simpa using mul_pos hRadius hCos

/-- Auxiliary form of the latitude factor after planar polar substitution. -/
theorem polarCoord_positive_first_sq
    (polar : Real × Real)
    (hPolar : polar ∈ Real.polarCoord.target)
    (hLatitude : polar.2 ∈ LatitudeAngle) :
    ENNReal.ofReal ((Real.polarCoord.symm polar).1 ^ 2) =
      ENNReal.ofReal (polar.1 ^ 2 * Real.cos polar.2 ^ 2) := by
  rw [Real.polarCoord_symm_apply]
  simp only [Prod.fst_mul, Complex.ofReal_mul, Complex.ofReal_re,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, sub_zero]
  congr 1
  ring

/-- Tonelli-polar calculation underlying the equatorial coarea formula.

This is the only long measure calculation in the file.  The two uses of
`Measure.measurePreserving_homeomorphUnitSphereProd` are the radial changes in
`ℝ³` and `ℝ⁴`; `Real.lintegral_comp_polarCoord_symm` is the planar polar change
in `(‖y‖,x₀)`. -/
private theorem standardEquatorialLatitude_lintegral
    (integrand : StandardSphere3 → ENNReal)
    (hIntegrand : Measurable integrand) :
    ∫⁻ point : StandardSphere3, integrand point
        ∂(volume : Measure EuclideanR4).toSphere =
      ∫⁻ parameter : StandardSphere2 × Real,
        standardEquatorialLatitudeWeight parameter *
          integrand (standardEquatorialLatitude parameter)
        ∂((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict LatitudeAngle)) := by
  classical
  let radialNormalizer : PositiveRadius → ENNReal :=
    canonicalLatitudeRadialNormalizer
  have hRadialNormalizer : Measurable radialNormalizer := by
    unfold radialNormalizer canonicalLatitudeRadialNormalizer
    fun_prop
  have hRadialMass :
      ∫⁻ radius : PositiveRadius, radialNormalizer radius
          ∂Measure.volumeIoiPow 3 = 1 :=
    lintegral_canonicalLatitudeRadialNormalizer
  have hPolar4 :=
    Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (volume : Measure EuclideanR4))
  have hPolar3 :=
    Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (volume : Measure EuclideanR3))
  have hSphereRadial :
      ∫⁻ point : StandardSphere3, integrand point
          ∂(volume : Measure EuclideanR4).toSphere =
        ∫⁻ polar : StandardSphere3 × PositiveRadius,
          radialNormalizer polar.2 * integrand polar.1
          ∂((volume : Measure EuclideanR4).toSphere.prod
            (Measure.volumeIoiPow 3)) := by
    rw [lintegral_prod]
    apply lintegral_congr
    intro point
    rw [← ENNReal.one_mul (integrand point), ← hRadialMass]
    simp_rw [← lintegral_const_mul]
    congr 1
    funext radius
    ac_rfl
  rw [hSphereRadial]
  rw [← hPolar4.lintegral_comp_emb
    (homeomorphUnitSphereProd EuclideanR4).measurableEmbedding]
  rw [lintegral_subtype_comap
    (measurableSet_singleton (0 : EuclideanR4)).compl]
  rw [← (WithLp.volume_preserving_toLp EuclideanR3 Real).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (EuclideanR3 × Real)).measurableEmbedding]
  rw [lintegral_prod]
  apply lintegral_congr
  intro normalVector
  have hR3Slice := hPolar3.lintegral_comp_emb
    (homeomorphUnitSphereProd EuclideanR3).measurableEmbedding
    (fun polar : StandardSphere2 × PositiveRadius =>
      let radius := polar.2.1
      let cartesian : Real × Real := (radius, normalVector)
      if hPositive : 0 < cartesian.1 then
        ENNReal.ofReal (cartesian.1 ^ 2) *
          radialNormalizer
            ⟨Real.sqrt (cartesian.1 ^ 2 + cartesian.2 ^ 2), by positivity⟩ *
          integrand
            (standardEquatorialLatitude
              (polar.1, Real.arctan (cartesian.2 / cartesian.1)))
      else 0)
  rw [← hR3Slice]
  rw [lintegral_subtype_comap
    (measurableSet_singleton (0 : EuclideanR3)).compl]
  rw [← lintegral_prod]
  let planarIntegrand : Real × Real → ENNReal := fun cartesian =>
    if hPositive : 0 < cartesian.1 then
      ENNReal.ofReal (cartesian.1 ^ 2) *
        radialNormalizer
          ⟨Real.sqrt (cartesian.1 ^ 2 + cartesian.2 ^ 2), by positivity⟩ *
        integrand
          (standardEquatorialLatitude
            (⟨(cartesian.1)⁻¹ • (0 : EuclideanR3), by simp⟩,
              Real.arctan (cartesian.2 / cartesian.1)))
    else 0
  have hPlanar := Real.lintegral_comp_polarCoord_symm planarIntegrand
  rw [← hPlanar]
  rw [lintegral_prod]
  apply lintegral_congr
  intro spherePoint
  rw [lintegral_prod]
  apply lintegral_congr
  intro radius
  rw [lintegral_restrict]
  · apply lintegral_congr
    intro latitude
    have hLatitude : latitude ∈ LatitudeAngle := by assumption
    have hCos : 0 < Real.cos latitude :=
      Real.cos_pos_of_mem_Ioo hLatitude
    have hRadius : 0 < radius.1 := radius.2
    simp only [standardEquatorialLatitudeWeight]
    rw [ENNReal.ofReal_mul (sq_nonneg radius.1)]
    rw [← ENNReal.mul_assoc]
    congr 1
    · rw [ENNReal.ofReal_pow (le_of_lt hRadius)]
      ring
    · congr 1
      · apply Subtype.ext
        simp [standardEquatorialLatitude, Real.polarCoord_symm_apply,
          Real.norm_eq_abs, abs_of_pos hRadius, hCos]
      · simp [radialNormalizer, canonicalLatitudeRadialNormalizer,
          Real.polarCoord_symm_apply, Real.norm_eq_abs,
          abs_of_pos hRadius, hCos]
  · exact measurableSet_Ioo

/-- Exact surface-measure formula in standard latitude coordinates. -/
theorem standardEquatorialLatitude_weighted_map :
    Measure.map standardEquatorialLatitude
      (((volume : Measure EuclideanR3).toSphere.prod
        (volume.restrict LatitudeAngle)).withDensity
          standardEquatorialLatitudeWeight) =
      (volume : Measure EuclideanR4).toSphere := by
  apply Measure.ext
  intro measurableSet hMeasurableSet
  rw [Measure.map_apply standardEquatorialLatitude_continuous.measurable
      hMeasurableSet,
    Measure.withDensity_apply _
      (standardEquatorialLatitude_continuous.measurable hMeasurableSet)]
  have hFormula := standardEquatorialLatitude_lintegral
    (fun point => measurableSet.indicator (fun _ => (1 : ENNReal)) point)
    (measurable_const.indicator hMeasurableSet)
  simpa [standardEquatorialLatitudeWeight, Set.indicator_comp_of_preimage]
    using hFormula.symm

/-- `cos 1` is strictly positive. -/
theorem cos_one_pos : 0 < Real.cos (1 : Real) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_gt_three]

/-- On the physical collar `0 < ν ≤ 1`, the latitude density is bounded below
by `cos² 1`. -/
theorem cos_one_sq_le_cos_sq
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    Real.cos (1 : Real) ^ 2 ≤ Real.cos normal ^ 2 := by
  have hPi : (1 : Real) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hCos : Real.cos (1 : Real) ≤ Real.cos normal :=
    Real.cos_le_cos_of_nonneg_of_le_pi hNormal.1 hPi hNormal.2
  nlinarith [cos_one_pos, Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_gt_three])]

/-- Pointwise reciprocal-density estimate used to remove the Jacobian weight. -/
theorem one_le_coareaConstant_mul_weight
    {normal : Real} (hNormal : normal ∈ Set.Ioc (0 : Real) 1) :
    (1 : ENNReal) ≤
      canonicalLatitudeCoareaMeasureConstant *
        ENNReal.ofReal (Real.cos normal ^ 2) := by
  have hCosOne : Real.cos (1 : Real) ≠ 0 := ne_of_gt cos_one_pos
  have hLower := cos_one_sq_le_cos_sq hNormal
  rw [canonicalLatitudeCoareaMeasureConstant]
  norm_cast
  have hInvNonnegative : 0 ≤ (Real.cos (1 : Real))⁻¹ ^ 2 := sq_nonneg _
  rw [← ENNReal.ofReal_mul hInvNonnegative]
  apply ENNReal.ofReal_le_ofReal
  field_simp
  nlinarith

/-- Unweighted positive latitude measure is dominated by the reciprocal minimum
of the spherical Jacobian. -/
theorem standardEquatorialLatitude_positiveCollar_map_le :
    Measure.map standardEquatorialLatitude
        ((volume : Measure EuclideanR3).toSphere.prod
          (volume.restrict (Set.Ioc (0 : Real) 1))) ≤
      canonicalLatitudeCoareaMeasureConstant •
        (volume : Measure EuclideanR4).toSphere := by
  let baseMeasure :=
    (volume : Measure EuclideanR3).toSphere.prod
      (volume.restrict LatitudeAngle)
  let collar : Set (StandardSphere2 × Real) :=
    Set.univ ×ˢ Set.Ioc (0 : Real) 1
  have hCollarMeasurable : MeasurableSet collar :=
    measurableSet_univ.prod measurableSet_Ioc
  have hCollarSubset : collar ⊆ Set.univ ×ˢ LatitudeAngle := by
    rintro ⟨spherePoint, normal⟩ ⟨-, hNormal⟩
    exact ⟨Set.mem_univ _, by
      constructor <;> nlinarith [hNormal.1, hNormal.2, Real.pi_gt_three]⟩
  have hDensity :
      (baseMeasure.restrict collar) ≤
        canonicalLatitudeCoareaMeasureConstant •
          (baseMeasure.withDensity
            standardEquatorialLatitudeWeight).restrict collar := by
    rw [← Measure.withDensity_one (baseMeasure.restrict collar),
      Measure.restrict_withDensity' collar]
    calc
      (baseMeasure.restrict collar).withDensity 1 ≤
          (baseMeasure.restrict collar).withDensity
            (fun parameter =>
              canonicalLatitudeCoareaMeasureConstant *
                standardEquatorialLatitudeWeight parameter) := by
        apply Measure.withDensity_mono
        filter_upwards [ae_restrict_mem hCollarMeasurable] with parameter hParameter
        exact one_le_coareaConstant_mul_weight hParameter.2
      _ = canonicalLatitudeCoareaMeasureConstant •
          (baseMeasure.restrict collar).withDensity
            standardEquatorialLatitudeWeight := by
        rw [Measure.smul_withDensity]
        congr
  have hMap := Measure.map_mono hDensity
  rw [Measure.map_smul] at hMap
  have hWeightedMap := standardEquatorialLatitude_weighted_map
  have hRestrictedMap :
      Measure.map standardEquatorialLatitude
          ((baseMeasure.withDensity standardEquatorialLatitudeWeight).restrict collar) ≤
        (volume : Measure EuclideanR4).toSphere := by
    calc
      Measure.map standardEquatorialLatitude
          ((baseMeasure.withDensity standardEquatorialLatitudeWeight).restrict collar) ≤
        Measure.map standardEquatorialLatitude
          (baseMeasure.withDensity standardEquatorialLatitudeWeight) :=
        Measure.map_mono (Measure.restrict_le_self)
      _ = _ := hWeightedMap
  simpa [baseMeasure, collar, Measure.prod_restrict_right,
    hCollarSubset] using hMap.trans
      (Measure.smul_mono hRestrictedMap)

private abbrev sphereData (period : Real) (hPeriod : period ≠ 0) :=
  reflectedSphereData period hPeriod
private abbrev EffectiveQuotient (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (sphereData period hPeriod)

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- Public spelling of the fundamental-domain map used in the intrinsic Lorentz
volume measure. -/
def canonicalLorentzFundamentalDomainMap
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : StandardSphere3 × Real) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    ((coverHomeomorphProd (sphereData period hPeriod)).symm
      (unitThreeSphereHomeomorph.symm parameter.1, parameter.2))

/-- The intrinsic Lorentz volume is the pushforward by the public
fundamental-domain map. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap
    (period : Real) (hPeriod : period ≠ 0) :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod =
      Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
        ((volume : Measure EuclideanR4).toSphere.prod
          (volume.restrict (canonicalLatitudeTimeInterval period))) := by
  rfl

/-- Reassociation of latitude, time and normal coordinates. -/
def canonicalLatitudeCollarReassociate
    (parameter : CanonicalLatitudeCollarParameter) :
    (StandardSphere2 × Real) × Real :=
  ((parameter.1.1, parameter.2), parameter.1.2)

/-- The collar map factors through the standard latitude map and the public
fundamental-domain map. -/
theorem canonicalLatitudeCollarMap_factor
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : CanonicalLatitudeCollarParameter) :
    canonicalLatitudeCollarMap period hPeriod parameter =
      canonicalLorentzFundamentalDomainMap period hPeriod
        (standardEquatorialLatitude
          (canonicalLatitudeCollarReassociate parameter).1,
          (canonicalLatitudeCollarReassociate parameter).2) := by
  rfl

/-- Product/reassociation version of the positive-collar domination. -/
theorem canonicalLatitudeCollarReassociate_map_le
    (period : Real) :
    Measure.map canonicalLatitudeCollarReassociate
        (canonicalLatitudeCollarMeasure period) ≤
      canonicalLatitudeCoareaMeasureConstant •
        (((volume : Measure EuclideanR4).toSphere.prod
          (volume.restrict (canonicalLatitudeTimeInterval period)))) := by
  rw [canonicalLatitudeCollarMeasure]
  rw [← Measure.prod_assoc]
  rw [Measure.map_prod_map]
  exact Measure.prod_mono
    standardEquatorialLatitude_positiveCollar_map_le le_rfl

/-- The exact spherical coarea domination required by the physical H1 trace. -/
theorem canonicalLatitudeMeasureToSphereCoareaDomination
    (period : Real) (hPeriod : period ≠ 0) :
    CanonicalLatitudeMeasureToSphereCoareaDomination period hPeriod := by
  unfold CanonicalLatitudeMeasureToSphereCoareaDomination
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap]
  calc
    Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeCollarMeasure period) =
      Measure.map
        (fun parameter : (StandardSphere2 × Real) × Real =>
          canonicalLorentzFundamentalDomainMap period hPeriod
            (standardEquatorialLatitude parameter.1, parameter.2))
        (Measure.map canonicalLatitudeCollarReassociate
          (canonicalLatitudeCollarMeasure period)) := by
      rw [Measure.map_map]
      · congr 1
        funext parameter
        exact canonicalLatitudeCollarMap_factor period hPeriod parameter
      · exact continuous_canonicalLatitudeCollarReassociate.measurable
      · exact canonicalLatitudeCollarMap_continuous period hPeriod |>.measurable
    _ ≤ Measure.map
        (fun parameter : StandardSphere3 × Real =>
          canonicalLorentzFundamentalDomainMap period hPeriod parameter)
        (canonicalLatitudeCoareaMeasureConstant •
          ((volume : Measure EuclideanR4).toSphere.prod
            (volume.restrict (canonicalLatitudeTimeInterval period)))) :=
      Measure.map_mono (canonicalLatitudeCollarReassociate_map_le period)
    _ = canonicalLatitudeCoareaMeasureConstant •
        Measure.map (canonicalLorentzFundamentalDomainMap period hPeriod)
          ((volume : Measure EuclideanR4).toSphere.prod
            (volume.restrict (canonicalLatitudeTimeInterval period))) := by
      rw [Measure.map_smul]
      rfl

/-- The former measure-theoretic frontier is now unconditional. -/
theorem canonicalPhysicalScalarLatitudeCoareaTheorem
    (period : Real) (hPeriod : period ≠ 0) :
    P0EFTJanusMappingTorusCanonicalPhysicalH1TraceCoareaClosure4D.CanonicalPhysicalScalarLatitudeCoareaTheorem
      period hPeriod :=
  canonicalLatitudeMeasureToSphereCoareaDomination period hPeriod

end
end P0EFTJanusMappingTorusCanonicalLatitudeMeasureToSphereCoarea4D
end JanusFormal
