import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The one-dimensional core of the canonical physical trace bound

The scalar FTC estimate needed on every normal collar line is proved here.
The remaining geometric input is stated separately: comparison of the
latitude-collar energy with the already installed finite-frame graph norm.
This comparison packages precisely the two APIs not presently supplied by
Mathlib: disintegration of `Measure.toSphere` by latitudes and a quantitative
right inverse for a finite spanning family of tangent sections.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

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
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D

private abbrev sphereData (period : Real) (hPeriod : period ≠ 0) :=
  reflectedSphereData period hPeriod
private abbrev throatData (period : Real) (hPeriod : period ≠ 0) :=
  fixedEquatorData period hPeriod
private abbrev EffectiveQuotient (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorus (throatData period hPeriod)
private abbrev EffectiveCover (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover (period : Real) (hPeriod : period ≠ 0) :=
  MappingTorusCover (throatData period hPeriod)

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance (period : Real) (hPeriod : period ≠ 0) :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance (period : Real) (hPeriod : period ≠ 0) :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance (period : Real) (hPeriod : period ≠ 0) :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance (period : Real) (hPeriod : period ≠ 0) :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The exact one-dimensional `H¹` energy used on a unit normal collar. -/
def unitNormalH1Energy (value derivative : Real → Real) : Real :=
  ∫ coordinate in (0 : Real)..1,
    2 * value coordinate ^ 2 + derivative coordinate ^ 2

/-- The scalar one-dimensional trace estimate.  It is an FTC and
integration-by-parts statement; no Sobolev-space or manifold trace API is
used. -/
theorem unitNormal_point_trace_sq_le
    (value derivative : Real → Real)
    (hValue : ∀ coordinate, HasDerivAt value (derivative coordinate) coordinate)
    (hDerivative : Continuous derivative) :
    value 0 ^ 2 ≤ unitNormalH1Energy value derivative := by
  let product : Real → Real := fun coordinate =>
    (1 - coordinate) * value coordinate ^ 2
  let productDerivative : Real → Real := fun coordinate =>
    -(value coordinate ^ 2) +
      2 * (1 - coordinate) * value coordinate * derivative coordinate
  have hValueContinuous : Continuous value :=
    continuous_iff_continuousAt.2 fun coordinate =>
      (hValue coordinate).continuousAt
  have hProductDerivativeContinuous : Continuous productDerivative := by
    dsimp [productDerivative]
    fun_prop
  have hProductDerivative : ∀ coordinate,
      HasDerivAt product (productDerivative coordinate) coordinate := by
    intro coordinate
    dsimp [product, productDerivative]
    have hRaw :=
      ((hasDerivAt_const coordinate 1).sub (hasDerivAt_id coordinate)).mul
        ((hValue coordinate).pow 2)
    convert! hRaw using 1
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  have hFTC :
      ∫ coordinate in (0 : Real)..1, productDerivative coordinate =
        -(value 0 ^ 2) := by
    have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : Real)) (b := 1)
      (fun coordinate _ => hProductDerivative coordinate)
      (hProductDerivativeContinuous.intervalIntegrable 0 1)
    simpa [product] using hIntegral
  let squareValue : Real → Real := fun coordinate => value coordinate ^ 2
  let cross : Real → Real := fun coordinate =>
    2 * (1 - coordinate) * value coordinate * derivative coordinate
  have hSquareValueContinuous : Continuous squareValue := by
    dsimp [squareValue]
    fun_prop
  have hCrossContinuous : Continuous cross := by
    dsimp [cross]
    fun_prop
  have hIdentity :
      value 0 ^ 2 =
        (∫ coordinate in (0 : Real)..1, squareValue coordinate) -
          ∫ coordinate in (0 : Real)..1, cross coordinate := by
    have hRewritten := hFTC
    change
      (∫ coordinate in (0 : Real)..1,
        -squareValue coordinate + cross coordinate) = -(value 0 ^ 2)
      at hRewritten
    rw [intervalIntegral.integral_add
        (hSquareValueContinuous.neg.intervalIntegrable 0 1)
        (hCrossContinuous.intervalIntegrable 0 1),
      intervalIntegral.integral_neg] at hRewritten
    linarith
  have hPointwise : ∀ coordinate ∈ Set.Icc (0 : Real) 1,
      -cross coordinate ≤
        squareValue coordinate + derivative coordinate ^ 2 := by
    intro coordinate hCoordinate
    have hFirst : 0 ≤
        (1 - coordinate) *
          (value coordinate + derivative coordinate) ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hCoordinate.2) (sq_nonneg _)
    have hSecond : 0 ≤
        coordinate *
          (value coordinate ^ 2 + derivative coordinate ^ 2) :=
      mul_nonneg hCoordinate.1
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    dsimp [cross, squareValue]
    nlinarith
  have hNegativeCross :
      (∫ coordinate in (0 : Real)..1, -cross coordinate) ≤
        ∫ coordinate in (0 : Real)..1,
          squareValue coordinate + derivative coordinate ^ 2 := by
    exact intervalIntegral.integral_mono_on (a := (0 : Real)) (b := 1)
      (by norm_num)
      (hCrossContinuous.neg.intervalIntegrable 0 1)
      ((hSquareValueContinuous.add
        (hDerivative.pow 2)).intervalIntegrable 0 1)
      hPointwise
  rw [hIdentity, sub_eq_add_neg,
    ← intervalIntegral.integral_neg]
  calc
    (∫ coordinate in (0 : Real)..1, squareValue coordinate) +
          ∫ coordinate in (0 : Real)..1, -cross coordinate ≤
        (∫ coordinate in (0 : Real)..1, squareValue coordinate) +
          ∫ coordinate in (0 : Real)..1,
            squareValue coordinate + derivative coordinate ^ 2 :=
      add_le_add_right hNegativeCross _
    _ = unitNormalH1Energy value derivative := by
      unfold unitNormalH1Energy squareValue
      have hDoubleValueContinuous : Continuous
          (fun coordinate => 2 * value coordinate ^ 2) := by
        fun_prop
      rw [intervalIntegral.integral_add
          ((hValueContinuous.pow 2).intervalIntegrable 0 1)
          ((hDerivative.pow 2).intervalIntegrable 0 1),
        intervalIntegral.integral_add
          (hDoubleValueContinuous.intervalIntegrable 0 1)
          ((hDerivative.pow 2).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul]
      ring

/-- Fubini-compatible form of the one-dimensional estimate.  The outer base
may be the physical throat (including its time factor); the inner integral is
only along the unit normal collar. -/
theorem fiberwise_unitNormal_point_trace_sq_le
    {Base : Type*} [MeasurableSpace Base]
    (measure : Measure Base)
    (value derivative : Base → Real → Real)
    (hValue : ∀ base coordinate,
      HasDerivAt (value base) (derivative base coordinate) coordinate)
    (hDerivative : ∀ base, Continuous (derivative base))
    (hTraceIntegrable : Integrable (fun base => value base 0 ^ 2) measure)
    (hEnergyIntegrable : Integrable
      (fun base => unitNormalH1Energy (value base) (derivative base)) measure) :
    (∫ base, value base 0 ^ 2 ∂measure) ≤
      ∫ base, unitNormalH1Energy (value base) (derivative base) ∂measure :=
  integral_mono hTraceIntegrable hEnergyIntegrable fun base =>
    unitNormal_point_trace_sq_le (value base) (derivative base)
      (hValue base) (hDerivative base)

/-! ## The canonical twisted latitude collar -/

/-- Geodesic latitude through an equatorial point.  Coordinate zero is the
normal coordinate and the remaining three coordinates are rescaled by
`cos normal`. -/
def equatorialLatitude
    (point : EquatorialTwoSphere) (normal : Real) : UnitThreeSphere :=
  ⟨Fin.cases (Real.sin normal)
      (fun index => Real.cos normal * point.1 index.succ), by
    unfold OnUnitThreeSphere radiusSquared
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, mul_pow]
    rw [← Finset.mul_sum]
    have hEquator := point.2.1
    unfold OnUnitThreeSphere radiusSquared at hEquator
    rw [Fin.sum_univ_succ] at hEquator
    rw [point.2.2] at hEquator
    norm_num at hEquator
    rw [hEquator]
    nlinarith [Real.sin_sq_add_cos_sq normal]⟩

@[simp]
theorem equatorialLatitude_zero (point : EquatorialTwoSphere) :
    equatorialLatitude point 0 = equatorialSphereInclusion point := by
  apply Subtype.ext
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · simpa [equatorialLatitude, equatorialSphereInclusion] using point.2.2.symm
  · simp [equatorialLatitude, equatorialSphereInclusion]

@[simp]
theorem equatorialTwoSphereHomeomorph_symm_tail
    (point : Metric.sphere (0 : EuclideanR3) 1) (index : Fin 3) :
    (equatorialTwoSphereHomeomorph.symm point).1 index.succ =
      (EuclideanSpace.equiv (Fin 3) Real point.1) index := by
  rfl

/-- Reflection reverses the latitude normal coordinate. -/
theorem sphereReflection_equatorialLatitude
    (point : EquatorialTwoSphere) (normal : Real) :
    sphereReflection (equatorialLatitude point normal) =
      equatorialLatitude point (-normal) := by
  apply Subtype.ext
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · simp [sphereReflection, reflectPoint, equatorialLatitude]
  · simp [sphereReflection, reflectPoint, equatorialLatitude,
      Fin.succ_ne_zero]

/-- Cover-level normal collar before quotienting. -/
def normalLatitudeCover
    (period : Real) (hPeriod : period ≠ 0)
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    EffectiveCover period hPeriod :=
  (coverHomeomorphProd (sphereData period hPeriod)).symm
    (equatorialLatitude anchor.fiber normal, anchor.time)

@[simp]
theorem normalLatitudeCover_zero
    (period : Real) (hPeriod : period ≠ 0)
    (anchor : EffectiveThroatCover period hPeriod) :
    normalLatitudeCover period hPeriod anchor 0 =
      fixedThroatCoverInclusion period hPeriod anchor := by
  apply (coverHomeomorphProd (sphereData period hPeriod)).injective
  apply Prod.ext
  · exact equatorialLatitude_zero anchor.fiber
  · rfl

/-- The generator of the mapping-torus deck action reverses the normal.  This
is why the physical collar must be treated on a fundamental domain rather
than as a globally oriented product over the throat quotient. -/
theorem normalLatitudeCover_deck_generator_twist
    (period : Real) (hPeriod : period ≠ 0)
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    normalLatitudeCover period hPeriod ((1 : Int) +ᵥ anchor) normal =
      (1 : Int) +ᵥ normalLatitudeCover period hPeriod anchor (-normal) := by
  apply MappingTorusCover.ext
  · change equatorialLatitude
        (((Homeomorph.refl EquatorialTwoSphere) ^ (1 : Int)) anchor.fiber) normal =
      (sphereReflection ^ (1 : Int)) (equatorialLatitude anchor.fiber (-normal))
    simp [sphereReflection_equatorialLatitude]
  · rfl

/-- Quotient latitude based at a chosen throat-cover representative. -/
def quotientNormalLatitude
    (period : Real) (hPeriod : period ≠ 0)
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    (normalLatitudeCover period hPeriod anchor normal)

@[simp]
theorem quotientNormalLatitude_zero
    (period : Real) (hPeriod : period ≠ 0)
    (anchor : EffectiveThroatCover period hPeriod) :
    quotientNormalLatitude period hPeriod anchor 0 =
      fixedThroatQuotientInclusion period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor) := by
  simp [quotientNormalLatitude]

/-- The latitude curve is analytic in its normal coordinate. -/
theorem equatorialLatitude_contMDiff (point : EquatorialTwoSphere) :
    ContMDiff 𝓘(Real, Real) (𝓡 3) ∞ (equatorialLatitude point) := by
  letI : Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩
  have hCoordinates : ContMDiff 𝓘(Real, Real) 𝓘(Real, R4Point) ∞
      (fun normal => (equatorialLatitude point normal).1) := by
    apply ContDiff.contMDiff
    rw [contDiff_pi]
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · simpa [equatorialLatitude] using Real.contDiff_sin
    · change ContDiff Real ∞
        (fun normal => Real.cos normal * point.1 tail.succ)
      fun_prop
  have hAmbient : ContMDiff 𝓘(Real, Real) 𝓘(Real, EuclideanR4) ∞
      (fun normal =>
        (unitThreeSphereHomeomorph (equatorialLatitude point normal)).1) := by
    exact (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.contMDiff.comp
      hCoordinates
  have hStandard : ContMDiff 𝓘(Real, Real) (𝓡 3) ∞
      (fun normal =>
        unitThreeSphereHomeomorph (equatorialLatitude point normal)) := by
    exact ContMDiff.codRestrict_sphere hAmbient fun normal =>
      (unitThreeSphereHomeomorph (equatorialLatitude point normal)).2
  have hInv := chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  exact (hInv.comp hStandard).congr fun normal => by simp

def equatorialLatitudeUncurried
    (parameter : EquatorialTwoSphere × Real) : UnitThreeSphere :=
  equatorialLatitude parameter.1 parameter.2

/-- Joint continuity of the explicit latitude collar.  This elementary part
does not require the still-isolated continuity of its tangent lift. -/
theorem equatorialLatitude_joint_continuous :
    Continuous equatorialLatitudeUncurried := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro index
  refine Fin.cases ?_ (fun tail => ?_) index
  · exact Real.continuous_sin.comp continuous_snd
  · exact (Real.continuous_cos.comp continuous_snd).mul
      ((continuous_apply tail.succ).comp
        (continuous_subtype_val.comp continuous_fst))

/-- The cover-level collar curve is analytic for every chosen fundamental
representative. -/
theorem normalLatitudeCover_contMDiff
    (period : Real) (hPeriod : period ≠ 0)
    (anchor : EffectiveThroatCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞
      (normalLatitudeCover period hPeriod anchor) := by
  let productEquiv := coverHomeomorphProd (sphereData period hPeriod)
  have hInv := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ∞ productEquiv
  exact hInv.comp
    ((equatorialLatitude_contMDiff anchor.fiber).prodMk contMDiff_const)

/-- The quotient latitude is analytic for each fundamental representative. -/
theorem quotientNormalLatitude_contMDiff
    (period : Real) (hPeriod : period ≠ 0)
    (anchor : EffectiveThroatCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞
      (quotientNormalLatitude period hPeriod anchor) :=
  (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
    |>.of_le (by simp)
    |>.comp (normalLatitudeCover_contMDiff period hPeriod anchor)

/-- Canonical scalar slice along the explicit twisted collar. -/
def canonicalNormalSlice
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (anchor : EffectiveThroatCover period hPeriod) : Real → Real :=
  fun normal => field (quotientNormalLatitude period hPeriod anchor normal)

theorem canonicalNormalSlice_contDiff
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (anchor : EffectiveThroatCover period hPeriod) :
    ContDiff Real ∞ (canonicalNormalSlice period hPeriod field anchor) := by
  apply ContMDiff.contDiff
  exact (field.contMDiff_toFun.of_le (by simp)).comp (n := ∞)
    (quotientNormalLatitude_contMDiff period hPeriod anchor)

theorem canonicalNormalSlice_hasDerivAt
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    HasDerivAt (canonicalNormalSlice period hPeriod field anchor)
      (deriv (canonicalNormalSlice period hPeriod field anchor) normal) normal :=
  ((canonicalNormalSlice_contDiff period hPeriod field anchor).differentiable
    (by simp)).differentiableAt.hasDerivAt

theorem canonicalNormalSlice_deriv_continuous
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (anchor : EffectiveThroatCover period hPeriod) :
    Continuous (deriv (canonicalNormalSlice period hPeriod field anchor)) :=
  (canonicalNormalSlice_contDiff period hPeriod field anchor).continuous_deriv
    (by simp)

@[simp]
theorem canonicalNormalSlice_zero
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (anchor : EffectiveThroatCover period hPeriod) :
    canonicalNormalSlice period hPeriod field anchor 0 =
      field (fixedThroatQuotientInclusion period hPeriod
        (mappingTorusMk (throatData period hPeriod) anchor)) := by
  simp [canonicalNormalSlice]

/-! ## Fundamental-domain Fubini data -/

/-- The true product parameter space used by the canonical throat measure. -/
abbrev CanonicalLatitudeBase :=
  Metric.sphere (0 : EuclideanR3) 1 × Real

def canonicalLatitudeTimeInterval (period : Real) : Set Real :=
  Set.Ioc (min 0 period) (max 0 period)

/-- Round `S²` measure times one half-open mapping-torus period. -/
def canonicalLatitudeBaseMeasure (period : Real) :
    Measure CanonicalLatitudeBase :=
  ((volume : Measure EuclideanR3).toSphere).prod
    (volume.restrict (canonicalLatitudeTimeInterval period))

/-- One positive unit normal interval, with ordinary Lebesgue measure. -/
def canonicalLatitudeUnitNormalMeasure : Measure Real :=
  volume.restrict (Set.Ioc 0 1)

instance canonicalLatitudeUnitNormalMeasure_isFinite :
    IsFiniteMeasure canonicalLatitudeUnitNormalMeasure := by
  unfold canonicalLatitudeUnitNormalMeasure
  infer_instance

/-- Parameters and product measure of the positive canonical latitude collar. -/
abbrev CanonicalLatitudeCollarParameter := CanonicalLatitudeBase × Real

def canonicalLatitudeCollarMeasure (period : Real) :
    Measure CanonicalLatitudeCollarParameter :=
  (canonicalLatitudeBaseMeasure period).prod
    canonicalLatitudeUnitNormalMeasure

theorem canonicalLatitudeBaseMeasure_isFinite (period : Real) :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) := by
  unfold canonicalLatitudeBaseMeasure canonicalLatitudeTimeInterval
  infer_instance

/-- Chosen throat-cover representative of a fundamental-domain parameter. -/
def canonicalLatitudeAnchor
    (period : Real) (hPeriod : period ≠ 0)
    (base : CanonicalLatitudeBase) : EffectiveThroatCover period hPeriod :=
  (coverHomeomorphProd (throatData period hPeriod)).symm
    (equatorialTwoSphereHomeomorph.symm base.1, base.2)

/-- The whole positive latitude collar as a single map to the quotient. -/
def canonicalLatitudeCollarMap
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : CanonicalLatitudeCollarParameter) :
    EffectiveQuotient period hPeriod :=
  quotientNormalLatitude period hPeriod
    (canonicalLatitudeAnchor period hPeriod parameter.1) parameter.2

theorem canonicalLatitudeCollarMap_continuous
    (period : Real) (hPeriod : period ≠ 0) :
    Continuous (canonicalLatitudeCollarMap period hPeriod) := by
  have hEquator : Continuous
      (fun parameter : CanonicalLatitudeCollarParameter =>
        equatorialTwoSphereHomeomorph.symm parameter.1.1) :=
    equatorialTwoSphereHomeomorph.symm.continuous.comp
      (continuous_fst.comp continuous_fst)
  have hLatitudeInput : Continuous
      (fun parameter : CanonicalLatitudeCollarParameter =>
        (equatorialTwoSphereHomeomorph.symm parameter.1.1,
          parameter.2)) :=
    hEquator.prodMk continuous_snd
  have hLatitude : Continuous
      (equatorialLatitudeUncurried ∘
        fun parameter : CanonicalLatitudeCollarParameter =>
          (equatorialTwoSphereHomeomorph.symm parameter.1.1,
            parameter.2)) :=
    equatorialLatitude_joint_continuous.comp hLatitudeInput
  have hCover : Continuous
      (fun parameter : CanonicalLatitudeCollarParameter =>
        (coverHomeomorphProd (sphereData period hPeriod)).symm
          (equatorialLatitudeUncurried
              (equatorialTwoSphereHomeomorph.symm parameter.1.1,
                parameter.2),
            parameter.1.2)) :=
    (coverHomeomorphProd (sphereData period hPeriod)).symm.continuous.comp
      (hLatitude.prodMk (continuous_snd.comp continuous_fst))
  have hQuotient :=
    (mappingTorusMk_isCoveringMap
      (sphereData period hPeriod)).isLocalHomeomorph.continuous.comp hCover
  change Continuous
    (fun parameter : CanonicalLatitudeCollarParameter =>
      mappingTorusMk (sphereData period hPeriod)
        ⟨equatorialLatitude
            (equatorialTwoSphereHomeomorph.symm parameter.1.1)
            parameter.2,
          parameter.1.2⟩)
  exact hQuotient

/-- Fundamental-domain map to the actual physical throat. -/
def canonicalLatitudeThroatMap
    (period : Real) (hPeriod : period ≠ 0)
    (base : CanonicalLatitudeBase) : EffectiveThroat period hPeriod :=
  mappingTorusMk (throatData period hPeriod)
    (canonicalLatitudeAnchor period hPeriod base)

theorem canonicalLatitudeThroatMap_continuous
    (period : Real) (hPeriod : period ≠ 0) :
    Continuous (canonicalLatitudeThroatMap period hPeriod) := by
  have hProduct : Continuous
      (fun base : CanonicalLatitudeBase =>
        (equatorialTwoSphereHomeomorph.symm base.1, base.2)) :=
    (equatorialTwoSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (throatData period hPeriod)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (throatData period hPeriod)).symm.continuous.comp hProduct)

/-- The already installed canonical throat measure is definitionally the
pushforward of the preceding product measure. -/
theorem intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase
    (period : Real) (hPeriod : period ≠ 0) :
    intrinsicCanonicalThroatVolumeMeasure period hPeriod =
      (canonicalLatitudeBaseMeasure period).map
        (canonicalLatitudeThroatMap period hPeriod) := by
  rfl

/-- Canonical normal slice on the actual product fundamental domain. -/
def canonicalLatitudeValue
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real → Real :=
  canonicalNormalSlice period hPeriod field
    (canonicalLatitudeAnchor period hPeriod base)

def canonicalLatitudeDerivative
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real → Real :=
  deriv (canonicalLatitudeValue period hPeriod field base)

/-- Tangent vector of the canonical latitude curve in the normal direction. -/
def canonicalLatitudeNormalVector
    (period : Real) (hPeriod : period ≠ 0)
    (base : CanonicalLatitudeBase) (normal : Real) :
    TangentSpace coverModelWithCorners
      (quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal) :=
  mfderiv 𝓘(Real, Real) coverModelWithCorners
    (quotientNormalLatitude period hPeriod
      (canonicalLatitudeAnchor period hPeriod base)) normal 1

theorem canonicalLatitudeDerivative_eq_mvfderiv_normal
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeDerivative period hPeriod field base normal =
      mvfderiv coverModelWithCorners field.toFun
        (quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod base) normal)
        (canonicalLatitudeNormalVector period hPeriod base normal) := by
  unfold canonicalLatitudeDerivative
  rw [← fderiv_apply_one_eq_deriv,
    ← mfderiv_eq_fderiv (f := canonicalLatitudeValue period hPeriod field base)]
  exact mfderiv_comp_apply normal
    (field.contMDiff_toFun.mdifferentiable (by simp)
      (quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod base) normal))
    ((quotientNormalLatitude_contMDiff period hPeriod
      (canonicalLatitudeAnchor period hPeriod base)).mdifferentiable
        (by simp) normal) 1

/-- Finite-frame derivative pulled back to the canonical latitude collar. -/
def canonicalLatitudeFrameDerivative
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    Fin (finiteSmoothTangentFrame period hPeriod).count → Real :=
  frameDerivative period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod) field
    (quotientNormalLatitude period hPeriod
      (canonicalLatitudeAnchor period hPeriod base) normal)

/-- Pullback of the finite-frame graph energy to one unit latitude fiber. -/
def unitLatitudeFrameH1Energy
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) : Real :=
  ∫ normal in (0 : Real)..1,
    2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
      ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ ^ 2

/-- The field value is jointly continuous on the whole canonical collar. -/
theorem canonicalLatitudeValue_uncurry_continuous
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (fun parameter : CanonicalLatitudeCollarParameter =>
      canonicalLatitudeValue period hPeriod field
        parameter.1 parameter.2) := by
  change Continuous
    (field.toFun ∘ canonicalLatitudeCollarMap period hPeriod)
  exact field.contMDiff_toFun.continuous.comp
    (canonicalLatitudeCollarMap_continuous period hPeriod)

/-- The implemented finite-frame derivative is jointly continuous on the
whole canonical collar, independently of normal-vector reconstruction. -/
theorem canonicalLatitudeFrameDerivative_uncurry_continuous
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (fun parameter : CanonicalLatitudeCollarParameter =>
      canonicalLatitudeFrameDerivative period hPeriod field
        parameter.1 parameter.2) := by
  change Continuous
    (frameDerivative period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod) field ∘
        canonicalLatitudeCollarMap period hPeriod)
  exact (frameDerivative_contMDiff period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod) field).continuous.comp
      (canonicalLatitudeCollarMap_continuous period hPeriod)

theorem unitLatitudeFrameH1Energy_continuous
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (unitLatitudeFrameH1Energy period hPeriod field) := by
  unfold unitLatitudeFrameH1Energy
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((canonicalLatitudeValue_uncurry_continuous
      period hPeriod field).pow 2).const_mul 2 |>.add
    ((canonicalLatitudeFrameDerivative_uncurry_continuous
      period hPeriod field).norm.pow 2)

/-- The nonnegative first-jet density whose pullback is exactly the latitude
frame integrand. -/
def canonicalPhysicalFrameH1Density
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  2 * field point ^ 2 +
    ‖frameDerivative period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2

theorem canonicalPhysicalFrameH1Density_continuous
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (canonicalPhysicalFrameH1Density period hPeriod field) := by
  exact (field.contMDiff_toFun.continuous.pow 2).const_mul 2 |>.add
    ((frameDerivative_contMDiff period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod) field).continuous.norm.pow 2)

theorem canonicalPhysicalFrameH1Density_nonnegative
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ canonicalPhysicalFrameH1Density period hPeriod field point := by
  unfold canonicalPhysicalFrameH1Density
  positivity

@[simp]
theorem canonicalPhysicalFrameH1Density_collar
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalPhysicalFrameH1Density period hPeriod field
        (canonicalLatitudeCollarMap period hPeriod (base, normal)) =
      2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
        ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ ^ 2 := by
  rfl

/-- Coordinates of the latitude-normal vector in one finite local frame. -/
def canonicalLatitudeLocalNormalCoefficient
    (period : Real) (hPeriod : period ≠ 0)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (basisIndex : FiniteTangentGeneratorBasisIndex)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
    (quotientNormalLatitude period hPeriod
      (canonicalLatitudeAnchor period hPeriod base) normal)
    (canonicalLatitudeNormalVector period hPeriod base normal)

/-- Exact fiberwise reconstruction.  One partition patch has weight at least
`1 / card`; dividing its local-frame coefficients by that weight expresses
the normal derivative through the implemented global finite frame. -/
theorem exists_canonicalLatitudeDerivative_frame_reconstruction
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    ∃ patch : FiniteTangentGeneratorPatch period hPeriod,
      1 / (Fintype.card
          (FiniteTangentGeneratorPatch period hPeriod) : Real) ≤
        finiteTangentGeneratorWeight period hPeriod patch
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal) ∧
      canonicalLatitudeDerivative period hPeriod field base normal =
        ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
          (canonicalLatitudeLocalNormalCoefficient period hPeriod patch
              basisIndex base normal /
            finiteTangentGeneratorWeight period hPeriod patch
              (quotientNormalLatitude period hPeriod
                (canonicalLatitudeAnchor period hPeriod base) normal)) *
            canonicalLatitudeFrameDerivative period hPeriod field base normal
              (finiteTangentGeneratorIndexEquivFin period hPeriod
                (patch, basisIndex)) := by
  let point := quotientNormalLatitude period hPeriod
    (canonicalLatitudeAnchor period hPeriod base) normal
  let vector := canonicalLatitudeNormalVector period hPeriod base normal
  obtain ⟨patch, hWeight⟩ :=
    exists_finiteTangentGeneratorWeight_ge_inv_card period hPeriod point
  refine ⟨patch, hWeight, ?_⟩
  have hCard : 0 < Fintype.card
      (FiniteTangentGeneratorPatch period hPeriod) :=
    Fintype.card_pos_iff.mpr ⟨patch⟩
  have hCardReal : 0 < (Fintype.card
      (FiniteTangentGeneratorPatch period hPeriod) : Real) := by
    exact_mod_cast hCard
  have hWeightPos : 0 <
      finiteTangentGeneratorWeight period hPeriod patch point :=
    (one_div_pos.mpr hCardReal).trans_le hWeight
  have hPointOpen :
      point ∈ finiteTangentGeneratorOpenPatch period hPeriod patch := by
    apply finiteTangentGeneratorClosedPatch_subset_openPatch period hPeriod patch
    exact subset_closure (ne_of_gt hWeightPos)
  have hVector := finiteTangentGeneratorLocalVector_reconstructs
    period hPeriod patch point hPointOpen vector
  have hGlobal : vector =
      ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
        (finiteTangentGeneratorLocalCoefficient period hPeriod patch basisIndex
            point vector /
          finiteTangentGeneratorWeight period hPeriod patch point) •
          (finiteSmoothTangentFrame period hPeriod).vectorAt point
            (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, basisIndex)) := by
    calc
      vector = ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
          finiteTangentGeneratorLocalCoefficient period hPeriod patch
              basisIndex point vector •
            finiteTangentGeneratorLocalVector period hPeriod patch
              basisIndex point := hVector
      _ = _ := by
        apply Finset.sum_congr rfl
        intro basisIndex _
        rw [finiteSmoothTangentFrame_vectorAt_generator]
        simp [smul_smul, hWeightPos.ne']
  have hApplied := congrArg
    (fun tangent => mvfderiv coverModelWithCorners field.toFun point tangent)
    hGlobal
  simpa [point, vector, canonicalLatitudeLocalNormalCoefficient,
    canonicalLatitudeFrameDerivative,
    canonicalLatitudeDerivative_eq_mvfderiv_normal,
    frameDerivative_eq_mfderiv] using hApplied

def canonicalLatitudeLocalNormalCoefficientL1
    (period : Real) (hPeriod : period ≠ 0)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
    |canonicalLatitudeLocalNormalCoefficient period hPeriod patch
      basisIndex base normal|

/-- Quantitative fiberwise consequence of the exact reconstruction.  The
partition denominator costs at most the finite patch cardinality. -/
theorem exists_canonicalLatitudeDerivative_abs_le_frame
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    ∃ patch : FiniteTangentGeneratorPatch period hPeriod,
      1 / (Fintype.card
          (FiniteTangentGeneratorPatch period hPeriod) : Real) ≤
        finiteTangentGeneratorWeight period hPeriod patch
          (quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod base) normal) ∧
      |canonicalLatitudeDerivative period hPeriod field base normal| ≤
        ((Fintype.card
            (FiniteTangentGeneratorPatch period hPeriod) : Real) *
          canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
            base normal) *
          ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ := by
  obtain ⟨patch, hWeight, hReconstruct⟩ :=
    exists_canonicalLatitudeDerivative_frame_reconstruction
      period hPeriod field base normal
  refine ⟨patch, hWeight, ?_⟩
  let point := quotientNormalLatitude period hPeriod
    (canonicalLatitudeAnchor period hPeriod base) normal
  let weight := finiteTangentGeneratorWeight period hPeriod patch point
  let coefficient := fun basisIndex : FiniteTangentGeneratorBasisIndex =>
    canonicalLatitudeLocalNormalCoefficient period hPeriod patch basisIndex
      base normal
  let derivative := canonicalLatitudeFrameDerivative period hPeriod field base normal
  let patchCount : Real := Fintype.card
    (FiniteTangentGeneratorPatch period hPeriod)
  have hCard : 0 < Fintype.card
      (FiniteTangentGeneratorPatch period hPeriod) :=
    Fintype.card_pos_iff.mpr ⟨patch⟩
  have hPatchCount : 0 < patchCount := by
    dsimp [patchCount]
    exact_mod_cast hCard
  have hWeightPos : 0 < weight := by
    exact (one_div_pos.mpr hPatchCount).trans_le hWeight
  have hCoefficientNonneg :
      0 ≤ ∑ basisIndex, |coefficient basisIndex| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hDenominator :
      (∑ basisIndex, |coefficient basisIndex|) / weight ≤
        patchCount * ∑ basisIndex, |coefficient basisIndex| := by
    rw [div_le_iff₀ hWeightPos]
    have hOne : 1 ≤ patchCount * weight := by
      calc
        1 = patchCount * (1 / patchCount) := by
          field_simp [hPatchCount.ne']
        _ ≤ patchCount * weight :=
          mul_le_mul_of_nonneg_left hWeight hPatchCount.le
    calc
      ∑ basisIndex, |coefficient basisIndex| =
          (∑ basisIndex, |coefficient basisIndex|) * 1 := by ring
      _ ≤ (∑ basisIndex, |coefficient basisIndex|) *
          (patchCount * weight) :=
        mul_le_mul_of_nonneg_left hOne hCoefficientNonneg
      _ = (patchCount * ∑ basisIndex, |coefficient basisIndex|) *
          weight := by ring
  rw [hReconstruct]
  calc
    |∑ basisIndex : FiniteTangentGeneratorBasisIndex,
        (coefficient basisIndex / weight) *
          derivative (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, basisIndex))| ≤
        ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
          |(coefficient basisIndex / weight) *
            derivative (finiteTangentGeneratorIndexEquivFin period hPeriod
              (patch, basisIndex))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
        (|coefficient basisIndex| / weight) * ‖derivative‖ := by
      apply Finset.sum_le_sum
      intro basisIndex _
      rw [abs_mul, abs_div, abs_of_pos hWeightPos]
      exact mul_le_mul_of_nonneg_left
        (norm_le_pi_norm derivative
          (finiteTangentGeneratorIndexEquivFin period hPeriod
            (patch, basisIndex)))
        (div_nonneg (abs_nonneg _) hWeightPos.le)
    _ = ((∑ basisIndex : FiniteTangentGeneratorBasisIndex,
        |coefficient basisIndex|) / weight) * ‖derivative‖ := by
      rw [← Finset.sum_mul, Finset.sum_div]
    _ ≤ (patchCount *
        ∑ basisIndex : FiniteTangentGeneratorBasisIndex,
          |coefficient basisIndex|) * ‖derivative‖ :=
      mul_le_mul_of_nonneg_right hDenominator (norm_nonneg derivative)
    _ = ((Fintype.card
          (FiniteTangentGeneratorPatch period hPeriod) : Real) *
        canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
          base normal) *
        ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ := by
      rfl

abbrev CanonicalLatitudeParameter := CanonicalLatitudeBase × Real

def canonicalLatitudeFundamentalCompact (period : Real) :
    Set CanonicalLatitudeParameter :=
  ((Set.univ : Set (Metric.sphere (0 : EuclideanR3) 1)) ×ˢ
      Set.Icc (min 0 period) (max 0 period)) ×ˢ
    Set.Icc (0 : Real) 1

theorem canonicalLatitudeFundamentalCompact_isCompact (period : Real) :
    IsCompact (canonicalLatitudeFundamentalCompact period) := by
  exact (isCompact_univ.prod isCompact_Icc).prod isCompact_Icc

def canonicalLatitudeNormalLift
    (period : Real) (hPeriod : period ≠ 0)
    (parameter : CanonicalLatitudeParameter) :
    TangentBundle coverModelWithCorners
      (EffectiveQuotient period hPeriod) :=
  ⟨quotientNormalLatitude period hPeriod
      (canonicalLatitudeAnchor period hPeriod parameter.1) parameter.2,
    canonicalLatitudeNormalVector period hPeriod parameter.1 parameter.2⟩

/-- The one missing joint-regularity statement required by the compact
coefficient argument.  It is strictly a tangent-lift statement and contains
no measure or coarea input. -/
def CanonicalLatitudeNormalLiftContinuous
    (period : Real) (hPeriod : period ≠ 0) : Prop :=
  Continuous (canonicalLatitudeNormalLift period hPeriod)

def canonicalLatitudeHighWeightSet
    (period : Real) (hPeriod : period ≠ 0)
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Set CanonicalLatitudeParameter :=
  canonicalLatitudeFundamentalCompact period ∩
    {parameter |
      1 / (Fintype.card
          (FiniteTangentGeneratorPatch period hPeriod) : Real) ≤
        finiteTangentGeneratorWeight period hPeriod patch
          (canonicalLatitudeNormalLift period hPeriod parameter).1}

theorem canonicalLatitudeHighWeightSet_isCompact
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsCompact (canonicalLatitudeHighWeightSet period hPeriod patch) := by
  have hPoint : Continuous
      (fun parameter =>
        (canonicalLatitudeNormalLift period hPeriod parameter).1) :=
    (FiberBundle.continuous_proj CoverCoordinates
      (TangentSpace coverModelWithCorners)).comp regularity
  have hWeight : Continuous
      (fun parameter =>
        finiteTangentGeneratorWeight period hPeriod patch
          (canonicalLatitudeNormalLift period hPeriod parameter).1) :=
    (finiteTangentGeneratorWeight_continuous period hPeriod patch).comp hPoint
  exact (canonicalLatitudeFundamentalCompact_isCompact period).inter_right
    (isClosed_le continuous_const hWeight)

theorem canonicalLatitudeLocalNormalCoefficient_continuousOn_highWeight
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod)
    (patch : FiniteTangentGeneratorPatch period hPeriod)
    (basisIndex : FiniteTangentGeneratorBasisIndex) :
    ContinuousOn
      (fun parameter : CanonicalLatitudeParameter =>
        canonicalLatitudeLocalNormalCoefficient period hPeriod patch
          basisIndex parameter.1 parameter.2)
      (canonicalLatitudeHighWeightSet period hPeriod patch) := by
  apply finiteTangentGeneratorLocalCoefficient_comp_continuousOn
    period hPeriod patch basisIndex
      (canonicalLatitudeNormalLift period hPeriod)
      (canonicalLatitudeHighWeightSet period hPeriod patch)
      regularity.continuousOn
  intro parameter hParameter
  have hWeight := hParameter.2
  have hCard : 0 < Fintype.card
      (FiniteTangentGeneratorPatch period hPeriod) :=
    Fintype.card_pos_iff.mpr ⟨patch⟩
  have hCardReal : 0 < (Fintype.card
      (FiniteTangentGeneratorPatch period hPeriod) : Real) := by
    exact_mod_cast hCard
  have hWeightPos : 0 < finiteTangentGeneratorWeight period hPeriod patch
      (canonicalLatitudeNormalLift period hPeriod parameter).1 :=
    (one_div_pos.mpr hCardReal).trans_le hWeight
  apply finiteTangentGeneratorClosedPatch_subset_openPatch period hPeriod patch
  exact subset_closure (ne_of_gt hWeightPos)

theorem exists_uniform_canonicalLatitudeLocalNormalCoefficientL1
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod) :
    ∃ bound : Real, 0 ≤ bound ∧
      ∀ (patch : FiniteTangentGeneratorPatch period hPeriod)
        (parameter : CanonicalLatitudeParameter),
        parameter ∈ canonicalLatitudeHighWeightSet period hPeriod patch →
        canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
          parameter.1 parameter.2 ≤ bound := by
  have hPatchBound : ∀ patch : FiniteTangentGeneratorPatch period hPeriod,
      ∃ bound : Real, 0 ≤ bound ∧
        ∀ parameter ∈ canonicalLatitudeHighWeightSet period hPeriod patch,
          canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
            parameter.1 parameter.2 ≤ bound := by
    intro patch
    have hContinuous : ContinuousOn
        (fun parameter : CanonicalLatitudeParameter =>
          canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
            parameter.1 parameter.2)
        (canonicalLatitudeHighWeightSet period hPeriod patch) := by
      unfold canonicalLatitudeLocalNormalCoefficientL1
      apply continuousOn_finsetSum Finset.univ
      intro basisIndex _
      exact (canonicalLatitudeLocalNormalCoefficient_continuousOn_highWeight
        period hPeriod regularity patch basisIndex).abs
    obtain ⟨rawBound, hRawBound⟩ :=
      (canonicalLatitudeHighWeightSet_isCompact
        period hPeriod regularity patch).exists_bound_of_continuousOn hContinuous
    refine ⟨max rawBound 0, le_max_right _ _, ?_⟩
    intro parameter hParameter
    have hNonnegative : 0 ≤
        canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
          parameter.1 parameter.2 := by
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc
      canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
          parameter.1 parameter.2 =
          ‖canonicalLatitudeLocalNormalCoefficientL1 period hPeriod patch
            parameter.1 parameter.2‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hNonnegative]
      _ ≤ rawBound := hRawBound parameter hParameter
      _ ≤ max rawBound 0 := le_max_left _ _
  choose patchBound hPatchBoundNonnegative hPatchBoundControls using hPatchBound
  refine ⟨∑ patch, patchBound patch,
    Finset.sum_nonneg fun patch _ => hPatchBoundNonnegative patch, ?_⟩
  intro patch parameter hParameter
  exact (hPatchBoundControls patch parameter hParameter).trans
    (Finset.single_le_sum
      (fun other _ => hPatchBoundNonnegative other)
      (Finset.mem_univ patch))

theorem exists_uniform_canonicalLatitudeDerivative_frame_bound
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod) :
    ∃ bound : Real, 0 ≤ bound ∧
      ∀ (field : SmoothQuotientField period hPeriod Real)
        (parameter : CanonicalLatitudeParameter),
        parameter ∈ canonicalLatitudeFundamentalCompact period →
        |canonicalLatitudeDerivative period hPeriod field
            parameter.1 parameter.2| ≤
          bound * ‖canonicalLatitudeFrameDerivative period hPeriod field
            parameter.1 parameter.2‖ := by
  obtain ⟨coefficientBound, hCoefficientBoundNonnegative,
      hCoefficientBound⟩ :=
    exists_uniform_canonicalLatitudeLocalNormalCoefficientL1
      period hPeriod regularity
  let patchCount : Real := Fintype.card
    (FiniteTangentGeneratorPatch period hPeriod)
  have hPatchCountNonnegative : 0 ≤ patchCount := by positivity
  refine ⟨patchCount * coefficientBound,
    mul_nonneg hPatchCountNonnegative hCoefficientBoundNonnegative, ?_⟩
  intro field parameter hParameter
  obtain ⟨patch, hWeight, hPointwise⟩ :=
    exists_canonicalLatitudeDerivative_abs_le_frame
      period hPeriod field parameter.1 parameter.2
  have hParameterHigh :
      parameter ∈ canonicalLatitudeHighWeightSet period hPeriod patch :=
    ⟨hParameter, hWeight⟩
  exact hPointwise.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (hCoefficientBound patch parameter hParameterHigh)
        hPatchCountNonnegative)
      (norm_nonneg _))

theorem canonicalLatitudeCollarPoint_continuous_of_normalLift
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod) :
    Continuous
      (fun parameter : CanonicalLatitudeParameter =>
        quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod parameter.1) parameter.2) :=
  (FiberBundle.continuous_proj CoverCoordinates
    (TangentSpace coverModelWithCorners)).comp regularity

theorem canonicalLatitudeValue_uncurry_continuous_of_normalLift
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous
      (fun parameter : CanonicalLatitudeParameter =>
        canonicalLatitudeValue period hPeriod field
          parameter.1 parameter.2) := by
  exact field.contMDiff_toFun.continuous.comp
    (canonicalLatitudeCollarPoint_continuous_of_normalLift
      period hPeriod regularity)

theorem canonicalLatitudeFrameDerivative_uncurry_continuous_of_normalLift
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous
      (fun parameter : CanonicalLatitudeParameter =>
        canonicalLatitudeFrameDerivative period hPeriod field
          parameter.1 parameter.2) := by
  exact (frameDerivative_contMDiff period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod) field).continuous.comp
    (canonicalLatitudeCollarPoint_continuous_of_normalLift
      period hPeriod regularity)

theorem canonicalLatitudeDerivative_uncurry_continuous_of_normalLift
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous
      (fun parameter : CanonicalLatitudeParameter =>
        canonicalLatitudeDerivative period hPeriod field
          parameter.1 parameter.2) := by
  have hTangentMap : Continuous
      (fun parameter : CanonicalLatitudeParameter =>
        tangentMap coverModelWithCorners 𝓘(Real, Real) field.toFun
          (canonicalLatitudeNormalLift period hPeriod parameter)) :=
    ((field.contMDiff_toFun.contMDiff_tangentMap (m := 0)
      (by simp)).continuous).comp regularity
  have hMvfderiv : Continuous
      (fun parameter : CanonicalLatitudeParameter =>
        mvfderiv coverModelWithCorners field.toFun
          (canonicalLatitudeNormalLift period hPeriod parameter).1
          (canonicalLatitudeNormalLift period hPeriod parameter).2) := by
    convert (contMDiff_snd_tangentBundle_modelSpace Real
      𝓘(Real, Real) (n := 0)).continuous.comp hTangentMap using 1
    rfl
  apply hMvfderiv.congr
  intro parameter
  exact (canonicalLatitudeDerivative_eq_mvfderiv_normal
    period hPeriod field parameter.1 parameter.2).symm

theorem unitNormalH1Energy_canonicalLatitude_continuous_of_normalLift
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous
      (fun base : CanonicalLatitudeBase => unitNormalH1Energy
        (canonicalLatitudeValue period hPeriod field base)
        (canonicalLatitudeDerivative period hPeriod field base)) := by
  unfold unitNormalH1Energy
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((canonicalLatitudeValue_uncurry_continuous_of_normalLift
      period hPeriod regularity field).pow 2).const_mul 2 |>.add
    ((canonicalLatitudeDerivative_uncurry_continuous_of_normalLift
      period hPeriod regularity field).pow 2)

theorem unitLatitudeFrameH1Energy_continuous_of_normalLift
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous (unitLatitudeFrameH1Energy period hPeriod field) := by
  unfold unitLatitudeFrameH1Energy
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((canonicalLatitudeValue_uncurry_continuous_of_normalLift
      period hPeriod regularity field).pow 2).const_mul 2 |>.add
    ((canonicalLatitudeFrameDerivative_uncurry_continuous_of_normalLift
      period hPeriod regularity field).norm.pow 2)

theorem continuous_integrable_canonicalLatitudeBaseMeasure
    (period : Real) (function : CanonicalLatitudeBase → Real)
    (hFunction : Continuous function) :
    Integrable function (canonicalLatitudeBaseMeasure period) := by
  let sphereMeasure : Measure (Metric.sphere (0 : EuclideanR3) 1) :=
    (volume : Measure EuclideanR3).toSphere
  let productMeasure : Measure CanonicalLatitudeBase :=
    sphereMeasure.prod volume
  let support : Set CanonicalLatitudeBase :=
    Set.univ ×ˢ canonicalLatitudeTimeInterval period
  let compactSupport : Set CanonicalLatitudeBase :=
    Set.univ ×ˢ Set.Icc (min 0 period) (max 0 period)
  have hCompact : IsCompact compactSupport :=
    isCompact_univ.prod isCompact_Icc
  have hSupportMeasurable : MeasurableSet support :=
    MeasurableSet.univ.prod measurableSet_Ioc
  have hSupportSubset : support ⊆ compactSupport := by
    exact Set.prod_mono_right Set.Ioc_subset_Icc_self
  have hMeasure : productMeasure support ≠ (⊤ : ENNReal) := by
    dsimp [productMeasure, support, sphereMeasure,
      canonicalLatitudeTimeInterval]
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _)
      measure_Ioc_lt_top.ne
  have hIntegrableOn : IntegrableOn function support productMeasure :=
    hFunction.continuousOn.integrableOn_of_subset_isCompact
      hCompact hSupportMeasurable hSupportSubset hMeasure
  rw [IntegrableOn, ← Measure.prod_restrict] at hIntegrableOn
  simpa [canonicalLatitudeBaseMeasure, productMeasure, sphereMeasure,
    support] using hIntegrableOn

/-- The frame collar energy is integrable without any normal-lift hypothesis.
Only its comparison with the ambient sphere measure is a coarea question. -/
theorem unitLatitudeFrameH1Energy_integrable
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    Integrable (unitLatitudeFrameH1Energy period hPeriod field)
      (canonicalLatitudeBaseMeasure period) :=
  continuous_integrable_canonicalLatitudeBaseMeasure period _
    (unitLatitudeFrameH1Energy_continuous period hPeriod field)

theorem exists_uniform_unitNormalH1Energy_le_unitLatitudeFrameH1Energy
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod) :
    ∃ bound : Real, 1 ≤ bound ∧
      ∀ (field : SmoothQuotientField period hPeriod Real)
        (base : CanonicalLatitudeBase),
        base.2 ∈ Set.Icc (min 0 period) (max 0 period) →
        unitNormalH1Energy
            (canonicalLatitudeValue period hPeriod field base)
            (canonicalLatitudeDerivative period hPeriod field base) ≤
          bound ^ 2 *
            unitLatitudeFrameH1Energy period hPeriod field base := by
  obtain ⟨derivativeBound, hDerivativeBoundNonnegative,
      hDerivativeBound⟩ :=
    exists_uniform_canonicalLatitudeDerivative_frame_bound
      period hPeriod regularity
  let bound := max 1 derivativeBound
  have hBoundOne : 1 ≤ bound := le_max_left _ _
  have hBoundNonnegative : 0 ≤ bound := le_trans (by norm_num) hBoundOne
  refine ⟨bound, hBoundOne, ?_⟩
  intro field base hBase
  have hValueContinuous : Continuous
      (canonicalLatitudeValue period hPeriod field base) := by
    exact (canonicalNormalSlice_contDiff period hPeriod field
      (canonicalLatitudeAnchor period hPeriod base)).continuous
  have hNormalDerivativeContinuous : Continuous
      (canonicalLatitudeDerivative period hPeriod field base) :=
    canonicalNormalSlice_deriv_continuous period hPeriod field
      (canonicalLatitudeAnchor period hPeriod base)
  have hFrameDerivativeContinuous : Continuous
      (canonicalLatitudeFrameDerivative period hPeriod field base) := by
    exact (frameDerivative_contMDiff period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field).continuous.comp
      (quotientNormalLatitude_contMDiff period hPeriod
        (canonicalLatitudeAnchor period hPeriod base)).continuous
  have hPointwise : ∀ normal ∈ Set.Icc (0 : Real) 1,
      2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
          canonicalLatitudeDerivative period hPeriod field base normal ^ 2 ≤
        bound ^ 2 *
          (2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
            ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ ^ 2) := by
    intro normal hNormal
    have hParameter : (base, normal) ∈
        canonicalLatitudeFundamentalCompact period :=
      ⟨⟨Set.mem_univ _, hBase⟩, hNormal⟩
    have hDerivativeRaw := hDerivativeBound field (base, normal) hParameter
    have hDerivative :
        |canonicalLatitudeDerivative period hPeriod field base normal| ≤
          bound *
            ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ :=
      hDerivativeRaw.trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 derivativeBound)
          (norm_nonneg _))
    have hDerivativeSquare :
        canonicalLatitudeDerivative period hPeriod field base normal ^ 2 ≤
          bound ^ 2 *
            ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ ^ 2 := by
      have hSquare := (sq_le_sq₀
        (abs_nonneg (canonicalLatitudeDerivative period hPeriod field base normal))
        (mul_nonneg hBoundNonnegative (norm_nonneg _))).mpr hDerivative
      simpa [mul_pow, sq_abs] using hSquare
    have hBoundSquare : 1 ≤ bound ^ 2 := by
      nlinarith [sq_nonneg bound]
    have hValueSquare :
        2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 ≤
          bound ^ 2 *
            (2 * canonicalLatitudeValue period hPeriod field base normal ^ 2) :=
      calc
        2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 =
            1 * (2 * canonicalLatitudeValue period hPeriod field base normal ^ 2) :=
          by ring
        _ ≤ bound ^ 2 *
            (2 * canonicalLatitudeValue period hPeriod field base normal ^ 2) :=
          mul_le_mul_of_nonneg_right hBoundSquare
            (mul_nonneg (by norm_num) (sq_nonneg _))
    calc
      2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
            canonicalLatitudeDerivative period hPeriod field base normal ^ 2 ≤
          bound ^ 2 *
              (2 * canonicalLatitudeValue period hPeriod field base normal ^ 2) +
            bound ^ 2 *
              ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ ^ 2 :=
        add_le_add hValueSquare hDerivativeSquare
      _ = _ := by ring
  unfold unitNormalH1Energy unitLatitudeFrameH1Energy
  calc
    (∫ normal in (0 : Real)..1,
        2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
          canonicalLatitudeDerivative period hPeriod field base normal ^ 2) ≤
      ∫ normal in (0 : Real)..1, bound ^ 2 *
        (2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
          ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ ^ 2) := by
        exact intervalIntegral.integral_mono_on (by norm_num)
          (((hValueContinuous.pow 2).const_mul 2).add
            (hNormalDerivativeContinuous.pow 2) |>.intervalIntegrable 0 1)
          (((((hValueContinuous.pow 2).const_mul 2).add
              (hFrameDerivativeContinuous.norm.pow 2)).const_mul
                (bound ^ 2)).intervalIntegrable 0 1)
          hPointwise
    _ = bound ^ 2 *
        ∫ normal in (0 : Real)..1,
          2 * canonicalLatitudeValue period hPeriod field base normal ^ 2 +
            ‖canonicalLatitudeFrameDerivative period hPeriod field base normal‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

theorem canonicalLatitudeTime_mem_Icc_ae (period : Real) :
    ∀ᵐ base ∂(canonicalLatitudeBaseMeasure period),
      base.2 ∈ Set.Icc (min 0 period) (max 0 period) := by
  unfold canonicalLatitudeBaseMeasure
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_Icc.preimage measurable_snd)).2
  refine Filter.Eventually.of_forall fun _sphere => ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  exact Set.Ioc_subset_Icc_self hTime

theorem canonicalLatitudeValue_hasDerivAt
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    HasDerivAt (canonicalLatitudeValue period hPeriod field base)
      (canonicalLatitudeDerivative period hPeriod field base normal) normal :=
  canonicalNormalSlice_hasDerivAt period hPeriod field
    (canonicalLatitudeAnchor period hPeriod base) normal

theorem canonicalLatitudeDerivative_continuous
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    Continuous (canonicalLatitudeDerivative period hPeriod field base) :=
  canonicalNormalSlice_deriv_continuous period hPeriod field
    (canonicalLatitudeAnchor period hPeriod base)

@[simp]
theorem canonicalLatitudeValue_zero
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeValue period hPeriod field base 0 =
      field (fixedThroatQuotientInclusion period hPeriod
        (canonicalLatitudeThroatMap period hPeriod base)) := by
  simp [canonicalLatitudeValue, canonicalLatitudeThroatMap]

theorem canonicalLatitudeTraceSquare_integrable
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    Integrable
      (fun base : CanonicalLatitudeBase =>
        canonicalLatitudeValue period hPeriod field base 0 ^ 2)
      (canonicalLatitudeBaseMeasure period) := by
  let throatSquare : EffectiveThroat period hPeriod → Real := fun point =>
    field (fixedThroatQuotientInclusion period hPeriod point) ^ 2
  have hThroatSquareContinuous : Continuous throatSquare := by
    dsimp [throatSquare]
    exact (field.contMDiff_toFun.continuous.comp
      (fixedThroatQuotientInclusion_contMDiff
        period hPeriod).continuous).pow 2
  have hThroatSquareIntegrable : Integrable throatSquare
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    hThroatSquareContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace throatSquare)
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    at hThroatSquareIntegrable
  have hComposed := hThroatSquareIntegrable.comp_measurable
    (canonicalLatitudeThroatMap_continuous period hPeriod).measurable
  simpa [throatSquare, Function.comp_def] using hComposed

/-- Exact `L²`-norm identification on the canonical product fundamental
domain.  This closes the measure-map part of the Fubini bridge. -/
theorem smoothCanonicalPhysicalTrace_norm_sq_eq_latitudeIntegral
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 =
      ∫ base : CanonicalLatitudeBase,
        canonicalLatitudeValue period hPeriod field base 0 ^ 2
        ∂(canonicalLatitudeBaseMeasure period) := by
  let nu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let trace := smoothCanonicalPhysicalTraceL2 period hPeriod field
  have hTraceAe :
      (trace : EffectiveThroat period hPeriod → Real) =ᵐ[nu]
        (throatTrace period hPeriod Real field).toFun := by
    change
      (smoothTraceToL2 period hPeriod Real nu field :
          EffectiveThroat period hPeriod → Real) =ᵐ[nu]
        (throatTrace period hPeriod Real field).toFun
    simpa [smoothTraceToL2] using
      (smoothThroatField_memLp period hPeriod Real nu
        (throatTrace period hPeriod Real field)).coeFn_toLp
  have hThroatSquareContinuous : Continuous
      (fun point : EffectiveThroat period hPeriod =>
        field (fixedThroatQuotientInclusion period hPeriod point) ^ 2) := by
    exact (field.contMDiff_toFun.continuous.comp
      (fixedThroatQuotientInclusion_contMDiff
        period hPeriod).continuous).pow 2
  calc
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 =
        inner Real trace trace := by
      exact (real_inner_self_eq_norm_sq trace).symm
    _ = ∫ point, inner Real (trace point) (trace point) ∂nu :=
      L2.inner_def trace trace
    _ = ∫ point, field
          (fixedThroatQuotientInclusion period hPeriod point) ^ 2 ∂nu := by
      apply integral_congr_ae
      filter_upwards [hTraceAe] with point hPoint
      rw [hPoint]
      simp [throatTrace, pow_two]
    _ = ∫ base : CanonicalLatitudeBase,
          field (fixedThroatQuotientInclusion period hPeriod
            (canonicalLatitudeThroatMap period hPeriod base)) ^ 2
          ∂(canonicalLatitudeBaseMeasure period) := by
      dsimp [nu]
      rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
      exact integral_map
        (canonicalLatitudeThroatMap_continuous
          period hPeriod).measurable.aemeasurable
        hThroatSquareContinuous.aestronglyMeasurable
    _ = ∫ base : CanonicalLatitudeBase,
          canonicalLatitudeValue period hPeriod field base 0 ^ 2
          ∂(canonicalLatitudeBaseMeasure period) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun base => by
        change field (fixedThroatQuotientInclusion period hPeriod
            (canonicalLatitudeThroatMap period hPeriod base)) ^ 2 =
          canonicalLatitudeValue period hPeriod field base 0 ^ 2
        rw [canonicalLatitudeValue_zero]

/-! ## The remaining `Measure.toSphere` coarea bridge -/

/-- The sharp uniform density bound on the unit positive collar: its latitude
Jacobian on `S³` is `cos normal ^ 2`, hence the reciprocal-square bound at
`normal = 1`. -/
def canonicalLatitudeCoareaMeasureConstant : NNReal :=
  ⟨(Real.cos 1)⁻¹ ^ 2, sq_nonneg _⟩

/-- The single external measure statement still absent from Mathlib.  It is
exactly the latitude disintegration of `Measure.toSphere` (tensored with one
fundamental time interval and pushed to the quotient); all measurability,
Fubini and graph-norm consequences are proved below. -/
def CanonicalLatitudeMeasureToSphereCoareaDomination
    (period : Real) (hPeriod : period ≠ 0) : Prop :=
  Measure.map (canonicalLatitudeCollarMap period hPeriod)
      (canonicalLatitudeCollarMeasure period) ≤
    canonicalLatitudeCoareaMeasureConstant •
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod

/-- The isolated measure domination implies the generic nonnegative collar
integral estimate. -/
theorem canonicalLatitudeCollar_integral_le_of_measureToSphereCoarea
    (period : Real) (hPeriod : period ≠ 0)
    (coarea : CanonicalLatitudeMeasureToSphereCoareaDomination
      period hPeriod)
    (function : EffectiveQuotient period hPeriod → Real)
    (hFunction : Continuous function)
    (hNonnegative : ∀ point, 0 ≤ function point) :
    (∫ base : CanonicalLatitudeBase,
        (∫ normal in (0 : Real)..1,
          function (canonicalLatitudeCollarMap period hPeriod
            (base, normal)))
      ∂(canonicalLatitudeBaseMeasure period)) ≤
      (canonicalLatitudeCoareaMeasureConstant : Real) *
        ∫ point, function point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
    canonicalLatitudeBaseMeasure_isFinite period
  let ambientMeasure :=
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  have hFunctionIntegrable : Integrable function ambientMeasure :=
    hFunction.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace function)
  have hScaledIntegrable : Integrable function
      (canonicalLatitudeCoareaMeasureConstant • ambientMeasure) :=
    hFunctionIntegrable.smul_measure_nnreal
  have hMappedIntegrable : Integrable function
      (Measure.map (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeCollarMeasure period)) :=
    hScaledIntegrable.mono_measure coarea
  have hPullbackIntegrable : Integrable
      (fun parameter : CanonicalLatitudeCollarParameter =>
        function (canonicalLatitudeCollarMap period hPeriod parameter))
      (canonicalLatitudeCollarMeasure period) := by
    simpa [Function.comp_def] using
      hMappedIntegrable.comp_measurable
        (canonicalLatitudeCollarMap_continuous period hPeriod).measurable
  have hInterval :
      (∫ base : CanonicalLatitudeBase,
          (∫ normal in (0 : Real)..1,
            function (canonicalLatitudeCollarMap period hPeriod
              (base, normal)))
        ∂(canonicalLatitudeBaseMeasure period)) =
        ∫ base : CanonicalLatitudeBase,
          ∫ normal,
            function (canonicalLatitudeCollarMap period hPeriod
              (base, normal)) ∂canonicalLatitudeUnitNormalMeasure
          ∂(canonicalLatitudeBaseMeasure period) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun base => by
      change (∫ normal in (0 : Real)..1,
          function (canonicalLatitudeCollarMap period hPeriod
            (base, normal))) =
        ∫ normal,
          function (canonicalLatitudeCollarMap period hPeriod
            (base, normal)) ∂canonicalLatitudeUnitNormalMeasure
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : Real) ≤ 1)]
      rfl
  calc
    (∫ base : CanonicalLatitudeBase,
        (∫ normal in (0 : Real)..1,
          function (canonicalLatitudeCollarMap period hPeriod
            (base, normal)))
      ∂(canonicalLatitudeBaseMeasure period)) =
        ∫ parameter : CanonicalLatitudeCollarParameter,
          function (canonicalLatitudeCollarMap period hPeriod parameter)
          ∂(canonicalLatitudeCollarMeasure period) := by
      rw [hInterval]
      exact integral_integral hPullbackIntegrable
    _ = ∫ point, function point
          ∂(Measure.map (canonicalLatitudeCollarMap period hPeriod)
            (canonicalLatitudeCollarMeasure period)) := by
      symm
      exact integral_map
        (canonicalLatitudeCollarMap_continuous
          period hPeriod).measurable.aemeasurable
        hFunction.aestronglyMeasurable
    _ ≤ ∫ point, function point
          ∂(canonicalLatitudeCoareaMeasureConstant • ambientMeasure) :=
      integral_mono_measure coarea
        (Filter.Eventually.of_forall hNonnegative) hScaledIntegrable
    _ = (canonicalLatitudeCoareaMeasureConstant : Real) *
          ∫ point, function point ∂ambientMeasure := by
      rw [integral_smul_nnreal_measure]
      rfl

/-- The graph norm of a smooth field is exactly the `L²` norm of its
implemented first jet. -/
theorem smoothToCanonicalPhysicalScalarH1_norm_sq_eq_integral_smoothFirstJet
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 =
      ∫ point : EffectiveQuotient period hPeriod,
        ‖smoothFirstJet period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  let jet := smoothFirstJet period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod) field
  let jetL2 := smoothFirstJetToL2 period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field
  have hMemLp : MemLp jet (2 : ENNReal)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
    simpa [jet] using smoothFirstJet_memLp period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field
  let energy := ∫ point,
    ‖jet point‖ ^ 2
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hEnergyNonnegative : 0 ≤ energy := by
    unfold energy
    exact integral_nonneg fun _ => sq_nonneg _
  have hELp := hMemLp.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ENNReal) ≠ 0)
    (by simp : (2 : ENNReal) ≠ (∞ : ENNReal))
  have hJetL2Norm : ‖jetL2‖ = Real.sqrt energy := by
    calc
      ‖jetL2‖ = (eLpNorm jet (2 : ENNReal)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)).toReal := by
        simp [jetL2, jet, smoothFirstJetToL2, Lp.norm_toLp]
      _ = (ENNReal.ofReal
          ((∫ point : EffectiveQuotient period hPeriod,
              ‖jet point‖ ^ (2 : ENNReal).toReal
              ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) ^
            (2 : ENNReal).toReal⁻¹)).toReal := congrArg ENNReal.toReal hELp
      _ = Real.sqrt energy := by
        simp only [ENNReal.toReal_ofNat]
        rw [ENNReal.toReal_ofReal']
        rw [max_eq_left (by positivity)]
        simp [energy, Real.sqrt_eq_rpow, one_div]
  calc
    ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 =
        ‖jetL2‖ ^ 2 := by rfl
    _ = energy := by rw [hJetL2Norm, Real.sq_sqrt hEnergyNonnegative]
    _ = ∫ point : EffectiveQuotient period hPeriod,
          ‖smoothFirstJet period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
      rfl

theorem canonicalPhysicalFrameH1Density_le_three_firstJet
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalFrameH1Density period hPeriod field point ≤
      3 * ‖smoothFirstJet period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2 := by
  let jet := smoothFirstJet period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod) field point
  have hValue : ‖field point‖ ≤ ‖jet‖ := by
    simpa [jet, smoothFirstJet] using norm_fst_le jet
  have hDerivative :
      ‖frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ ≤ ‖jet‖ := by
    simpa [jet, smoothFirstJet] using norm_snd_le jet
  have hValueSq : field point ^ 2 ≤ ‖jet‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (field point)) (norm_nonneg jet)).2 hValue
  have hDerivativeSq :
      ‖frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2 ≤
        ‖jet‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg jet)).2 hDerivative
  change 2 * field point ^ 2 +
      ‖frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2 ≤
    3 * ‖jet‖ ^ 2
  linarith

theorem integral_canonicalPhysicalFrameH1Density_le_graphNorm
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real) :
    (∫ point : EffectiveQuotient period hPeriod,
        canonicalPhysicalFrameH1Density period hPeriod field point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) ≤
      3 * ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
  have hDensityIntegrable : Integrable
      (canonicalPhysicalFrameH1Density period hPeriod field)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    (canonicalPhysicalFrameH1Density_continuous period hPeriod field)
      |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hJetContinuous : Continuous
      (fun point : EffectiveQuotient period hPeriod =>
        3 * ‖smoothFirstJet period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2) :=
    ((smoothFirstJet_contMDiff period hPeriod Real
      (finiteSmoothTangentFrame period hPeriod) field).continuous.norm.pow 2)
        |>.const_mul 3
  have hJetIntegrable : Integrable
      (fun point : EffectiveQuotient period hPeriod =>
        3 * ‖smoothFirstJet period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    hJetContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ point : EffectiveQuotient period hPeriod,
        canonicalPhysicalFrameH1Density period hPeriod field point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) ≤
        ∫ point : EffectiveQuotient period hPeriod,
          3 * ‖smoothFirstJet period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
      integral_mono hDensityIntegrable hJetIntegrable fun point =>
        canonicalPhysicalFrameH1Density_le_three_firstJet
          period hPeriod field point
    _ = 3 * ∫ point : EffectiveQuotient period hPeriod,
          ‖smoothFirstJet period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field point‖ ^ 2
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
      rw [integral_const_mul]
    _ = 3 * ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
      rw [smoothToCanonicalPhysicalScalarH1_norm_sq_eq_integral_smoothFirstJet]

/-- Pure coarea/measure comparison.  It contains no normal reconstruction:
the integrand is exactly the already installed finite-frame first jet. -/
structure CanonicalLatitudeCoareaBound
    (period : Real) (hPeriod : period ≠ 0) where
  constant : Real
  nonnegative : 0 ≤ constant
  frameEnergyIntegrable : ∀ field, Integrable
    (unitLatitudeFrameH1Energy period hPeriod field)
    (canonicalLatitudeBaseMeasure period)
  frameCollarEnergy_le_graph : ∀ field,
    (∫ base : CanonicalLatitudeBase,
        unitLatitudeFrameH1Energy period hPeriod field base
      ∂(canonicalLatitudeBaseMeasure period)) ≤
      constant ^ 2 *
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2

/-- The single `Measure.toSphere` domination statement closes all of entry A,
including integrability, Fubini and comparison with the implemented graph
norm. -/
def canonicalLatitudeCoareaBoundOfMeasureToSphereDomination
    (period : Real) (hPeriod : period ≠ 0)
    (coarea : CanonicalLatitudeMeasureToSphereCoareaDomination
      period hPeriod) :
    CanonicalLatitudeCoareaBound period hPeriod where
  constant := Real.sqrt
    (3 * (canonicalLatitudeCoareaMeasureConstant : Real))
  nonnegative := Real.sqrt_nonneg _
  frameEnergyIntegrable field :=
    unitLatitudeFrameH1Energy_integrable period hPeriod field
  frameCollarEnergy_le_graph field := by
    have hCoarea :=
      canonicalLatitudeCollar_integral_le_of_measureToSphereCoarea
        period hPeriod coarea
        (canonicalPhysicalFrameH1Density period hPeriod field)
        (canonicalPhysicalFrameH1Density_continuous
          period hPeriod field)
        (canonicalPhysicalFrameH1Density_nonnegative
          period hPeriod field)
    have hDensity :=
      integral_canonicalPhysicalFrameH1Density_le_graphNorm
        period hPeriod field
    calc
      (∫ base : CanonicalLatitudeBase,
          unitLatitudeFrameH1Energy period hPeriod field base
        ∂(canonicalLatitudeBaseMeasure period)) ≤
          (canonicalLatitudeCoareaMeasureConstant : Real) *
            ∫ point : EffectiveQuotient period hPeriod,
              canonicalPhysicalFrameH1Density period hPeriod field point
            ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
        simpa [unitLatitudeFrameH1Energy] using hCoarea
      _ ≤ (canonicalLatitudeCoareaMeasureConstant : Real) *
          (3 * ‖smoothToCanonicalPhysicalScalarH1
            period hPeriod field‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hDensity
          canonicalLatitudeCoareaMeasureConstant.coe_nonneg
      _ = (Real.sqrt
            (3 * (canonicalLatitudeCoareaMeasureConstant : Real))) ^ 2 *
          ‖smoothToCanonicalPhysicalScalarH1
            period hPeriod field‖ ^ 2 := by
        rw [Real.sq_sqrt]
        · ring
        · positivity

/-- Quantitative reconstruction of the latitude-normal derivative from the
global finite tangent family.  This package is independent of coarea. -/
structure CanonicalNormalFrameReconstructionBound
    (period : Real) (hPeriod : period ≠ 0) where
  constant : Real
  nonnegative : 0 ≤ constant
  normalEnergyIntegrable : ∀ field, Integrable
    (fun base : CanonicalLatitudeBase => unitNormalH1Energy
      (canonicalLatitudeValue period hPeriod field base)
      (canonicalLatitudeDerivative period hPeriod field base))
    (canonicalLatitudeBaseMeasure period)
  normalCollarEnergy_le_frame : ∀ field,
    (∫ base : CanonicalLatitudeBase, unitNormalH1Energy
        (canonicalLatitudeValue period hPeriod field base)
        (canonicalLatitudeDerivative period hPeriod field base)
      ∂(canonicalLatitudeBaseMeasure period)) ≤
      constant ^ 2 *
        ∫ base : CanonicalLatitudeBase,
          unitLatitudeFrameH1Energy period hPeriod field base
        ∂(canonicalLatitudeBaseMeasure period)

/-- The compact finite-frame argument closes the full reconstruction package
once the joint tangent lift of the explicit latitude collar is continuous. -/
def canonicalNormalFrameReconstructionBoundOfNormalLiftContinuous
    (period : Real) (hPeriod : period ≠ 0)
    (regularity : CanonicalLatitudeNormalLiftContinuous period hPeriod) :
    CanonicalNormalFrameReconstructionBound period hPeriod := by
  let existence :=
    exists_uniform_unitNormalH1Energy_le_unitLatitudeFrameH1Energy
      period hPeriod regularity
  let bound := existence.choose
  have hBoundOne : 1 ≤ bound := existence.choose_spec.1
  have hEnergy := existence.choose_spec.2
  refine
    { constant := bound
      nonnegative := le_trans (by norm_num) hBoundOne
      normalEnergyIntegrable := ?_
      normalCollarEnergy_le_frame := ?_ }
  · intro field
    exact continuous_integrable_canonicalLatitudeBaseMeasure period _
      (unitNormalH1Energy_canonicalLatitude_continuous_of_normalLift
        period hPeriod regularity field)
  · intro field
    have hNormalIntegrable :=
      continuous_integrable_canonicalLatitudeBaseMeasure period _
        (unitNormalH1Energy_canonicalLatitude_continuous_of_normalLift
          period hPeriod regularity field)
    have hFrameIntegrable :=
      continuous_integrable_canonicalLatitudeBaseMeasure period _
        (unitLatitudeFrameH1Energy_continuous_of_normalLift
          period hPeriod regularity field)
    calc
      (∫ base : CanonicalLatitudeBase, unitNormalH1Energy
          (canonicalLatitudeValue period hPeriod field base)
          (canonicalLatitudeDerivative period hPeriod field base)
        ∂(canonicalLatitudeBaseMeasure period)) ≤
          ∫ base : CanonicalLatitudeBase, bound ^ 2 *
            unitLatitudeFrameH1Energy period hPeriod field base
          ∂(canonicalLatitudeBaseMeasure period) := by
        apply integral_mono_ae hNormalIntegrable
          (hFrameIntegrable.const_mul (bound ^ 2))
        filter_upwards [canonicalLatitudeTime_mem_Icc_ae period] with base hBase
        exact hEnergy field base hBase
      _ = bound ^ 2 *
          ∫ base : CanonicalLatitudeBase,
            unitLatitudeFrameH1Energy period hPeriod field base
          ∂(canonicalLatitudeBaseMeasure period) := by
        rw [integral_const_mul]

/-- Legacy aggregate comparison used by the completed trace construction. -/
structure CanonicalLatitudeCoareaFrameBound
    (period : Real) (hPeriod : period ≠ 0) where
  constant : Real
  nonnegative : 0 ≤ constant
  normalEnergyIntegrable : ∀ field, Integrable
    (fun base : CanonicalLatitudeBase => unitNormalH1Energy
      (canonicalLatitudeValue period hPeriod field base)
      (canonicalLatitudeDerivative period hPeriod field base))
    (canonicalLatitudeBaseMeasure period)
  collarEnergy_le_graph : ∀ field,
    (∫ base : CanonicalLatitudeBase, unitNormalH1Energy
        (canonicalLatitudeValue period hPeriod field base)
        (canonicalLatitudeDerivative period hPeriod field base)
      ∂(canonicalLatitudeBaseMeasure period)) ≤
      constant ^ 2 *
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2

/-- The separated reconstruction and coarea estimates recover the former
single comparison, with the product constant. -/
def CanonicalNormalFrameReconstructionBound.combineCoarea
    (period : Real) (hPeriod : period ≠ 0)
    (reconstruction : CanonicalNormalFrameReconstructionBound period hPeriod)
    (coarea : CanonicalLatitudeCoareaBound period hPeriod) :
    CanonicalLatitudeCoareaFrameBound period hPeriod where
  constant := reconstruction.constant * coarea.constant
  nonnegative := mul_nonneg reconstruction.nonnegative coarea.nonnegative
  normalEnergyIntegrable := reconstruction.normalEnergyIntegrable
  collarEnergy_le_graph field := by
    calc
      (∫ base : CanonicalLatitudeBase, unitNormalH1Energy
          (canonicalLatitudeValue period hPeriod field base)
          (canonicalLatitudeDerivative period hPeriod field base)
        ∂(canonicalLatitudeBaseMeasure period)) ≤
          reconstruction.constant ^ 2 *
            ∫ base : CanonicalLatitudeBase,
              unitLatitudeFrameH1Energy period hPeriod field base
            ∂(canonicalLatitudeBaseMeasure period) :=
        reconstruction.normalCollarEnergy_le_frame field
      _ ≤ reconstruction.constant ^ 2 *
          (coarea.constant ^ 2 *
            ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (coarea.frameCollarEnergy_le_graph field)
          (sq_nonneg reconstruction.constant)
      _ = (reconstruction.constant * coarea.constant) ^ 2 *
          ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
        ring

/-- Backwards-compatible name for the now-minimal comparison package. -/
abbrev CanonicalLatitudeFrameEnergyComparison :=
  CanonicalLatitudeCoareaFrameBound

/-- The abstract Fubini reduction and the proved one-dimensional FTC estimate
turn the isolated coarea/frame comparison into the squared smooth trace
bound. -/
theorem CanonicalLatitudeFrameEnergyComparison.squaredBound
    (period : Real) (hPeriod : period ≠ 0)
    (comparison : CanonicalLatitudeFrameEnergyComparison period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothCanonicalPhysicalTraceL2 period hPeriod field‖ ^ 2 ≤
      comparison.constant ^ 2 *
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 := by
  rw [smoothCanonicalPhysicalTrace_norm_sq_eq_latitudeIntegral]
  exact (fiberwise_unitNormal_point_trace_sq_le
      (canonicalLatitudeBaseMeasure period)
      (canonicalLatitudeValue period hPeriod field)
      (canonicalLatitudeDerivative period hPeriod field)
      (canonicalLatitudeValue_hasDerivAt period hPeriod field)
      (canonicalLatitudeDerivative_continuous period hPeriod field)
      (canonicalLatitudeTraceSquare_integrable period hPeriod field)
      (comparison.normalEnergyIntegrable field)).trans
    (comparison.collarEnergy_le_graph field)

/-- The exact geometric comparison closes the formerly conditional physical
trace bound. -/
def canonicalPhysicalH1TraceBoundOfLatitudeComparison
    (period : Real) (hPeriod : period ≠ 0)
    (comparison : CanonicalLatitudeFrameEnergyComparison period hPeriod) :
    CanonicalPhysicalH1TraceBound period hPeriod where
  constant := comparison.constant
  nonnegative := comparison.nonnegative
  bound field := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg comparison.nonnegative (norm_nonneg _))).mp
    rw [mul_pow]
    exact CanonicalLatitudeFrameEnergyComparison.squaredBound
      period hPeriod comparison field

/-- All completed-space consequences are now unconditional once the explicit
latitude/frame comparison is supplied. -/
def canonicalPhysicalH1TraceOfLatitudeComparison
    (period : Real) (hPeriod : period ≠ 0)
    (comparison : CanonicalLatitudeFrameEnergyComparison period hPeriod) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod :=
  canonicalPhysicalH1Trace period hPeriod
    (canonicalPhysicalH1TraceBoundOfLatitudeComparison
      period hPeriod comparison)

theorem canonicalPhysicalH1TraceOfLatitudeComparison_agrees_on_smooth
    (period : Real) (hPeriod : period ≠ 0)
    (comparison : CanonicalLatitudeFrameEnergyComparison period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalH1TraceOfLatitudeComparison period hPeriod comparison
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field :=
  canonicalPhysicalH1Trace_agrees_on_smooth period hPeriod
    (canonicalPhysicalH1TraceBoundOfLatitudeComparison
      period hPeriod comparison) field

theorem canonicalPhysicalH1TraceOfLatitudeComparison_norm_le
    (period : Real) (hPeriod : period ≠ 0)
    (comparison : CanonicalLatitudeFrameEnergyComparison period hPeriod)
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    ‖canonicalPhysicalH1TraceOfLatitudeComparison
        period hPeriod comparison field‖ ≤
      comparison.constant * ‖field‖ :=
  canonicalPhysicalH1Trace_norm_le period hPeriod
    (canonicalPhysicalH1TraceBoundOfLatitudeComparison
      period hPeriod comparison) field

theorem canonicalPhysicalH1TraceExists_ofLatitudeComparison
    (period : Real) (hPeriod : period ≠ 0)
    (comparison : CanonicalLatitudeFrameEnergyComparison period hPeriod) :
    CanonicalPhysicalH1TraceExists period hPeriod :=
  (canonicalPhysicalH1TraceExists_iff period hPeriod).2
    ⟨canonicalPhysicalH1TraceBoundOfLatitudeComparison
      period hPeriod comparison⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
end JanusFormal
