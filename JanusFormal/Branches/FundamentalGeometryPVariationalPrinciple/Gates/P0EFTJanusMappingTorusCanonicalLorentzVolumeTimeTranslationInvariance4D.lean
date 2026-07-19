import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteTimeFlow4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

/-!
# Canonical Lorentz volume under the complete D8 time flow

The half-open time fundamental domain is translated modulo one period.  An
odd winding also applies the reflected-sphere monodromy.  This gives a genuine
measure-preserving skew product on the fundamental domain, semiconjugate to
the complete time flow on the actual quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private theorem canonicalTimeInterval_eq_absFundamentalDomain :
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

private def canonicalSpacetimeTimeWrap
    (shift time : Real) : Real :=
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  (AddCircle.equivIoc |period| (min 0 period)
    ((time : AddCircle |period|) + (shift : AddCircle |period|))).1

attribute [local instance] Measure.Subtype.measureSpace in
private theorem canonicalSpacetimeTimeWrap_measurePreserving (shift : Real) :
    MeasurePreserving (canonicalSpacetimeTimeWrap period hPeriod shift)
      (volume.restrict (canonicalLatitudeTimeInterval period))
      (volume.restrict (canonicalLatitudeTimeInterval period)) := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  rw [canonicalTimeInterval_eq_absFundamentalDomain period]
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

private def absoluteTimeWinding (shift time : Real) : Int :=
  toIocDiv (abs_pos.mpr hPeriod) (min 0 period) (time + shift)

private theorem absoluteTimeWinding_eq_ceil (shift time : Real) :
    absoluteTimeWinding period hPeriod shift time =
      ⌈((time + shift - min 0 period) / |period| : Real)⌉ - 1 := by
  apply (toIocDiv_eq_iff (abs_pos.mpr hPeriod)).2
  simp only [zsmul_eq_mul]
  have hAbs : 0 < |period| := abs_pos.mpr hPeriod
  let value := (time + shift - min 0 period) / |period|
  have hLower : value ≤ (⌈value⌉ : Int) := Int.le_ceil value
  have hUpper : ((⌈value⌉ : Int) : Real) < value + 1 :=
    Int.ceil_lt_add_one value
  have hValue : value * |period| = time + shift - min 0 period := by
    dsimp [value]
    exact div_mul_cancel₀ _ hAbs.ne'
  change min 0 period <
      time + shift - (((⌈value⌉ : Int) - 1 : Int) : Real) * |period| ∧
    time + shift - (((⌈value⌉ : Int) - 1 : Int) : Real) * |period| ≤
      min 0 period + |period|
  push_cast
  have hPositiveFactor : 0 <
      (value - ((⌈value⌉ : Int) : Real) + 1) * |period| :=
    mul_pos (by linarith) hAbs
  have hNonpositiveFactor :
      (value - ((⌈value⌉ : Int) : Real)) * |period| ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hLower) hAbs.le
  constructor
  · nlinarith
  · nlinarith

private theorem absoluteTimeWinding_measurable (shift : Real) :
    Measurable (absoluteTimeWinding period hPeriod shift) := by
  have hValue : Measurable fun time : Real =>
      (time + shift - min 0 period) / |period| :=
    ((measurable_id.add_const shift).sub_const (min 0 period)).div_const |period|
  have hCeil : Measurable fun time : Real =>
      ⌈((time + shift - min 0 period) / |period| : Real)⌉ :=
    hValue.ceil
  convert hCeil.sub_const 1 using 1
  funext time
  exact absoluteTimeWinding_eq_ceil period hPeriod shift time

private def signedTimeWinding (shift time : Real) : Int :=
  if 0 < period then absoluteTimeWinding period hPeriod shift time
  else -absoluteTimeWinding period hPeriod shift time

private theorem signedTimeWinding_measurable (shift : Real) :
    Measurable (signedTimeWinding period hPeriod shift) := by
  by_cases hPositive : 0 < period
  · change Measurable (fun time => if 0 < period then
        absoluteTimeWinding period hPeriod shift time
      else -absoluteTimeWinding period hPeriod shift time)
    simpa only [if_pos hPositive] using
      absoluteTimeWinding_measurable period hPeriod shift
  · change Measurable (fun time => if 0 < period then
        absoluteTimeWinding period hPeriod shift time
      else -absoluteTimeWinding period hPeriod shift time)
    simpa only [if_neg hPositive] using
      (absoluteTimeWinding_measurable period hPeriod shift).neg

private theorem canonicalSpacetimeTimeWrap_absolute_deck
    (shift time : Real) :
    canonicalSpacetimeTimeWrap period hPeriod shift time +
        (absoluteTimeWinding period hPeriod shift time : Real) * |period| =
      time + shift := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  change toIocMod (abs_pos.mpr hPeriod) (min 0 period) (time + shift) +
      (toIocDiv (abs_pos.mpr hPeriod) (min 0 period) (time + shift) : Real) *
        |period| = time + shift
  rw [toIocMod]
  simp only [zsmul_eq_mul]
  ring

private theorem canonicalSpacetimeTimeWrap_deck
    (shift time : Real) :
    canonicalSpacetimeTimeWrap period hPeriod shift time +
        (signedTimeWinding period hPeriod shift time : Real) * period =
      time + shift := by
  have hAbsolute := canonicalSpacetimeTimeWrap_absolute_deck
    period hPeriod shift time
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · rw [abs_of_neg hNegative] at hAbsolute
    simp only [signedTimeWinding, if_neg (not_lt.mpr hNegative.le), Int.cast_neg]
    nlinarith
  · rw [abs_of_pos hPositive] at hAbsolute
    simpa [signedTimeWinding, hPositive] using hAbsolute

private def sphereWindingTwist (winding : Int)
    (point : StandardSphere) : StandardSphere :=
  if Even winding then point else spherePT point

private theorem sphereReflection_square :
    sphereReflection * sphereReflection = 1 := by
  apply Homeomorph.ext
  intro point
  apply Subtype.ext
  change P0EFTJanusReflectionFixedThroat.reflectPoint
      (P0EFTJanusReflectionFixedThroat.reflectPoint point.1) = point.1
  exact P0EFTJanusReflectionFixedThroat.reflect_point_involutive point.1

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

private theorem sphereReflection_zpow_twist_cancel
    (winding : Int) (point : StandardSphere) :
    (sphereReflection ^ winding)
        (unitThreeSphereHomeomorph.symm
          (sphereWindingTwist winding point)) =
      unitThreeSphereHomeomorph.symm point := by
  rw [sphereReflection_zpow_apply_parity]
  by_cases hEven : Even winding
  · simp [sphereWindingTwist, hEven]
  · simp only [sphereWindingTwist, if_neg hEven]
    rw [unitSphere_conjugacy]
    exact sphereReflection.left_inv _

private theorem sphereWindingTwist_uncurry_measurable (shift : Real) :
    Measurable (Function.uncurry fun time point =>
      sphereWindingTwist
        (signedTimeWinding period hPeriod shift time) point) := by
  have hWinding := signedTimeWinding_measurable period hPeriod shift
  have hEvenInt : MeasurableSet {winding : Int | Even winding} :=
    MeasurableSet.of_discrete
  have hEven : MeasurableSet
      {input : Real × StandardSphere |
        Even (signedTimeWinding period hPeriod shift input.1)} :=
    (hWinding.comp measurable_fst) hEvenInt
  change Measurable (fun input : Real × StandardSphere =>
    if Even (signedTimeWinding period hPeriod shift input.1)
    then input.2 else spherePT input.2)
  exact Measurable.ite hEven measurable_snd
    (spherePT_continuous.measurable.comp measurable_snd)

def spacetimeBaseTimeTranslation (shift : Real)
    (base : SpacetimeBase) : SpacetimeBase :=
  (sphereWindingTwist
      (signedTimeWinding period hPeriod shift base.2) base.1,
    canonicalSpacetimeTimeWrap period hPeriod shift base.2)

theorem spacetimeBaseTimeTranslation_measurePreserving (shift : Real) :
    MeasurePreserving (spacetimeBaseTimeTranslation period hPeriod shift)
      (spacetimeBaseMeasure period) (spacetimeBaseMeasure period) := by
  let sphereMeasure := (volume : Measure EuclideanR4).toSphere
  let timeMeasure := volume.restrict (canonicalLatitudeTimeInterval period)
  have hSkew : MeasurePreserving
      (fun input : Real × StandardSphere =>
        (canonicalSpacetimeTimeWrap period hPeriod shift input.1,
          sphereWindingTwist
            (signedTimeWinding period hPeriod shift input.1) input.2))
      (timeMeasure.prod sphereMeasure) (timeMeasure.prod sphereMeasure) := by
    refine MeasurePreserving.skew_product
      (μa := timeMeasure) (μb := timeMeasure)
      (μc := sphereMeasure) (μd := sphereMeasure)
      (f := canonicalSpacetimeTimeWrap period hPeriod shift)
      (g := fun time point => sphereWindingTwist
        (signedTimeWinding period hPeriod shift time) point)
      (canonicalSpacetimeTimeWrap_measurePreserving
        period hPeriod shift) ?_ ?_
    · exact sphereWindingTwist_uncurry_measurable period hPeriod shift
    · exact Filter.Eventually.of_forall fun time => by
        by_cases hEven : Even (signedTimeWinding period hPeriod shift time)
        · simpa [sphereWindingTwist, hEven] using
            (MeasurePreserving.id sphereMeasure).map_eq
        · simpa [sphereWindingTwist, hEven] using spherePT_measurePreserving.map_eq
  change MeasurePreserving
    (fun base : StandardSphere × Real =>
      (sphereWindingTwist
          (signedTimeWinding period hPeriod shift base.2) base.1,
        canonicalSpacetimeTimeWrap period hPeriod shift base.2))
    (sphereMeasure.prod timeMeasure) (sphereMeasure.prod timeMeasure)
  have hSwapForward : MeasurePreserving Prod.swap
      (sphereMeasure.prod timeMeasure) (timeMeasure.prod sphereMeasure) :=
    Measure.measurePreserving_swap
  have hSwapBackward : MeasurePreserving Prod.swap
      (timeMeasure.prod sphereMeasure) (sphereMeasure.prod timeMeasure) :=
    Measure.measurePreserving_swap
  simpa [Function.comp_def] using
    (hSwapBackward.comp (hSkew.comp hSwapForward))

theorem effectiveTimeFlow_spacetimeFundamentalDomainMap_wrapped
    (shift : Real) (base : SpacetimeBase) :
    effectiveTimeFlow period hPeriod shift
        (spacetimeFundamentalDomainMap period hPeriod base) =
      spacetimeFundamentalDomainMap period hPeriod
        (spacetimeBaseTimeTranslation period hPeriod shift base) := by
  unfold spacetimeFundamentalDomainMap spacetimeBaseTimeTranslation
  rw [effectiveTimeFlow_mk, mappingTorusMk_eq_iff_exists_vadd]
  let winding := signedTimeWinding period hPeriod shift base.2
  refine ⟨winding, ?_⟩
  apply MappingTorusCover.ext
  · change (sphereReflection ^ winding)
        (unitThreeSphereHomeomorph.symm
          (sphereWindingTwist winding base.1)) =
      unitThreeSphereHomeomorph.symm base.1
    exact sphereReflection_zpow_twist_cancel winding base.1
  · change canonicalSpacetimeTimeWrap period hPeriod shift base.2 +
        (winding : Real) * period = base.2 + shift
    exact canonicalSpacetimeTimeWrap_deck period hPeriod shift base.2

theorem intrinsicCanonicalLorentzVolumeMeasure_timeTranslation_measurePreserving
    (shift : Real) :
    MeasurePreserving (effectiveTimeFlow period hPeriod shift)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_spacetimeBase]
  apply MeasurePreserving.of_semiconj
    ((spacetimeFundamentalDomainMap_continuous period hPeriod).measurable.measurePreserving
      (spacetimeBaseMeasure period))
    (spacetimeBaseTimeTranslation_measurePreserving period hPeriod shift)
  · intro base
    exact (effectiveTimeFlow_spacetimeFundamentalDomainMap_wrapped
      period hPeriod shift base).symm
  · exact (effectiveTimeFlow_contMDiff
      period hPeriod shift).continuous.measurable

theorem intrinsicCanonicalLorentzVolumeMeasure_timeTranslation_map
    (shift : Real) :
    Measure.map (effectiveTimeFlow period hPeriod shift)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod :=
  (intrinsicCanonicalLorentzVolumeMeasure_timeTranslation_measurePreserving
    period hPeriod shift).map_eq

end

end P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
end JanusFormal
