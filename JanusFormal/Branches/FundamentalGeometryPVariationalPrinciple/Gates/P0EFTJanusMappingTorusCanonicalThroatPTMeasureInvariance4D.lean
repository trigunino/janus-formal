import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-!
# Canonical throat PT measure invariance

The canonical throat measure is the pushforward of round `S²` measure times
one half-open time period.  Reflection of that fundamental period descends to
the actual throat PT involution, proving the remaining measure contract and
making all integrated BV/PT covariance statements unconditional.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVPTCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-! ## Fundamental-domain reflection -/

/-- The representative of `-time` in the translated half-open period. -/
def canonicalLatitudeBasePT (base : CanonicalLatitudeBase) :
    CanonicalLatitudeBase :=
  (base.1, period - base.2)

@[simp]
theorem canonicalLatitudeBasePT_involutive (base : CanonicalLatitudeBase) :
    canonicalLatitudeBasePT period
        (canonicalLatitudeBasePT period base) = base := by
  ext <;> simp [canonicalLatitudeBasePT]

theorem canonicalLatitudeBasePT_continuous :
    Continuous (canonicalLatitudeBasePT period) := by
  exact continuous_fst.prodMk (continuous_const.sub continuous_snd)

theorem canonicalLatitudeBasePT_measurable :
    Measurable (canonicalLatitudeBasePT period) :=
  (canonicalLatitudeBasePT_continuous period).measurable

/-- Reflection about the midpoint of a nonzero signed period preserves its
Lebesgue fundamental-domain measure. -/
theorem canonicalLatitudeTimeReflection_measurePreserving
    (hPeriod : period ≠ 0) :
    MeasurePreserving (fun time : Real => period - time)
      (volume.restrict (canonicalLatitudeTimeInterval period))
      (volume.restrict (canonicalLatitudeTimeInterval period)) := by
  have hPreimage :
      (fun time : Real => period - time) ⁻¹'
          Ico (min 0 period) (max 0 period) =
        Ioc (min 0 period) (max 0 period) := by
    by_cases hPositive : 0 < period
    · rw [min_eq_left hPositive.le, max_eq_right hPositive.le]
      ext time
      simp only [mem_preimage, mem_Ico, mem_Ioc]
      constructor <;> rintro ⟨hFirst, hSecond⟩ <;>
        constructor <;> linarith
    · have hNegative : period < 0 :=
        lt_of_le_of_ne (le_of_not_gt hPositive) hPeriod
      rw [min_eq_right hNegative.le, max_eq_left hNegative.le]
      ext time
      simp only [mem_preimage, mem_Ico, mem_Ioc]
      constructor <;> rintro ⟨hFirst, hSecond⟩ <;>
        constructor <;> linarith
  have hRestricted :=
    (volume.measurePreserving_sub_left period).restrict_preimage
      (measurableSet_Ico : MeasurableSet
        (Ico (min 0 period) (max 0 period)))
  rw [hPreimage] at hRestricted
  simpa only [canonicalLatitudeTimeInterval,
    restrict_Ico_eq_restrict_Ioc] using hRestricted

/-- Product preservation on round `S²` times the time fundamental domain. -/
theorem canonicalLatitudeBasePT_measurePreserving
    (hPeriod : period ≠ 0) :
    MeasurePreserving (canonicalLatitudeBasePT period)
      (canonicalLatitudeBaseMeasure period)
      (canonicalLatitudeBaseMeasure period) := by
  change MeasurePreserving
    (Prod.map id (fun time : Real => period - time))
    (((volume : Measure EuclideanR3).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
    (((volume : Measure EuclideanR3).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact (MeasurePreserving.id
    ((volume : Measure EuclideanR3).toSphere)).prod
      (canonicalLatitudeTimeReflection_measurePreserving period hPeriod)

/-! ## Descent to the actual throat -/

/-- The translated fundamental-domain reflection represents actual quotient
time reversal. -/
theorem fixedThroatPT_canonicalLatitudeThroatMap
    (base : CanonicalLatitudeBase) :
    fixedThroatPT period hPeriod
        (canonicalLatitudeThroatMap period hPeriod base) =
      canonicalLatitudeThroatMap period hPeriod
        (canonicalLatitudeBasePT period base) := by
  unfold fixedThroatPT canonicalLatitudeThroatMap canonicalLatitudeAnchor
    canonicalLatitudeBasePT
  rw [mappingTorusTimeReversal_mk,
    mappingTorusMk_eq_iff_exists_vadd]
  refine ⟨-1, ?_⟩
  apply MappingTorusCover.ext
  · rw [vadd_fiber]
    simp [fixedEquatorData]
  · rw [vadd_time]
    change (period - base.2) + ((-1 : Int) : Real) * period = -base.2
    norm_num
    ring

/-- Canonical throat PT preserves the installed intrinsic throat measure. -/
theorem intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving :
    CanonicalThroatPTMeasureInvariant period hPeriod := by
  change MeasurePreserving (fixedThroatPTMeasurableEquiv period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
  apply MeasurePreserving.of_semiconj
    ((canonicalLatitudeThroatMap_continuous period hPeriod).measurable.measurePreserving
      (canonicalLatitudeBaseMeasure period))
    (canonicalLatitudeBasePT_measurePreserving period hPeriod)
  · intro base
    exact (fixedThroatPT_canonicalLatitudeThroatMap
      period hPeriod base).symm
  · exact (fixedThroatPTMeasurableEquiv period hPeriod).measurable

/-! ## Unconditional integrated BV/PT covariance -/

theorem canonicalSmoothThroatBVMasterAction_pt_unconditional
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalSmoothThroatBVMasterAction period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field) =
      canonicalSmoothThroatBVMasterAction period hPeriod field :=
  canonicalSmoothThroatBVMasterAction_pt period hPeriod
    (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
      period hPeriod) field

theorem canonicalSmoothThroatBVMasterFirstVariation_pt_unconditional
    (field variation : SmoothFiniteMetricBVField period hPeriod) :
    canonicalSmoothThroatBVMasterFirstVariation period hPeriod
        (smoothFiniteMetricBVPT period hPeriod field)
        (smoothFiniteMetricBVPT period hPeriod variation) =
      canonicalSmoothThroatBVMasterFirstVariation period hPeriod
        field variation :=
  canonicalSmoothThroatBVMasterFirstVariation_pt period hPeriod
    (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
      period hPeriod) field variation

theorem canonicalUltralocalBVFunctionalValue_pt_unconditional
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVFunctionalValue period hPeriod
        (smoothUltralocalBVFunctionalPT functional)
        (smoothFiniteMetricBVPT period hPeriod field) =
      canonicalUltralocalBVFunctionalValue period hPeriod functional field :=
  canonicalUltralocalBVFunctionalValue_pt period hPeriod
    (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
      period hPeriod) functional field

theorem canonicalUltralocalBVOddAntibracket_pt_unconditional
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT first)
        (smoothUltralocalBVFunctionalPT second)
        (smoothFiniteMetricBVPT period hPeriod field) =
      canonicalUltralocalBVOddAntibracket period hPeriod
        first second field :=
  canonicalUltralocalBVOddAntibracket_pt period hPeriod
    (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
      period hPeriod) first second field

theorem canonicalSmoothThroatBV_integrated_CME_pt_unconditional
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVOddAntibracket period hPeriod
        (smoothUltralocalBVFunctionalPT
          smoothThroatBVMasterUltralocalFunctional)
        (smoothUltralocalBVFunctionalPT
          smoothThroatBVMasterUltralocalFunctional)
        (smoothFiniteMetricBVPT period hPeriod field) = 0 :=
  canonicalSmoothThroatBV_integrated_CME_pt period hPeriod
    (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
      period hPeriod) field

end
end P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
end JanusFormal
