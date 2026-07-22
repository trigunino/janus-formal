import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecificLimits.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D

/-!
# Expanding smooth cutoffs inside one boundary period

Let `a = min 0 T`, `b = max 0 T`, with midpoint `m` and half-length
`r = |T| / 2`.  For every `n`, choose the standard smooth bump centered at `m`
with outer radius `r` and inner radius

`r - r / (n + 2)`.

It is supported strictly inside `(a,b)`, takes values in `[0,1]`, and is equal
to one on an increasing family of closed intervals exhausting `(a,b)`.  Hence
it converges pointwise, and almost everywhere for the canonical boundary
measure, to one.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeInteriorTimeCutoff4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Midpoint of the canonical fundamental time interval. -/
def canonicalLatitudeFundamentalTimeMidpoint : Real :=
  (min 0 period + max 0 period) / 2

/-- Half the length of one nonzero period. -/
def canonicalLatitudeFundamentalTimeHalfLength : Real :=
  |period| / 2

/-- The half-length is positive. -/
theorem canonicalLatitudeFundamentalTimeHalfLength_pos :
    0 < canonicalLatitudeFundamentalTimeHalfLength period := by
  unfold canonicalLatitudeFundamentalTimeHalfLength
  positivity

/-- Shrinking transition width of the `n`th time cutoff. -/
def canonicalLatitudeFundamentalTimeTransitionWidth
    (index : Nat) : Real :=
  canonicalLatitudeFundamentalTimeHalfLength period / (index + 2 : Real)

/-- Inner radius of the `n`th time cutoff. -/
def canonicalLatitudeFundamentalTimeInnerRadius
    (index : Nat) : Real :=
  canonicalLatitudeFundamentalTimeHalfLength period -
    canonicalLatitudeFundamentalTimeTransitionWidth period index

/-- Transition width is positive. -/
theorem canonicalLatitudeFundamentalTimeTransitionWidth_pos
    (index : Nat) :
    0 < canonicalLatitudeFundamentalTimeTransitionWidth period index := by
  unfold canonicalLatitudeFundamentalTimeTransitionWidth
  positivity

/-- The inner radius is positive. -/
theorem canonicalLatitudeFundamentalTimeInnerRadius_pos
    (index : Nat) :
    0 < canonicalLatitudeFundamentalTimeInnerRadius period index := by
  let halfLength := canonicalLatitudeFundamentalTimeHalfLength period
  have hHalfLength : 0 < halfLength :=
    canonicalLatitudeFundamentalTimeHalfLength_pos period hPeriod
  have hDenominator : 1 < (index + 2 : Real) := by
    norm_num
  have hDivision : halfLength / (index + 2 : Real) < halfLength := by
    exact (div_lt_iff₀ (by positivity : (0 : Real) < index + 2)).2
      (by nlinarith)
  unfold canonicalLatitudeFundamentalTimeInnerRadius
    canonicalLatitudeFundamentalTimeTransitionWidth
  exact sub_pos.mpr hDivision

/-- The inner radius is strictly below the outer radius. -/
theorem canonicalLatitudeFundamentalTimeInnerRadius_lt_halfLength
    (index : Nat) :
    canonicalLatitudeFundamentalTimeInnerRadius period index <
      canonicalLatitudeFundamentalTimeHalfLength period := by
  unfold canonicalLatitudeFundamentalTimeInnerRadius
  linarith [canonicalLatitudeFundamentalTimeTransitionWidth_pos period index]

/-- The canonical expanding smooth time cutoff. -/
def canonicalLatitudeInteriorTimeCutoff
    (index : Nat) :
    ContDiffBump (canonicalLatitudeFundamentalTimeMidpoint period) :=
  ⟨canonicalLatitudeFundamentalTimeInnerRadius period index,
    canonicalLatitudeFundamentalTimeHalfLength period,
    canonicalLatitudeFundamentalTimeInnerRadius_pos period hPeriod index,
    canonicalLatitudeFundamentalTimeInnerRadius_lt_halfLength period index⟩

/-- Smoothness of every time cutoff. -/
theorem canonicalLatitudeInteriorTimeCutoff_contDiff
    (index : Nat) :
    ContDiff Real ∞ (canonicalLatitudeInteriorTimeCutoff period hPeriod index) :=
  ContDiffBump.contDiff _

/-- Midpoint minus half-length is the left endpoint. -/
theorem canonicalLatitudeFundamentalTimeMidpoint_sub_halfLength :
    canonicalLatitudeFundamentalTimeMidpoint period -
        canonicalLatitudeFundamentalTimeHalfLength period =
      min 0 period := by
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · rw [canonicalLatitudeFundamentalTimeMidpoint,
      canonicalLatitudeFundamentalTimeHalfLength,
      min_eq_right hNegative.le, max_eq_left hNegative.le,
      abs_of_neg hNegative]
    ring
  · rw [canonicalLatitudeFundamentalTimeMidpoint,
      canonicalLatitudeFundamentalTimeHalfLength,
      min_eq_left hPositive.le, max_eq_right hPositive.le,
      abs_of_pos hPositive]
    ring

/-- Midpoint plus half-length is the right endpoint. -/
theorem canonicalLatitudeFundamentalTimeMidpoint_add_halfLength :
    canonicalLatitudeFundamentalTimeMidpoint period +
        canonicalLatitudeFundamentalTimeHalfLength period =
      max 0 period := by
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · rw [canonicalLatitudeFundamentalTimeMidpoint,
      canonicalLatitudeFundamentalTimeHalfLength,
      min_eq_right hNegative.le, max_eq_left hNegative.le,
      abs_of_neg hNegative]
    ring
  · rw [canonicalLatitudeFundamentalTimeMidpoint,
      canonicalLatitudeFundamentalTimeHalfLength,
      min_eq_left hPositive.le, max_eq_right hPositive.le,
      abs_of_pos hPositive]
    ring

/-- Distance from the midpoint is below the half-length exactly on the open
fundamental interval. -/
theorem dist_midpoint_lt_halfLength_iff
    (time : Real) :
    dist time (canonicalLatitudeFundamentalTimeMidpoint period) <
        canonicalLatitudeFundamentalTimeHalfLength period ↔
      time ∈ canonicalLatitudeOpenFundamentalTime period := by
  rw [Real.dist_eq, abs_lt]
  unfold canonicalLatitudeOpenFundamentalTime
  constructor
  · intro hDistance
    rw [← canonicalLatitudeFundamentalTimeMidpoint_sub_halfLength
        period hPeriod,
      ← canonicalLatitudeFundamentalTimeMidpoint_add_halfLength
        period hPeriod]
    constructor <;> linarith
  · intro hTime
    rw [← canonicalLatitudeFundamentalTimeMidpoint_sub_halfLength
        period hPeriod,
      ← canonicalLatitudeFundamentalTimeMidpoint_add_halfLength
        period hPeriod] at hTime
    constructor <;> linarith

/-- The time cutoff is nonnegative. -/
theorem canonicalLatitudeInteriorTimeCutoff_nonnegative
    (index : Nat) (time : Real) :
    0 ≤ canonicalLatitudeInteriorTimeCutoff period hPeriod index time :=
  ContDiffBump.nonneg _

/-- The time cutoff is at most one. -/
theorem canonicalLatitudeInteriorTimeCutoff_le_one
    (index : Nat) (time : Real) :
    canonicalLatitudeInteriorTimeCutoff period hPeriod index time ≤ 1 :=
  ContDiffBump.le_one _

/-- Every time cutoff is supported inside the open fundamental interval. -/
theorem canonicalLatitudeInteriorTimeCutoff_support_subset
    (index : Nat) :
    Function.support
        (canonicalLatitudeInteriorTimeCutoff period hPeriod index) ⊆
      canonicalLatitudeOpenFundamentalTime period := by
  intro time hTime
  apply (dist_midpoint_lt_halfLength_iff period hPeriod time).1
  by_contra hDistance
  have hZero := ContDiffBump.zero_of_le_dist
    (canonicalLatitudeInteriorTimeCutoff period hPeriod index)
    (le_of_not_gt hDistance)
  exact hTime hZero

/-- The transition widths converge to zero. -/
theorem canonicalLatitudeFundamentalTimeTransitionWidth_tendsto_zero :
    Tendsto
      (canonicalLatitudeFundamentalTimeTransitionWidth period)
      atTop (𝓝 0) := by
  have hDenominator : Tendsto
      (fun index : Nat => (index + 2 : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hInverse : Tendsto
      (fun index : Nat => ((index + 2 : Real))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hDenominator
  simpa [canonicalLatitudeFundamentalTimeTransitionWidth,
    div_eq_mul_inv] using
    hInverse.const_mul
      (canonicalLatitudeFundamentalTimeHalfLength period)

/-- Inner radii converge to the whole half-length. -/
theorem canonicalLatitudeFundamentalTimeInnerRadius_tendsto_halfLength :
    Tendsto
      (canonicalLatitudeFundamentalTimeInnerRadius period)
      atTop
      (𝓝 (canonicalLatitudeFundamentalTimeHalfLength period)) := by
  simpa [canonicalLatitudeFundamentalTimeInnerRadius] using
    tendsto_const_nhds.sub
      (canonicalLatitudeFundamentalTimeTransitionWidth_tendsto_zero period)

/-- At every interior time, the cutoff is eventually exactly one. -/
theorem canonicalLatitudeInteriorTimeCutoff_eventuallyEq_one
    (time : Real)
    (hTime : time ∈ canonicalLatitudeOpenFundamentalTime period) :
    (fun index : Nat =>
      canonicalLatitudeInteriorTimeCutoff period hPeriod index time) =ᶠ[atTop]
      fun _ => 1 := by
  have hDistance :
      dist time (canonicalLatitudeFundamentalTimeMidpoint period) <
        canonicalLatitudeFundamentalTimeHalfLength period :=
    (dist_midpoint_lt_halfLength_iff period hPeriod time).2 hTime
  have hEventually : ∀ᶠ index : Nat in atTop,
      dist time (canonicalLatitudeFundamentalTimeMidpoint period) <
        canonicalLatitudeFundamentalTimeInnerRadius period index :=
    (canonicalLatitudeFundamentalTimeInnerRadius_tendsto_halfLength period)
      (Set.Ioi_mem_nhds hDistance)
  filter_upwards [hEventually] with index hIndex
  exact ContDiffBump.one_of_mem_closedBall
    (canonicalLatitudeInteriorTimeCutoff period hPeriod index)
    (le_of_lt hIndex)

/-- Pointwise convergence to one throughout the open period. -/
theorem canonicalLatitudeInteriorTimeCutoff_tendsto_one
    (time : Real)
    (hTime : time ∈ canonicalLatitudeOpenFundamentalTime period) :
    Tendsto
      (fun index : Nat =>
        canonicalLatitudeInteriorTimeCutoff period hPeriod index time)
      atTop (𝓝 1) :=
  (canonicalLatitudeInteriorTimeCutoff_eventuallyEq_one
    period hPeriod time hTime).tendsto

/-- Base-level cutoff depending only on time. -/
def canonicalLatitudeInteriorBaseCutoff
    (index : Nat) (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeInteriorTimeCutoff period hPeriod index base.2

/-- Smoothness of the base cutoff. -/
theorem canonicalLatitudeInteriorBaseCutoff_contMDiff
    (index : Nat) :
    ContMDiff canonicalLatitudeBaseModelWithCorners
      𝓘(Real, Real) ∞
      (canonicalLatitudeInteriorBaseCutoff period hPeriod index) :=
  (canonicalLatitudeInteriorTimeCutoff_contDiff period hPeriod index)
    |>.contMDiff.comp contMDiff_snd

/-- Base cutoff support lies in the interior seed region. -/
theorem canonicalLatitudeInteriorBaseCutoff_support_subset
    (index : Nat) :
    Function.support
        (canonicalLatitudeInteriorBaseCutoff period hPeriod index) ⊆
      (Set.univ : Set (Metric.sphere (0 : EuclideanR3) 1)) ×ˢ
        canonicalLatitudeOpenFundamentalTime period := by
  intro base hBase
  exact ⟨Set.mem_univ _,
    canonicalLatitudeInteriorTimeCutoff_support_subset
      period hPeriod index hBase⟩

/-- Almost-everywhere convergence of the base cutoffs to one. -/
theorem ae_canonicalLatitudeInteriorBaseCutoff_tendsto_one :
    ∀ᵐ base ∂canonicalLatitudeBaseMeasure period,
      Tendsto
        (fun index : Nat =>
          canonicalLatitudeInteriorBaseCutoff period hPeriod index base)
        atTop (𝓝 1) := by
  filter_upwards
    [ae_canonicalLatitudeBase_time_mem_openFundamentalTime period hPeriod]
    with base hTime
  exact canonicalLatitudeInteriorTimeCutoff_tendsto_one
    period hPeriod base.2 hTime

/-- Expanding interior-cutoff certificate. -/
theorem canonicalLatitudeInteriorTimeCutoff_certificate
    (index : Nat) :
    ContDiff Real ∞
        (canonicalLatitudeInteriorTimeCutoff period hPeriod index) ∧
      (∀ time, 0 ≤ canonicalLatitudeInteriorTimeCutoff period hPeriod index time) ∧
      (∀ time, canonicalLatitudeInteriorTimeCutoff period hPeriod index time ≤ 1) ∧
      Function.support
          (canonicalLatitudeInteriorTimeCutoff period hPeriod index) ⊆
        canonicalLatitudeOpenFundamentalTime period :=
  ⟨canonicalLatitudeInteriorTimeCutoff_contDiff period hPeriod index,
    canonicalLatitudeInteriorTimeCutoff_nonnegative period hPeriod index,
    canonicalLatitudeInteriorTimeCutoff_le_one period hPeriod index,
    canonicalLatitudeInteriorTimeCutoff_support_subset period hPeriod index⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeInteriorTimeCutoff4D
end JanusFormal
