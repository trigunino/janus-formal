import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.LocallyFinite
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D

/-!
# Periodic and antiperiodic boundary cores from one interior seed

A smooth function on `S² × ℝ` whose support lies in the interior of one
fundamental time interval can be extended in two canonical ways:

* summing all translates by `n T` gives a smooth `T`-periodic function;
* summing all translates by `2 n T` and subtracting its translate by `T` gives
  a smooth `T`-antiperiodic function.

The translate families are locally finite because the seed has support in one
bounded period.  On the chosen fundamental interval both constructions agree
with the seed almost everywhere.  Consequently a single density theorem for
smooth interior seeds implies density of both canonical boundary cores.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter Function
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalLatitudeSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance canonicalLatitudeBaseChartedSpace :
    ChartedSpace CanonicalLatitudeBaseModel CanonicalLatitudeBase :=
  inferInstance

local instance canonicalLatitudeBaseIsManifold :
    IsManifold canonicalLatitudeBaseModelWithCorners ω CanonicalLatitudeBase :=
  inferInstance

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

private abbrev BoundaryL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.CanonicalPhysicalScalarFirstSheetL2
    period

/-- Open interior of one canonical time period. -/
def canonicalLatitudeOpenFundamentalTime : Set Real :=
  Set.Ioo (min 0 period) (max 0 period)

/-- Smooth scalar seeds supported inside one open fundamental period. -/
structure CanonicalLatitudeSmoothInteriorSeedCore where
  toFun : CanonicalLatitudeBase → Real
  contMDiff_toFun : ContMDiff canonicalLatitudeBaseModelWithCorners
    𝓘(Real, Real) ∞ toFun
  support_subset : Function.support toFun ⊆
    (Set.univ : Set (Metric.sphere (0 : EuclideanR3) 1)) ×ˢ
      canonicalLatitudeOpenFundamentalTime period
  memLp_toFun : MemLp toFun (2 : ENNReal)
    (canonicalLatitudeBaseMeasure period)

instance : CoeFun (CanonicalLatitudeSmoothInteriorSeedCore period)
    (fun _ => CanonicalLatitudeBase → Real) :=
  ⟨CanonicalLatitudeSmoothInteriorSeedCore.toFun⟩

/-- Canonical `L²` realization of an interior seed. -/
def canonicalLatitudeSmoothInteriorSeedEmbedding
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    BoundaryL2 period :=
  seed.memLp_toFun.toLp seed.toFun

/-- Almost-everywhere representative of the seed embedding. -/
theorem canonicalLatitudeSmoothInteriorSeedEmbedding_ae
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    (canonicalLatitudeSmoothInteriorSeedEmbedding period seed :
        CanonicalLatitudeBase → Real) =ᵐ[canonicalLatitudeBaseMeasure period]
      seed.toFun :=
  seed.memLp_toFun.coeFn_toLp

/-- A seed vanishes whenever its time coordinate is outside the open
fundamental period. -/
theorem CanonicalLatitudeSmoothInteriorSeedCore.eq_zero_of_time_not_mem
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (base : CanonicalLatitudeBase)
    (hTime : base.2 ∉ canonicalLatitudeOpenFundamentalTime period) :
    seed base = 0 := by
  rw [← Function.notMem_support]
  intro hSupport
  exact hTime (seed.support_subset hSupport).2

/-- Every time in the open fundamental period has absolute value strictly less
than the period length. -/
theorem abs_lt_abs_period_of_mem_openFundamentalTime
    {time : Real}
    (hTime : time ∈ canonicalLatitudeOpenFundamentalTime period) :
    |time| < |period| := by
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · rw [canonicalLatitudeOpenFundamentalTime,
      min_eq_right hNegative.le, max_eq_left hNegative.le] at hTime
    rw [abs_of_nonpos hTime.2.le, abs_of_neg hNegative]
    linarith
  · rw [canonicalLatitudeOpenFundamentalTime,
      min_eq_left hPositive.le, max_eq_right hPositive.le] at hTime
    rw [abs_of_pos hTime.1, abs_of_pos hPositive]
    exact hTime.2

/-- Two points in one open fundamental interval differ by less than one period. -/
theorem abs_sub_lt_abs_period_of_mem_openFundamentalTime
    {first second : Real}
    (hFirst : first ∈ canonicalLatitudeOpenFundamentalTime period)
    (hSecond : second ∈ canonicalLatitudeOpenFundamentalTime period) :
    |first - second| < |period| := by
  rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
  · rw [canonicalLatitudeOpenFundamentalTime,
      min_eq_right hNegative.le, max_eq_left hNegative.le] at hFirst hSecond
    rw [abs_of_neg hNegative]
    rw [abs_lt]
    constructor <;> linarith
  · rw [canonicalLatitudeOpenFundamentalTime,
      min_eq_left hPositive.le, max_eq_right hPositive.le] at hFirst hSecond
    rw [abs_of_pos hPositive]
    rw [abs_lt]
    constructor <;> linarith

/-- Translation of an interior seed by one integer multiple of a real step. -/
def canonicalLatitudeInteriorSeedTranslate
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (step : Real) (winding : Int)
    (base : CanonicalLatitudeBase) : Real :=
  seed (base.1, base.2 + (winding : Real) * step)

/-- Every translated seed is smooth. -/
theorem canonicalLatitudeInteriorSeedTranslate_contMDiff
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (step : Real) (winding : Int) :
    ContMDiff canonicalLatitudeBaseModelWithCorners
      𝓘(Real, Real) ∞
      (canonicalLatitudeInteriorSeedTranslate seed step winding) := by
  unfold canonicalLatitudeInteriorSeedTranslate
  exact seed.contMDiff_toFun.comp
    (contMDiff_fst.prodMk
      (contMDiff_snd.add
        (contMDiff_const.mul contMDiff_const)))

/-- Integer translates of an interior seed form a locally finite family for
any nonzero step. -/
theorem canonicalLatitudeInteriorSeedTranslate_support_locallyFinite
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (step : Real) (hStep : step ≠ 0) :
    LocallyFinite fun winding : Int =>
      Function.support
        (canonicalLatitudeInteriorSeedTranslate seed step winding) := by
  intro base
  have hStepAbs : 0 < |step| := abs_pos.mpr hStep
  obtain ⟨bound, hBound⟩ := exists_nat_gt
    ((|base.2| + 1 + |period|) / |step|)
  let neighborhood : Set CanonicalLatitudeBase :=
    Prod.snd ⁻¹' Set.Ioo (base.2 - 1) (base.2 + 1)
  refine ⟨neighborhood, ?_, ?_⟩
  · exact ((isOpen_Ioo.preimage continuous_snd).mem_nhds
      (by simp [neighborhood]))
  · refine (Set.finite_Icc (-(bound : Int)) (bound : Int)).subset ?_
    intro winding hWinding
    change (Function.support
        (canonicalLatitudeInteriorSeedTranslate seed step winding) ∩
      neighborhood).Nonempty at hWinding
    rcases hWinding with ⟨nearby, hTerm, hNearby⟩
    have hShifted :
        (nearby.1, nearby.2 + (winding : Real) * step) ∈
          Function.support seed.toFun :=
      hTerm
    have hShiftedTime :
        nearby.2 + (winding : Real) * step ∈
          canonicalLatitudeOpenFundamentalTime period :=
      (seed.support_subset hShifted).2
    have hShiftedAbs :
        |nearby.2 + (winding : Real) * step| < |period| :=
      abs_lt_abs_period_of_mem_openFundamentalTime
        period hPeriod hShiftedTime
    have hNearbyInterval : nearby.2 ∈
        Set.Ioo (base.2 - 1) (base.2 + 1) := hNearby
    have hDifference : |nearby.2 - base.2| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hNearbyInterval.1, hNearbyInterval.2]
    have hNearbyAbs : |nearby.2| < |base.2| + 1 := by
      calc
        |nearby.2| = |base.2 + (nearby.2 - base.2)| := by
          congr 1
          ring
        _ ≤ |base.2| + |nearby.2 - base.2| := abs_add _ _
        _ < |base.2| + 1 := add_lt_add_left hDifference _
    have hProduct :
        |(winding : Real)| * |step| < |base.2| + 1 + |period| := by
      rw [← abs_mul]
      have hIdentity :
          (winding : Real) * step =
            (nearby.2 + (winding : Real) * step) - nearby.2 := by
        ring
      rw [hIdentity]
      calc
        |(nearby.2 + (winding : Real) * step) - nearby.2| ≤
            |nearby.2 + (winding : Real) * step| + |nearby.2| :=
          abs_sub _ _
        _ < |period| + (|base.2| + 1) :=
          add_lt_add hShiftedAbs hNearbyAbs
        _ = |base.2| + 1 + |period| := by ring
    have hWindingReal : |(winding : Real)| < (bound : Real) :=
      ((lt_div_iff₀ hStepAbs).2 hProduct).trans hBound
    have hBounds := (abs_lt.mp hWindingReal)
    constructor
    · exact_mod_cast hBounds.1.le
    · exact_mod_cast hBounds.2.le

/-- Locally finite smooth periodization with arbitrary nonzero step. -/
def canonicalLatitudeInteriorSeedPeriodization
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (step : Real) (base : CanonicalLatitudeBase) : Real :=
  ∑ᶠ winding : Int,
    canonicalLatitudeInteriorSeedTranslate seed step winding base

/-- Smoothness of a locally finite periodization. -/
theorem canonicalLatitudeInteriorSeedPeriodization_contMDiff
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (step : Real) (hStep : step ≠ 0) :
    ContMDiff canonicalLatitudeBaseModelWithCorners
      𝓘(Real, Real) ∞
      (canonicalLatitudeInteriorSeedPeriodization seed step) := by
  unfold canonicalLatitudeInteriorSeedPeriodization
  exact contMDiff_finsum
    (fun winding =>
      canonicalLatitudeInteriorSeedTranslate_contMDiff
        period seed step winding)
    (canonicalLatitudeInteriorSeedTranslate_support_locallyFinite
      period hPeriod seed step hStep)

/-- A periodization is periodic with its translation step. -/
theorem canonicalLatitudeInteriorSeedPeriodization_add_step
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (step : Real) (hStep : step ≠ 0)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeInteriorSeedPeriodization seed step
        (base.1, base.2 + step) =
      canonicalLatitudeInteriorSeedPeriodization seed step base := by
  let term : Int → Real := fun winding =>
    canonicalLatitudeInteriorSeedTranslate seed step winding base
  have hLeftFinite : HasFiniteSupport fun winding : Int =>
      canonicalLatitudeInteriorSeedTranslate seed step winding
        (base.1, base.2 + step) :=
    (canonicalLatitudeInteriorSeedTranslate_support_locallyFinite
      period hPeriod seed step hStep).point_finite (base.1, base.2 + step)
  have hRightFinite : HasFiniteSupport term :=
    (canonicalLatitudeInteriorSeedTranslate_support_locallyFinite
      period hPeriod seed step hStep).point_finite base
  unfold canonicalLatitudeInteriorSeedPeriodization
  calc
    (∑ᶠ winding : Int,
      canonicalLatitudeInteriorSeedTranslate seed step winding
        (base.1, base.2 + step)) =
        ∑' winding : Int,
          canonicalLatitudeInteriorSeedTranslate seed step winding
            (base.1, base.2 + step) := by
      symm
      rw [tsum_eq_finsum]
      exact hLeftFinite
    _ = ∑' winding : Int, term winding := by
      simpa [term, canonicalLatitudeInteriorSeedTranslate,
        Equiv.coe_addRight, Int.cast_add, Int.cast_one] using
        (Equiv.addRight (1 : Int)).tsum_eq term
    _ = ∑ᶠ winding : Int, term winding := by
      rw [tsum_eq_finsum]
      exact hRightFinite

/-- A nonzero integer shift by a step at least one period long cannot keep two
times inside the same open fundamental period. -/
theorem winding_eq_zero_of_time_and_shift_mem
    (step : Real) (hStep : step ≠ 0)
    (hStepLong : |period| ≤ |step|)
    (time : Real) (winding : Int)
    (hTime : time ∈ canonicalLatitudeOpenFundamentalTime period)
    (hShifted : time + (winding : Real) * step ∈
      canonicalLatitudeOpenFundamentalTime period) :
    winding = 0 := by
  by_contra hWinding
  have hWindingAbs : (1 : Real) ≤ |(winding : Real)| := by
    rcases Int.le_neg_one_or_one_le hWinding with hNegative | hPositive
    · have hCast : (winding : Real) ≤ -1 := by exact_mod_cast hNegative
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hCast : (1 : Real) ≤ winding := by exact_mod_cast hPositive
      rw [abs_of_nonneg (by linarith)]
      exact hCast
  have hDifference :
      |(time + (winding : Real) * step) - time| < |period| :=
    abs_sub_lt_abs_period_of_mem_openFundamentalTime
      period hPeriod hShifted hTime
  have hStepLe : |step| ≤ |(winding : Real) * step| := by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg step) hWindingAbs
  have hIdentity :
      |(time + (winding : Real) * step) - time| =
        |(winding : Real) * step| := by
    congr 1
    ring
  rw [hIdentity] at hDifference
  exact (not_lt_of_ge (hStepLong.trans hStepLe)) hDifference

/-- On the open fundamental period, ordinary periodization agrees with the
original seed. -/
theorem canonicalLatitudeInteriorSeedPeriodization_eq_seed
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (base : CanonicalLatitudeBase)
    (hTime : base.2 ∈ canonicalLatitudeOpenFundamentalTime period) :
    canonicalLatitudeInteriorSeedPeriodization seed period base = seed base := by
  unfold canonicalLatitudeInteriorSeedPeriodization
  apply finsum_eq_single _ 0
  intro winding hWinding
  apply seed.eq_zero_of_time_not_mem
  intro hShifted
  exact hWinding
    (winding_eq_zero_of_time_and_shift_mem
      period hPeriod period hPeriod (le_refl _)
      base.2 winding hTime hShifted)

/-- Almost every boundary-base time lies in the open fundamental period. -/
theorem ae_canonicalLatitudeBase_time_mem_openFundamentalTime :
    ∀ᵐ base ∂canonicalLatitudeBaseMeasure period,
      base.2 ∈ canonicalLatitudeOpenFundamentalTime period := by
  unfold canonicalLatitudeBaseMeasure
  rw [Measure.prod_ae_iff]
  filter_upwards [] with sphere
  have hInterval :
      ∀ᵐ time ∂volume.restrict
          (canonicalLatitudeTimeInterval period),
        time ∈ canonicalLatitudeTimeInterval period :=
    ae_restrict_mem measurableSet_Ioc
  have hEndpoint :
      ∀ᵐ time ∂volume.restrict
          (canonicalLatitudeTimeInterval period),
        time ≠ max 0 period :=
    Measure.ae_ne _ (max 0 period)
  filter_upwards [hInterval, hEndpoint] with time hTime hEndpoint
  exact ⟨hTime.1, lt_of_le_of_ne hTime.2 hEndpoint⟩

/-- Ordinary periodic extension of one interior seed. -/
def canonicalLatitudePeriodicCoreOfInteriorSeed
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    CanonicalLatitudeSmoothPeriodicValueCore period where
  toFun := canonicalLatitudeInteriorSeedPeriodization seed period
  contMDiff_toFun :=
    canonicalLatitudeInteriorSeedPeriodization_contMDiff
      period hPeriod seed period hPeriod
  deck_periodic := fun base =>
    canonicalLatitudeInteriorSeedPeriodization_add_step
      period hPeriod seed period hPeriod base
  memLp_toFun := by
    apply seed.memLp_toFun.ae_eq
    filter_upwards
      [ae_canonicalLatitudeBase_time_mem_openFundamentalTime period hPeriod]
      with base hTime
    exact (canonicalLatitudeInteriorSeedPeriodization_eq_seed
      period hPeriod seed base hTime).symm

/-- Double-periodic extension used to construct the antiperiodic core. -/
def canonicalLatitudeDoublePeriodization
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    CanonicalLatitudeBase → Real :=
  canonicalLatitudeInteriorSeedPeriodization seed (2 * period)

/-- Smoothness of the double-periodic extension. -/
theorem canonicalLatitudeDoublePeriodization_contMDiff
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    ContMDiff canonicalLatitudeBaseModelWithCorners
      𝓘(Real, Real) ∞
      (canonicalLatitudeDoublePeriodization seed) :=
  canonicalLatitudeInteriorSeedPeriodization_contMDiff
    period hPeriod seed (2 * period) (mul_ne_zero two_ne_zero hPeriod)

/-- Double periodicity. -/
theorem canonicalLatitudeDoublePeriodization_add_two_period
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeDoublePeriodization seed
        (base.1, base.2 + 2 * period) =
      canonicalLatitudeDoublePeriodization seed base :=
  canonicalLatitudeInteriorSeedPeriodization_add_step
    period hPeriod seed (2 * period)
      (mul_ne_zero two_ne_zero hPeriod) base

/-- On the fundamental interval, double periodization still agrees with the
seed. -/
theorem canonicalLatitudeDoublePeriodization_eq_seed
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (base : CanonicalLatitudeBase)
    (hTime : base.2 ∈ canonicalLatitudeOpenFundamentalTime period) :
    canonicalLatitudeDoublePeriodization seed base = seed base := by
  unfold canonicalLatitudeDoublePeriodization
    canonicalLatitudeInteriorSeedPeriodization
  apply finsum_eq_single _ 0
  intro winding hWinding
  apply seed.eq_zero_of_time_not_mem
  intro hShifted
  apply hWinding
  apply winding_eq_zero_of_time_and_shift_mem
    period hPeriod (2 * period) (mul_ne_zero two_ne_zero hPeriod)
      _ base.2 winding hTime hShifted
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  nlinarith [abs_nonneg period]

/-- A half-period translate of the double periodization vanishes on the chosen
open fundamental interval. -/
theorem canonicalLatitudeDoublePeriodization_add_period_eq_zero
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period)
    (base : CanonicalLatitudeBase)
    (hTime : base.2 ∈ canonicalLatitudeOpenFundamentalTime period) :
    canonicalLatitudeDoublePeriodization seed
      (base.1, base.2 + period) = 0 := by
  unfold canonicalLatitudeDoublePeriodization
    canonicalLatitudeInteriorSeedPeriodization
  apply finsum_congr
  intro winding
  apply seed.eq_zero_of_time_not_mem
  intro hShifted
  let oddWinding : Int := 2 * winding + 1
  have hOddShift :
      base.2 + (oddWinding : Real) * period =
        (base.2 + period) + (winding : Real) * (2 * period) := by
    dsimp [oddWinding]
    push_cast
    ring
  have hOddZero := winding_eq_zero_of_time_and_shift_mem
    period hPeriod period hPeriod (le_refl _)
    base.2 oddWinding hTime (hOddShift ▸ hShifted)
  have hOddNe : oddWinding ≠ 0 := by
    dsimp [oddWinding]
    omega
  exact (hOddNe hOddZero).elim

/-- Antiperiodic extension obtained from a double-periodic extension. -/
def canonicalLatitudeAntiperiodicCoreOfInteriorSeed
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    CanonicalLatitudeSmoothAntiperiodicNormalCore period where
  toFun := fun base =>
    canonicalLatitudeDoublePeriodization seed base -
      canonicalLatitudeDoublePeriodization seed (base.1, base.2 + period)
  contMDiff_toFun := by
    exact (canonicalLatitudeDoublePeriodization_contMDiff
      period hPeriod seed).sub
      ((canonicalLatitudeDoublePeriodization_contMDiff
        period hPeriod seed).comp
        (contMDiff_fst.prodMk
          (contMDiff_snd.add contMDiff_const)))
  deck_antiperiodic := by
    intro base
    rw [canonicalLatitudeDoublePeriodization_add_two_period]
    ring
  memLp_toFun := by
    apply seed.memLp_toFun.ae_eq
    filter_upwards
      [ae_canonicalLatitudeBase_time_mem_openFundamentalTime period hPeriod]
      with base hTime
    rw [canonicalLatitudeDoublePeriodization_eq_seed
      period hPeriod seed base hTime]
    rw [canonicalLatitudeDoublePeriodization_add_period_eq_zero
      period hPeriod seed base hTime]
    ring

/-- The periodic core embedding is exactly the seed embedding. -/
theorem canonicalLatitudePeriodicCoreOfInteriorSeed_embedding
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    canonicalLatitudeSmoothPeriodicValueEmbedding period
        (canonicalLatitudePeriodicCoreOfInteriorSeed period hPeriod seed) =
      canonicalLatitudeSmoothInteriorSeedEmbedding period seed := by
  apply Lp.ext
  filter_upwards
    [canonicalLatitudeSmoothPeriodicValueEmbedding_ae period
      (canonicalLatitudePeriodicCoreOfInteriorSeed period hPeriod seed),
     canonicalLatitudeSmoothInteriorSeedEmbedding_ae period seed,
     ae_canonicalLatitudeBase_time_mem_openFundamentalTime period hPeriod]
    with base hPeriodic hSeed hTime
  rw [hPeriodic, hSeed]
  exact canonicalLatitudeInteriorSeedPeriodization_eq_seed
    period hPeriod seed base hTime

/-- The antiperiodic core embedding is exactly the seed embedding. -/
theorem canonicalLatitudeAntiperiodicCoreOfInteriorSeed_embedding
    (seed : CanonicalLatitudeSmoothInteriorSeedCore period) :
    canonicalLatitudeSmoothAntiperiodicNormalEmbedding period
        (canonicalLatitudeAntiperiodicCoreOfInteriorSeed period hPeriod seed) =
      canonicalLatitudeSmoothInteriorSeedEmbedding period seed := by
  apply Lp.ext
  filter_upwards
    [canonicalLatitudeSmoothAntiperiodicNormalEmbedding_ae period
      (canonicalLatitudeAntiperiodicCoreOfInteriorSeed period hPeriod seed),
     canonicalLatitudeSmoothInteriorSeedEmbedding_ae period seed,
     ae_canonicalLatitudeBase_time_mem_openFundamentalTime period hPeriod]
    with base hNormal hSeed hTime
  rw [hNormal, hSeed]
  rw [canonicalLatitudeDoublePeriodization_eq_seed
    period hPeriod seed base hTime]
  rw [canonicalLatitudeDoublePeriodization_add_period_eq_zero
    period hPeriod seed base hTime]
  ring

/-- The sole remaining density statement for both canonical boundary cores. -/
structure CanonicalLatitudeSmoothInteriorSeedDensityData where
  dense : DenseRange
    (canonicalLatitudeSmoothInteriorSeedEmbedding period)

namespace CanonicalLatitudeSmoothInteriorSeedDensityData

/-- One dense interior-seed core makes both canonical boundary cores dense. -/
def toSmoothBoundaryCoreDensityData
    (density : CanonicalLatitudeSmoothInteriorSeedDensityData period) :
    CanonicalLatitudeSmoothBoundaryCoreDensityData period where
  valueDense := by
    apply density.dense.mono
    rintro value ⟨seed, rfl⟩
    exact ⟨canonicalLatitudePeriodicCoreOfInteriorSeed
      period hPeriod seed,
      canonicalLatitudePeriodicCoreOfInteriorSeed_embedding
        period hPeriod seed⟩
  normalDense := by
    apply density.dense.mono
    rintro value ⟨seed, rfl⟩
    exact ⟨canonicalLatitudeAntiperiodicCoreOfInteriorSeed
      period hPeriod seed,
      canonicalLatitudeAntiperiodicCoreOfInteriorSeed_embedding
        period hPeriod seed⟩

/-- Periodization density certificate. -/
theorem certificate
    (density : CanonicalLatitudeSmoothInteriorSeedDensityData period) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) :=
  ⟨(density.toSmoothBoundaryCoreDensityData hPeriod).valueDense,
    (density.toSmoothBoundaryCoreDensityData hPeriod).normalDense⟩

end CanonicalLatitudeSmoothInteriorSeedDensityData

end
end P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D
end JanusFormal
