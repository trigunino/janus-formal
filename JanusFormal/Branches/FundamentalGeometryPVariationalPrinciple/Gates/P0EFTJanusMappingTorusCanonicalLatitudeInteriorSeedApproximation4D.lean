import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeInteriorTimeCutoff4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedDensityReduction4D

/-!
# Density of smooth interior boundary seeds

For a bounded continuous boundary function `f`, first multiply by the expanding
smooth time cutoff `χₙ`.  Dominated convergence gives

`χₙ f → f` in boundary `L²`.

Next use Mathlib's manifold smooth approximation theorem with pointwise error
`1/(n+1)`.  Because smooth approximation preserves support, the approximant is
still supported in the open fundamental interval.  Its uniform error from
`χₙ f` tends to zero, hence so does its `L²` error.

The resulting diagonal sequence proves density of the smooth interior seed
core.  Periodization then proves density of both the periodic value core and the
antiperiodic normal core unconditionally.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedApproximation4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalLatitudeBoundaryCoreDensityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedPeriodization4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorTimeCutoff4D
open P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedDensityReduction4D

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

/-- Bounded continuous source multiplied by the `n`th interior time cutoff. -/
def canonicalLatitudeInteriorCutContinuousField
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) (base : CanonicalLatitudeBase) : Real :=
  canonicalLatitudeInteriorBaseCutoff period hPeriod index base *
    continuousField base

/-- Continuity of every cut field. -/
theorem canonicalLatitudeInteriorCutContinuousField_continuous
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) :
    Continuous
      (canonicalLatitudeInteriorCutContinuousField
        period hPeriod continuousField index) :=
  (canonicalLatitudeInteriorBaseCutoff_contMDiff
    period hPeriod index).continuous.mul continuousField.continuous

/-- Cut fields are bounded by the original bounded continuous field. -/
theorem canonicalLatitudeInteriorCutContinuousField_norm_le
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) (base : CanonicalLatitudeBase) :
    ‖canonicalLatitudeInteriorCutContinuousField
        period hPeriod continuousField index base‖ ≤
      ‖continuousField‖ := by
  unfold canonicalLatitudeInteriorCutContinuousField
  rw [Real.norm_eq_abs, abs_mul]
  have hCutoffAbs :
      |canonicalLatitudeInteriorBaseCutoff period hPeriod index base| ≤ 1 := by
    rw [abs_of_nonneg
      (canonicalLatitudeInteriorTimeCutoff_nonnegative
        period hPeriod index base.2)]
    exact canonicalLatitudeInteriorTimeCutoff_le_one
      period hPeriod index base.2
  calc
    _ ≤ 1 * |continuousField base| :=
      mul_le_mul_of_nonneg_right hCutoffAbs (abs_nonneg _)
    _ = ‖continuousField base‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖continuousField‖ := continuousField.norm_coe_le_norm base

/-- Every cut field belongs to boundary `L²`. -/
theorem canonicalLatitudeInteriorCutContinuousField_memLp
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) :
    MemLp
      (canonicalLatitudeInteriorCutContinuousField
        period hPeriod continuousField index)
      (2 : ENNReal) (canonicalLatitudeBaseMeasure period) :=
  MemLp.of_bound
    (canonicalLatitudeInteriorCutContinuousField_continuous
      period hPeriod continuousField index).aestronglyMeasurable
    ‖continuousField‖
    (Filter.Eventually.of_forall fun base =>
      canonicalLatitudeInteriorCutContinuousField_norm_le
        period hPeriod continuousField index base)

/-- Boundary `L²` realization of the cut continuous field. -/
def canonicalLatitudeInteriorCutContinuousL2
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) : BoundaryL2 period :=
  (canonicalLatitudeInteriorCutContinuousField_memLp
    period hPeriod continuousField index).toLp
      (canonicalLatitudeInteriorCutContinuousField
        period hPeriod continuousField index)

/-- Almost-everywhere representative of a cut field. -/
theorem canonicalLatitudeInteriorCutContinuousL2_ae
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) :
    (canonicalLatitudeInteriorCutContinuousL2
        period hPeriod continuousField index :
      CanonicalLatitudeBase → Real) =ᵐ[canonicalLatitudeBaseMeasure period]
      canonicalLatitudeInteriorCutContinuousField
        period hPeriod continuousField index :=
  (canonicalLatitudeInteriorCutContinuousField_memLp
    period hPeriod continuousField index).coeFn_toLp

/-- Almost-everywhere representative of the original bounded continuous `L²`
vector. -/
theorem boundedContinuousToCanonicalLatitudeBoundaryL2_ae
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    (boundedContinuousToCanonicalLatitudeBoundaryL2
        period continuousField : CanonicalLatitudeBase → Real) =ᵐ[
          canonicalLatitudeBaseMeasure period] continuousField :=
  BoundedContinuousFunction.coeFn_toLp
    (2 : ENNReal) (canonicalLatitudeBaseMeasure period) Real continuousField

/-- Squared error density of the endpoint cutoff. -/
def canonicalLatitudeInteriorCutErrorDensity
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) (base : CanonicalLatitudeBase) : Real :=
  ((canonicalLatitudeInteriorBaseCutoff period hPeriod index base - 1) *
    continuousField base) ^ 2

/-- Cutoff error density is continuous. -/
theorem canonicalLatitudeInteriorCutErrorDensity_continuous
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) :
    Continuous
      (canonicalLatitudeInteriorCutErrorDensity
        period hPeriod continuousField index) := by
  unfold canonicalLatitudeInteriorCutErrorDensity
  exact (((canonicalLatitudeInteriorBaseCutoff_contMDiff
    period hPeriod index).continuous.sub continuous_const).mul
      continuousField.continuous).pow 2

/-- Cutoff error is dominated by the original squared field. -/
theorem canonicalLatitudeInteriorCutErrorDensity_le
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) (base : CanonicalLatitudeBase) :
    canonicalLatitudeInteriorCutErrorDensity
        period hPeriod continuousField index base ≤
      continuousField base ^ 2 := by
  let cutoff := canonicalLatitudeInteriorBaseCutoff
    period hPeriod index base
  have hCutoffNonnegative : 0 ≤ cutoff :=
    canonicalLatitudeInteriorTimeCutoff_nonnegative
      period hPeriod index base.2
  have hCutoffLeOne : cutoff ≤ 1 :=
    canonicalLatitudeInteriorTimeCutoff_le_one
      period hPeriod index base.2
  have hCoefficient : (cutoff - 1) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg cutoff, sq_nonneg (cutoff - 1)]
  unfold canonicalLatitudeInteriorCutErrorDensity
  change ((cutoff - 1) * continuousField base) ^ 2 ≤
    continuousField base ^ 2
  rw [mul_pow]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hCoefficient
      (sq_nonneg (continuousField base))

/-- The squared bounded continuous source is integrable. -/
theorem boundedContinuous_sq_integrable
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    Integrable (fun base => continuousField base ^ 2)
      (canonicalLatitudeBaseMeasure period) := by
  have hMemLp : MemLp continuousField (2 : ENNReal)
      (canonicalLatitudeBaseMeasure period) :=
    MemLp.of_bound continuousField.continuous.aestronglyMeasurable
      ‖continuousField‖
      (Filter.Eventually.of_forall fun base =>
        continuousField.norm_coe_le_norm base)
  exact hMemLp.integrable_sq

/-- Pointwise almost-everywhere convergence of the cutoff error density. -/
theorem ae_canonicalLatitudeInteriorCutErrorDensity_tendsto_zero
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    ∀ᵐ base ∂canonicalLatitudeBaseMeasure period,
      Tendsto
        (fun index : Nat =>
          canonicalLatitudeInteriorCutErrorDensity
            period hPeriod continuousField index base)
        atTop (𝓝 0) := by
  filter_upwards
    [ae_canonicalLatitudeInteriorBaseCutoff_tendsto_one period hPeriod]
    with base hCutoff
  have hDifference : Tendsto
      (fun index : Nat =>
        canonicalLatitudeInteriorBaseCutoff period hPeriod index base - 1)
      atTop (𝓝 0) := by
    simpa using hCutoff.sub_const 1
  have hProduct : Tendsto
      (fun index : Nat =>
        (canonicalLatitudeInteriorBaseCutoff period hPeriod index base - 1) *
          continuousField base)
      atTop (𝓝 0) := by
    simpa using hDifference.mul_const (continuousField base)
  simpa [canonicalLatitudeInteriorCutErrorDensity] using hProduct.pow 2

/-- Dominated convergence for the squared endpoint-cutoff error. -/
theorem integral_canonicalLatitudeInteriorCutErrorDensity_tendsto_zero
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    Tendsto
      (fun index : Nat =>
        ∫ base,
          canonicalLatitudeInteriorCutErrorDensity
            period hPeriod continuousField index base
          ∂canonicalLatitudeBaseMeasure period)
      atTop (𝓝 0) := by
  have hTarget := tendsto_integral_of_dominated_convergence
    (fun base : CanonicalLatitudeBase => continuousField base ^ 2)
    (fun index =>
      (canonicalLatitudeInteriorCutErrorDensity_continuous
        period hPeriod continuousField index).aestronglyMeasurable)
    (boundedContinuous_sq_integrable period continuousField)
    (fun index => Filter.Eventually.of_forall fun base => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      exact canonicalLatitudeInteriorCutErrorDensity_le
        period hPeriod continuousField index base)
    (ae_canonicalLatitudeInteriorCutErrorDensity_tendsto_zero
      period hPeriod continuousField)
  simpa using hTarget

/-- Squared `L²` endpoint-cutoff error equals its pointwise integral. -/
theorem norm_sq_canonicalLatitudeInteriorCutContinuousL2_sub
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) :
    ‖canonicalLatitudeInteriorCutContinuousL2
          period hPeriod continuousField index -
        boundedContinuousToCanonicalLatitudeBoundaryL2
          period continuousField‖ ^ 2 =
      ∫ base,
        canonicalLatitudeInteriorCutErrorDensity
          period hPeriod continuousField index base
        ∂canonicalLatitudeBaseMeasure period := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [Lp.coeFn_sub
      (canonicalLatitudeInteriorCutContinuousL2
        period hPeriod continuousField index)
      (boundedContinuousToCanonicalLatitudeBoundaryL2
        period continuousField),
     canonicalLatitudeInteriorCutContinuousL2_ae
      period hPeriod continuousField index,
     boundedContinuousToCanonicalLatitudeBoundaryL2_ae
      period continuousField]
    with base hSub hCut hField
  rw [hSub, hCut, hField]
  unfold canonicalLatitudeInteriorCutContinuousField
    canonicalLatitudeInteriorCutErrorDensity
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  ring

/-- Endpoint-cutoff vectors converge in boundary `L²`. -/
theorem canonicalLatitudeInteriorCutContinuousL2_tendsto
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    Tendsto
      (canonicalLatitudeInteriorCutContinuousL2
        period hPeriod continuousField)
      atTop
      (𝓝 (boundedContinuousToCanonicalLatitudeBoundaryL2
        period continuousField)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hSquare : Tendsto
      (fun index : Nat =>
        ‖canonicalLatitudeInteriorCutContinuousL2
            period hPeriod continuousField index -
          boundedContinuousToCanonicalLatitudeBoundaryL2
            period continuousField‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_sq_canonicalLatitudeInteriorCutContinuousL2_sub] using
      integral_canonicalLatitudeInteriorCutErrorDensity_tendsto_zero
        period hPeriod continuousField
  have hSqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hSquare
  change Tendsto
    (fun index : Nat => Real.sqrt
      (‖canonicalLatitudeInteriorCutContinuousL2
          period hPeriod continuousField index -
        boundedContinuousToCanonicalLatitudeBoundaryL2
          period continuousField‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hSqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hSqrt

/-- Uniform smooth approximation radius. -/
def canonicalLatitudeInteriorSmoothApproximationRadius
    (index : Nat) : Real :=
  1 / (index + 1 : Real)

/-- Smooth approximation radii are positive. -/
theorem canonicalLatitudeInteriorSmoothApproximationRadius_pos
    (index : Nat) :
    0 < canonicalLatitudeInteriorSmoothApproximationRadius index := by
  unfold canonicalLatitudeInteriorSmoothApproximationRadius
  positivity

/-- Existence of a smooth support-preserving approximation to a cut continuous
field. -/
theorem exists_canonicalLatitudeSmoothInteriorApproximation
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) :
    ∃ approximation : CanonicalLatitudeBase → Real,
      ContMDiff canonicalLatitudeBaseModelWithCorners
        𝓘(Real, Real) ∞ approximation ∧
      (∀ base,
        dist
          (canonicalLatitudeInteriorCutContinuousField
            period hPeriod continuousField index base)
          (approximation base) <
            canonicalLatitudeInteriorSmoothApproximationRadius index) ∧
      Function.support approximation ⊆
        (Set.univ : Set (Metric.sphere (0 : EuclideanR3) 1)) ×ˢ
          canonicalLatitudeOpenFundamentalTime period := by
  obtain ⟨approximation, hSmooth, hDistance, hSupport⟩ :=
    (canonicalLatitudeInteriorCutContinuousField_continuous
      period hPeriod continuousField index).exists_contMDiff_approx
      canonicalLatitudeBaseModelWithCorners ∞
      (continuous_const : Continuous
        (fun _ : CanonicalLatitudeBase =>
          canonicalLatitudeInteriorSmoothApproximationRadius index))
      (fun _ => canonicalLatitudeInteriorSmoothApproximationRadius_pos index)
  refine ⟨approximation, hSmooth, hDistance, ?_⟩
  exact hSupport.trans <| by
    intro base hBase
    exact canonicalLatitudeInteriorBaseCutoff_support_subset
      period hPeriod index <| by
        intro hCutoff
        apply hBase
        unfold canonicalLatitudeInteriorCutContinuousField
        rw [hCutoff, zero_mul]

/-- Chosen smooth interior approximation. -/
def canonicalLatitudeSmoothInteriorApproximationFunction
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) : CanonicalLatitudeBase → Real :=
  Classical.choose
    (exists_canonicalLatitudeSmoothInteriorApproximation
      period hPeriod continuousField index)

/-- Chosen smooth interior seed. -/
def canonicalLatitudeSmoothInteriorApproximation
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) : CanonicalLatitudeSmoothInteriorSeedCore period where
  toFun := canonicalLatitudeSmoothInteriorApproximationFunction
    period hPeriod continuousField index
  contMDiff_toFun :=
    (Classical.choose_spec
      (exists_canonicalLatitudeSmoothInteriorApproximation
        period hPeriod continuousField index)).1
  support_subset :=
    (Classical.choose_spec
      (exists_canonicalLatitudeSmoothInteriorApproximation
        period hPeriod continuousField index)).2.2
  memLp_toFun := by
    let approximation := canonicalLatitudeSmoothInteriorApproximationFunction
      period hPeriod continuousField index
    have hDistance :=
      (Classical.choose_spec
        (exists_canonicalLatitudeSmoothInteriorApproximation
          period hPeriod continuousField index)).2.1
    have hSmooth :=
      (Classical.choose_spec
        (exists_canonicalLatitudeSmoothInteriorApproximation
          period hPeriod continuousField index)).1
    apply MemLp.of_bound hSmooth.continuous.aestronglyMeasurable
      (‖continuousField‖ + 1)
    exact Filter.Eventually.of_forall fun base => by
      have hCutBound := canonicalLatitudeInteriorCutContinuousField_norm_le
        period hPeriod continuousField index base
      have hApprox :
          ‖approximation base -
              canonicalLatitudeInteriorCutContinuousField
                period hPeriod continuousField index base‖ < 1 := by
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hDistance base).trans_le <| by
          unfold canonicalLatitudeInteriorSmoothApproximationRadius
          have hDenominator : (1 : Real) ≤ index + 1 := by positivity
          exact one_div_le_one hDenominator
      calc
        ‖approximation base‖ ≤
            ‖approximation base -
                canonicalLatitudeInteriorCutContinuousField
                  period hPeriod continuousField index base‖ +
              ‖canonicalLatitudeInteriorCutContinuousField
                period hPeriod continuousField index base‖ := by
          simpa only [sub_add_cancel] using
            norm_add_le
              (approximation base -
                canonicalLatitudeInteriorCutContinuousField
                  period hPeriod continuousField index base)
              (canonicalLatitudeInteriorCutContinuousField
                period hPeriod continuousField index base)
        _ ≤ 1 + ‖continuousField‖ :=
          add_le_add hApprox.le hCutBound
        _ = ‖continuousField‖ + 1 := add_comm _ _

/-- Pointwise approximation estimate of the chosen smooth seed. -/
theorem canonicalLatitudeSmoothInteriorApproximation_spec
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) (base : CanonicalLatitudeBase) :
    dist
      (canonicalLatitudeInteriorCutContinuousField
        period hPeriod continuousField index base)
      (canonicalLatitudeSmoothInteriorApproximation
        period hPeriod continuousField index base) <
      canonicalLatitudeInteriorSmoothApproximationRadius index :=
  (Classical.choose_spec
    (exists_canonicalLatitudeSmoothInteriorApproximation
      period hPeriod continuousField index)).2.1 base

/-- Squared smooth-versus-cut approximation error. -/
def canonicalLatitudeSmoothInteriorApproximationErrorDensity
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) (base : CanonicalLatitudeBase) : Real :=
  (canonicalLatitudeSmoothInteriorApproximation
      period hPeriod continuousField index base -
    canonicalLatitudeInteriorCutContinuousField
      period hPeriod continuousField index base) ^ 2

/-- Smooth approximation error is bounded by the squared approximation radius. -/
theorem canonicalLatitudeSmoothInteriorApproximationErrorDensity_le
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) (base : CanonicalLatitudeBase) :
    canonicalLatitudeSmoothInteriorApproximationErrorDensity
        period hPeriod continuousField index base ≤
      canonicalLatitudeInteriorSmoothApproximationRadius index ^ 2 := by
  unfold canonicalLatitudeSmoothInteriorApproximationErrorDensity
  have hDistance := canonicalLatitudeSmoothInteriorApproximation_spec
    period hPeriod continuousField index base
  rw [Real.dist_eq, abs_sub_comm] at hDistance
  nlinarith [sq_nonneg
    (canonicalLatitudeSmoothInteriorApproximation
      period hPeriod continuousField index base -
      canonicalLatitudeInteriorCutContinuousField
        period hPeriod continuousField index base)]

/-- Smooth approximation radii converge to zero. -/
theorem canonicalLatitudeInteriorSmoothApproximationRadius_tendsto_zero :
    Tendsto canonicalLatitudeInteriorSmoothApproximationRadius
      atTop (𝓝 0) := by
  simpa [canonicalLatitudeInteriorSmoothApproximationRadius] using
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- Smooth-versus-cut error densities converge pointwise to zero. -/
theorem canonicalLatitudeSmoothInteriorApproximationErrorDensity_tendsto_zero
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (base : CanonicalLatitudeBase) :
    Tendsto
      (fun index : Nat =>
        canonicalLatitudeSmoothInteriorApproximationErrorDensity
          period hPeriod continuousField index base)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun index => sq_nonneg _)
    (Filter.Eventually.of_forall fun index =>
      canonicalLatitudeSmoothInteriorApproximationErrorDensity_le
        period hPeriod continuousField index base)
  exact (canonicalLatitudeInteriorSmoothApproximationRadius_tendsto_zero.pow 2)

/-- Dominated convergence for the smooth-versus-cut squared error. -/
theorem integral_canonicalLatitudeSmoothInteriorApproximationErrorDensity_tendsto_zero
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    Tendsto
      (fun index : Nat =>
        ∫ base,
          canonicalLatitudeSmoothInteriorApproximationErrorDensity
            period hPeriod continuousField index base
          ∂canonicalLatitudeBaseMeasure period)
      atTop (𝓝 0) := by
  have hOneIntegrable : Integrable
      (fun _ : CanonicalLatitudeBase => (1 : Real))
      (canonicalLatitudeBaseMeasure period) :=
    integrable_const 1
  have hTarget := tendsto_integral_of_dominated_convergence
    (fun _ : CanonicalLatitudeBase => (1 : Real))
    (fun index =>
      ((canonicalLatitudeSmoothInteriorApproximation
        period hPeriod continuousField index).contMDiff_toFun.continuous.sub
        (canonicalLatitudeInteriorCutContinuousField_continuous
          period hPeriod continuousField index)).pow 2
        |>.aestronglyMeasurable)
    hOneIntegrable
    (fun index => Filter.Eventually.of_forall fun base => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (canonicalLatitudeSmoothInteriorApproximationErrorDensity_le
        period hPeriod continuousField index base).trans <| by
          have hRadius :
              canonicalLatitudeInteriorSmoothApproximationRadius index ≤ 1 := by
            unfold canonicalLatitudeInteriorSmoothApproximationRadius
            have hDenominator : (1 : Real) ≤ index + 1 := by positivity
            exact one_div_le_one hDenominator
          nlinarith [sq_nonneg
            (canonicalLatitudeInteriorSmoothApproximationRadius index - 1)])
    (Filter.Eventually.of_forall fun base =>
      canonicalLatitudeSmoothInteriorApproximationErrorDensity_tendsto_zero
        period hPeriod continuousField base)
  simpa using hTarget

/-- Squared `L²` distance between the smooth seed and the cut field. -/
theorem norm_sq_smoothInteriorApproximation_sub_cut
    (continuousField : CanonicalLatitudeBase →ᵇ Real)
    (index : Nat) :
    ‖canonicalLatitudeSmoothInteriorSeedEmbedding period
          (canonicalLatitudeSmoothInteriorApproximation
            period hPeriod continuousField index) -
        canonicalLatitudeInteriorCutContinuousL2
          period hPeriod continuousField index‖ ^ 2 =
      ∫ base,
        canonicalLatitudeSmoothInteriorApproximationErrorDensity
          period hPeriod continuousField index base
        ∂canonicalLatitudeBaseMeasure period := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [Lp.coeFn_sub
      (canonicalLatitudeSmoothInteriorSeedEmbedding period
        (canonicalLatitudeSmoothInteriorApproximation
          period hPeriod continuousField index))
      (canonicalLatitudeInteriorCutContinuousL2
        period hPeriod continuousField index),
     canonicalLatitudeSmoothInteriorSeedEmbedding_ae period
      (canonicalLatitudeSmoothInteriorApproximation
        period hPeriod continuousField index),
     canonicalLatitudeInteriorCutContinuousL2_ae
      period hPeriod continuousField index]
    with base hSub hSmooth hCut
  rw [hSub, hSmooth, hCut]
  unfold canonicalLatitudeSmoothInteriorApproximationErrorDensity
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Smooth seed embeddings converge to the corresponding cut vectors. -/
theorem smoothInteriorApproximation_sub_cut_norm_tendsto_zero
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    Tendsto
      (fun index : Nat =>
        ‖canonicalLatitudeSmoothInteriorSeedEmbedding period
            (canonicalLatitudeSmoothInteriorApproximation
              period hPeriod continuousField index) -
          canonicalLatitudeInteriorCutContinuousL2
            period hPeriod continuousField index‖)
      atTop (𝓝 0) := by
  have hSquare : Tendsto
      (fun index : Nat =>
        ‖canonicalLatitudeSmoothInteriorSeedEmbedding period
            (canonicalLatitudeSmoothInteriorApproximation
              period hPeriod continuousField index) -
          canonicalLatitudeInteriorCutContinuousL2
            period hPeriod continuousField index‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_sq_smoothInteriorApproximation_sub_cut] using
      integral_canonicalLatitudeSmoothInteriorApproximationErrorDensity_tendsto_zero
        period hPeriod continuousField
  have hSqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hSquare
  change Tendsto
    (fun index : Nat => Real.sqrt
      (‖canonicalLatitudeSmoothInteriorSeedEmbedding period
          (canonicalLatitudeSmoothInteriorApproximation
            period hPeriod continuousField index) -
        canonicalLatitudeInteriorCutContinuousL2
          period hPeriod continuousField index‖ ^ 2))
    atTop (𝓝 (Real.sqrt 0)) at hSqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hSqrt

/-- The diagonal smooth interior seeds converge to the original bounded
continuous boundary vector. -/
theorem canonicalLatitudeSmoothInteriorApproximation_tendsto_l2
    (continuousField : CanonicalLatitudeBase →ᵇ Real) :
    Tendsto
      (fun index : Nat =>
        canonicalLatitudeSmoothInteriorSeedEmbedding period
          (canonicalLatitudeSmoothInteriorApproximation
            period hPeriod continuousField index))
      atTop
      (𝓝 (boundedContinuousToCanonicalLatitudeBoundaryL2
        period continuousField)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hFirst := smoothInteriorApproximation_sub_cut_norm_tendsto_zero
    period hPeriod continuousField
  have hSecond : Tendsto
      (fun index : Nat =>
        ‖canonicalLatitudeInteriorCutContinuousL2
            period hPeriod continuousField index -
          boundedContinuousToCanonicalLatitudeBoundaryL2
            period continuousField‖)
      atTop (𝓝 0) := by
    simpa [tendsto_iff_norm_sub_tendsto_zero] using
      canonicalLatitudeInteriorCutContinuousL2_tendsto
        period hPeriod continuousField
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun index => norm_nonneg _)
    (Filter.Eventually.of_forall fun index => by
      calc
        ‖canonicalLatitudeSmoothInteriorSeedEmbedding period
              (canonicalLatitudeSmoothInteriorApproximation
                period hPeriod continuousField index) -
            boundedContinuousToCanonicalLatitudeBoundaryL2
              period continuousField‖ ≤
          ‖canonicalLatitudeSmoothInteriorSeedEmbedding period
              (canonicalLatitudeSmoothInteriorApproximation
                period hPeriod continuousField index) -
            canonicalLatitudeInteriorCutContinuousL2
              period hPeriod continuousField index‖ +
          ‖canonicalLatitudeInteriorCutContinuousL2
              period hPeriod continuousField index -
            boundedContinuousToCanonicalLatitudeBoundaryL2
              period continuousField‖ := by
            simpa only [sub_add_sub_cancel] using
              norm_add_le
                (canonicalLatitudeSmoothInteriorSeedEmbedding period
                  (canonicalLatitudeSmoothInteriorApproximation
                    period hPeriod continuousField index) -
                  canonicalLatitudeInteriorCutContinuousL2
                    period hPeriod continuousField index)
                (canonicalLatitudeInteriorCutContinuousL2
                  period hPeriod continuousField index -
                  boundedContinuousToCanonicalLatitudeBoundaryL2
                    period continuousField))
  exact hFirst.add hSecond

/-- Unconditional common interior-seed approximation package. -/
def canonicalLatitudeContinuousInteriorSeedApproximationData :
    CanonicalLatitudeContinuousInteriorSeedApproximationData period where
  approximation := canonicalLatitudeSmoothInteriorApproximation period hPeriod
  tendsto_l2 := canonicalLatitudeSmoothInteriorApproximation_tendsto_l2
    period hPeriod

/-- Smooth interior seeds are dense in boundary `L²`. -/
theorem canonicalLatitudeSmoothInteriorSeedEmbedding_denseRange :
    DenseRange (canonicalLatitudeSmoothInteriorSeedEmbedding period) :=
  (canonicalLatitudeContinuousInteriorSeedApproximationData period hPeriod)
    |>.denseRange

/-- Both canonical boundary cores are dense unconditionally. -/
def canonicalLatitudeSmoothBoundaryCoreDensityData :
    CanonicalLatitudeSmoothBoundaryCoreDensityData period :=
  (canonicalLatitudeContinuousInteriorSeedApproximationData period hPeriod)
    |>.toBoundaryCoreDensityData hPeriod

/-- Final canonical boundary-density certificate. -/
theorem certificate :
    DenseRange (canonicalLatitudeSmoothInteriorSeedEmbedding period) ∧
      DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) :=
  (canonicalLatitudeContinuousInteriorSeedApproximationData period hPeriod)
    |>.certificate hPeriod

end
end P0EFTJanusMappingTorusCanonicalLatitudeInteriorSeedApproximation4D
end JanusFormal
