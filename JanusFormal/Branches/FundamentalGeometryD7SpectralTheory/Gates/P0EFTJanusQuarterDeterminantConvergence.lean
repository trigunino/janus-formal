import Mathlib.Analysis.SpecificLimits.Normed
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusRenormalizedSpectralDeterminant

namespace JanusFormal
namespace P0EFTJanusQuarterDeterminantConvergence

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusRenormalizedSpectralDeterminant
open P0EFTJanusFullHolonomyDeterminant
open P0EFTJanusNormalPinLiftBoundaryConditions

noncomputable section

def sphereMassAngle (data : ProductThroatSpectralData) (level : ℕ) : ℝ :=
  data.circlePeriod * Real.sqrt (sphereEigenvalueSquared data level)

def quarterLocalTerm (data : ProductThroatSpectralData) (level : ℕ) : ℝ :=
  (sphereMultiplicity data level : ℝ) *
    (sphereMassAngle data level - Real.log 2)

def quarterLocalCounterterm (data : ProductThroatSpectralData) (N : ℕ) : ℝ :=
  ∑ level ∈ Finset.range (N + 1), quarterLocalTerm data level

def quarterRemainderTerm (data : ProductThroatSpectralData) (level : ℕ) : ℝ :=
  (sphereMultiplicity data level : ℝ) *
    Real.log (1 + Real.exp (-2 * sphereMassAngle data level))

theorem quarter_mode_log_decomposition
    (data : ProductThroatSpectralData) (level : ℕ) :
    Real.log (sphereLevelKernel data (1 / 4) level) =
      sphereMassAngle data level - Real.log 2 +
        Real.log (1 + Real.exp (-2 * sphereMassAngle data level)) := by
  let x := sphereMassAngle data level
  have hAngle : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  have hFactor : Real.cosh x =
      (Real.exp x / 2) * (1 + Real.exp (-2 * x)) := by
    rw [Real.cosh_eq]
    have hNeg : Real.exp (-x) = Real.exp x * Real.exp (-2 * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hNeg]
    ring
  change Real.log (modeDeterminantKernel x (1 / 4)) = _
  rw [modeDeterminantKernel, hAngle, Real.cos_pi_div_two, sub_zero, hFactor]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_div (Real.exp_ne_zero x) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_exp]

theorem quarter_cutoff_subtraction_identity
    (data : ProductThroatSpectralData) (N : ℕ) :
    finiteCutoffLogDeterminant data N (1 / 4) -
        quarterLocalCounterterm data N =
      ∑ level ∈ Finset.range (N + 1), quarterRemainderTerm data level := by
  unfold finiteCutoffLogDeterminant cutoffSphereLevels quarterLocalCounterterm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro level _
  unfold quarterLocalTerm quarterRemainderTerm
  rw [quarter_mode_log_decomposition]
  ring

theorem sphere_mass_angle_linear_lower_bound
    (data : ProductThroatSpectralData) (level : ℕ) :
    (data.circlePeriod / data.sphereRadius) * ((level + 1 : ℕ) : ℝ) ≤
      sphereMassAngle data level := by
  have hRadius : 0 < data.sphereRadius := data.sphereRadiusPositive
  have hLevel : 0 ≤ ((level + 1 : ℕ) : ℝ) := by positivity
  have hSquare :
      (((level + 1 : ℕ) : ℝ) / data.sphereRadius) ^ 2 ≤
        sphereEigenvalueSquared data level := by
    unfold sphereEigenvalueSquared monopoleAbsCharge
    have hCharge : 0 ≤ ((data.monopoleCharge.natAbs : ℕ) : ℝ) := by positivity
    push_cast
    field_simp
    nlinarith
  have hSqrt :
      ((level + 1 : ℕ) : ℝ) / data.sphereRadius ≤
        Real.sqrt (sphereEigenvalueSquared data level) :=
    Real.le_sqrt_of_sq_le hSquare
  unfold sphereMassAngle
  have := mul_le_mul_of_nonneg_left hSqrt data.circlePeriodPositive.le
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this

theorem quarter_remainder_term_nonnegative
    (data : ProductThroatSpectralData) (level : ℕ) :
    0 ≤ quarterRemainderTerm data level := by
  unfold quarterRemainderTerm
  apply mul_nonneg (by positivity)
  exact Real.log_nonneg (by
    linarith [Real.exp_pos (-2 * sphereMassAngle data level)])

theorem quarter_remainder_term_le_exponential
    (data : ProductThroatSpectralData) (level : ℕ) :
    quarterRemainderTerm data level ≤
      (sphereMultiplicity data level : ℝ) *
        Real.exp
          (-2 * (data.circlePeriod / data.sphereRadius) *
            ((level + 1 : ℕ) : ℝ)) := by
  have hMass := sphere_mass_angle_linear_lower_bound data level
  have hExp :
      Real.exp (-2 * sphereMassAngle data level) ≤
        Real.exp
          (-2 * (data.circlePeriod / data.sphereRadius) *
            ((level + 1 : ℕ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hLog :
      Real.log (1 + Real.exp (-2 * sphereMassAngle data level)) ≤
        Real.exp (-2 * sphereMassAngle data level) := by
    have hPositive : 0 < 1 + Real.exp (-2 * sphereMassAngle data level) := by positivity
    exact (Real.log_le_sub_one_of_pos hPositive).trans_eq (by ring)
  unfold quarterRemainderTerm
  exact mul_le_mul_of_nonneg_left (hLog.trans hExp) (by positivity)

theorem quarter_remainder_summable (data : ProductThroatSpectralData) :
    Summable (quarterRemainderTerm data) := by
  let ratio : ℝ := Real.exp (-2 * (data.circlePeriod / data.sphereRadius))
  have hQuotient : 0 < data.circlePeriod / data.sphereRadius :=
    div_pos data.circlePeriodPositive data.sphereRadiusPositive
  have hExponent : -2 * (data.circlePeriod / data.sphereRadius) < 0 := by
    nlinarith
  have hRatioNonnegative : 0 ≤ ratio := Real.exp_nonneg _
  have hRatioLessThanOne : ratio < 1 := (Real.exp_lt_one_iff).2 hExponent
  have hGeom : Summable (fun n : ℕ => (n : ℝ) * ratio ^ n) := by
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hRatioNonnegative]))
  have hPure : Summable (fun n : ℕ => ratio ^ n) :=
    summable_geometric_of_lt_one hRatioNonnegative hRatioLessThanOne
  have hMajorant : Summable (fun level : ℕ =>
      (sphereMultiplicity data level : ℝ) * ratio ^ (level + 1)) := by
    unfold sphereMultiplicity monopoleAbsCharge
    simp_rw [pow_succ]
    push_cast
    ring_nf
    exact ((hPure.mul_left
      ((data.monopoleCharge.natAbs : ℝ) * ratio + 2 * ratio)).add
        (hGeom.mul_left (2 * ratio))).congr (by intro n; ring)
  refine hMajorant.of_nonneg_of_le (quarter_remainder_term_nonnegative data) ?_
  intro level
  refine (quarter_remainder_term_le_exponential data level).trans_eq ?_
  unfold ratio
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem quarter_cutoff_remainder_converges (data : ProductThroatSpectralData) :
    Filter.Tendsto
      (fun N => finiteCutoffLogDeterminant data N (1 / 4) -
        quarterLocalCounterterm data N)
      Filter.atTop (nhds (∑' level, quarterRemainderTerm data level)) := by
  have hPartial := (quarter_remainder_summable data).hasSum.tendsto_sum_nat
  have hShifted := hPartial.comp (Filter.tendsto_add_atTop_nat 1)
  exact hShifted.congr'
    (Filter.Eventually.of_forall fun N =>
      (quarter_cutoff_subtraction_identity data N).symm)

def rootHolonomy : NormalRootChoice → ℝ
  | .positiveQuarter => 1 / 4
  | .negativeQuarter => 3 / 4

theorem root_holonomy_cosine_vanishes (choice : NormalRootChoice) :
    Real.cos (2 * Real.pi * rootHolonomy choice) = 0 := by
  cases choice with
  | positiveQuarter =>
      change Real.cos (2 * Real.pi * (1 / 4 : ℝ)) = 0
      convert Real.cos_pi_div_two using 2
      ring
  | negativeQuarter =>
      change Real.cos (2 * Real.pi * (3 / 4 : ℝ)) = 0
      rw [show 2 * Real.pi * (3 / 4 : ℝ) = Real.pi + Real.pi / 2 by ring,
        Real.cos_add, Real.cos_pi, Real.cos_pi_div_two,
        Real.sin_pi, Real.sin_pi_div_two]
      ring

theorem finite_cutoff_root_eq_quarter (data : ProductThroatSpectralData)
    (choice : NormalRootChoice) (N : ℕ) :
    finiteCutoffLogDeterminant data N (rootHolonomy choice) =
      finiteCutoffLogDeterminant data N (1 / 4) := by
  unfold finiteCutoffLogDeterminant
  apply Finset.sum_congr rfl
  intro level _
  congr 2
  unfold sphereLevelKernel modeDeterminantKernel
  rw [root_holonomy_cosine_vanishes]
  have hQuarter : Real.cos (2 * Real.pi * (1 / 4 : ℝ)) = 0 := by
    convert Real.cos_pi_div_two using 2
    ring
  rw [hQuarter]

structure Z4RenormalizedDeterminantCertificate
    (data : ProductThroatSpectralData) where
  localCounterterm : ℕ → ℝ
  renormalizedLog : NormalRootChoice → ℝ
  cutoffConverges : ∀ choice : NormalRootChoice,
    Filter.Tendsto
      (fun N => finiteCutoffLogDeterminant data N (rootHolonomy choice) -
        localCounterterm N)
      Filter.atTop (nhds (renormalizedLog choice))

noncomputable def z4RenormalizedDeterminant
    (data : ProductThroatSpectralData) :
    Z4RenormalizedDeterminantCertificate data where
  localCounterterm := quarterLocalCounterterm data
  renormalizedLog := fun _ => ∑' level, quarterRemainderTerm data level
  cutoffConverges := fun choice =>
    (quarter_cutoff_remainder_converges data).congr'
      (Filter.Eventually.of_forall fun N => by
        change finiteCutoffLogDeterminant data N (1 / 4) -
            quarterLocalCounterterm data N =
          finiteCutoffLogDeterminant data N (rootHolonomy choice) -
            quarterLocalCounterterm data N
        rw [finite_cutoff_root_eq_quarter data choice N])

end

end P0EFTJanusQuarterDeterminantConvergence
end JanusFormal
