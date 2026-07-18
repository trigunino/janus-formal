import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusEulerMaclaurinOrderFour
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusMonopoleSphereHeatTrace
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusProductThroatDiracHeatCoefficients

namespace JanusFormal
namespace P0EFTJanusMonopoleHeatAsymptoticMatch

set_option autoImplicit false

open Filter Set Asymptotics MeasureTheory
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusProductThroatLocalInvariants
open P0EFTJanusProductThroatDiracHeatCoefficients
open P0EFTJanusUniversalClosedHeatCoefficients
open P0EFTJanusDiracSeeleyDeWittCandidate
open P0EFTJanusEulerMaclaurinOrderFour

noncomputable section

def dimensionlessFullSphereHeatTrace
    (data : ProductThroatSpectralData) (u : ℝ) : ℝ :=
  (monopoleAbsCharge data : ℝ) +
    2 * sphereHeatTrace data (u * data.sphereRadius ^ 2)

/-- Euler--Maclaurin boundary jets for `(2x+q) exp(-u x(x+q))`. -/
def emFirstJet (q u : ℝ) : ℝ := 2 - q ^ 2 * u

def emThirdJet (q u : ℝ) : ℝ :=
  -12 * u + 12 * q ^ 2 * u ^ 2 - q ^ 4 * u ^ 3

def eulerMaclaurinApproximation (q u : ℝ) : ℝ :=
  q + 2 * (1 / u - q / 2 - emFirstJet q u / 12 +
    emThirdJet q u / 720)

def predictedSphereHeatExpansion (q u : ℝ) : ℝ :=
  2 / u - 1 / 3 + (5 * q ^ 2 - 1) * u / 30

def emShift (q x : ℝ) : ℝ := x + q / 2

def emGaussian (q u x : ℝ) : ℝ :=
  Real.exp (u * q ^ 2 / 4) * Real.exp (-u * emShift q x ^ 2)

def emSummand (q u x : ℝ) : ℝ :=
  2 * emShift q x * emGaussian q u x

def emSummandD1 (q u x : ℝ) : ℝ :=
  2 * (1 - 2 * u * emShift q x ^ 2) * emGaussian q u x

def emSummandD2 (q u x : ℝ) : ℝ :=
  2 * (-6 * u * emShift q x + 4 * u ^ 2 * emShift q x ^ 3) * emGaussian q u x

def emSummandD3 (q u x : ℝ) : ℝ :=
  2 * (-6 * u + 24 * u ^ 2 * emShift q x ^ 2 -
    8 * u ^ 3 * emShift q x ^ 4) * emGaussian q u x

def emSummandD4 (q u x : ℝ) : ℝ :=
  2 * (60 * u ^ 2 * emShift q x - 80 * u ^ 3 * emShift q x ^ 3 +
    16 * u ^ 4 * emShift q x ^ 5) * emGaussian q u x

def emSummandD5 (q u x : ℝ) : ℝ :=
  2 * (60 * u ^ 2 - 360 * u ^ 3 * emShift q x ^ 2 +
    240 * u ^ 4 * emShift q x ^ 4 - 32 * u ^ 5 * emShift q x ^ 6) *
      emGaussian q u x

theorem hasDerivAt_emShift (q x : ℝ) : HasDerivAt (emShift q) 1 x := by
  unfold emShift
  convert (hasDerivAt_id x).add_const (q / 2) using 1
  all_goals rfl

theorem hasDerivAt_emGaussian (q u x : ℝ) :
    HasDerivAt (emGaussian q u)
      (-2 * u * emShift q x * emGaussian q u x) x := by
  have hz := hasDerivAt_emShift q x
  unfold emGaussian
  convert (hasDerivAt_const x (Real.exp (u * q ^ 2 / 4))).mul
    (((hz.pow 2).const_mul (-u)).exp) using 1
  all_goals first | rfl |
    (simp only [emShift, Pi.pow_apply]; ring)

theorem hasDerivAt_emSummand (q u x : ℝ) :
    HasDerivAt (emSummand q u) (emSummandD1 q u x) x := by
  have hz := hasDerivAt_emShift q x
  unfold emSummand emSummandD1
  convert (hz.const_mul 2).mul (hasDerivAt_emGaussian q u x) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_emSummandD1 (q u x : ℝ) :
    HasDerivAt (emSummandD1 q u) (emSummandD2 q u x) x := by
  have hz := hasDerivAt_emShift q x
  have hp : HasDerivAt
      (fun y => 2 * (1 - 2 * u * emShift q y ^ 2))
      (-8 * u * emShift q x) x := by
    convert (hasDerivAt_const x 2).mul
      ((hasDerivAt_const x 1).sub
        ((hasDerivAt_const x (2 * u)).mul (hz.pow 2))) using 1
    all_goals first | rfl | ring
  unfold emSummandD1 emSummandD2
  convert hp.mul (hasDerivAt_emGaussian q u x) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_emSummandD2 (q u x : ℝ) :
    HasDerivAt (emSummandD2 q u) (emSummandD3 q u x) x := by
  have hz := hasDerivAt_emShift q x
  have hp : HasDerivAt
      (fun y => 2 * (-6 * u * emShift q y + 4 * u ^ 2 * emShift q y ^ 3))
      (2 * (-6 * u + 12 * u ^ 2 * emShift q x ^ 2)) x := by
    convert (((hz.const_mul (-6 * u)).add
      ((hz.pow 3).const_mul (4 * u ^ 2))).const_mul 2) using 1
    all_goals first | rfl | ring
  unfold emSummandD2 emSummandD3
  convert hp.mul (hasDerivAt_emGaussian q u x) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_emSummandD3 (q u x : ℝ) :
    HasDerivAt (emSummandD3 q u) (emSummandD4 q u x) x := by
  have hz := hasDerivAt_emShift q x
  have hp : HasDerivAt
      (fun y => 2 * (-6 * u + 24 * u ^ 2 * emShift q y ^ 2 -
        8 * u ^ 3 * emShift q y ^ 4))
      (2 * (48 * u ^ 2 * emShift q x - 32 * u ^ 3 * emShift q x ^ 3)) x := by
    convert ((((hasDerivAt_const x (-6 * u)).add
      ((hz.pow 2).const_mul (24 * u ^ 2))).sub
        ((hz.pow 4).const_mul (8 * u ^ 3))).const_mul 2) using 1
    all_goals first | rfl | ring
  unfold emSummandD3 emSummandD4
  convert hp.mul (hasDerivAt_emGaussian q u x) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_emSummandD4 (q u x : ℝ) :
    HasDerivAt (emSummandD4 q u) (emSummandD5 q u x) x := by
  have hz := hasDerivAt_emShift q x
  have hp : HasDerivAt
      (fun y => 2 * (60 * u ^ 2 * emShift q y - 80 * u ^ 3 * emShift q y ^ 3 +
        16 * u ^ 4 * emShift q y ^ 5))
      (2 * (60 * u ^ 2 - 240 * u ^ 3 * emShift q x ^ 2 +
        80 * u ^ 4 * emShift q x ^ 4)) x := by
    convert ((((hz.const_mul (60 * u ^ 2)).sub
      ((hz.pow 3).const_mul (80 * u ^ 3))).add
        ((hz.pow 5).const_mul (16 * u ^ 4))).const_mul 2) using 1
    all_goals first | rfl | ring
  unfold emSummandD4 emSummandD5
  convert hp.mul (hasDerivAt_emGaussian q u x) using 1
  all_goals first | rfl | ring

def emFifthProfile (y : ℝ) : ℝ :=
  2 * (60 - 360 * y ^ 2 + 240 * y ^ 4 - 32 * y ^ 6) * Real.exp (-y ^ 2)

def emFifthProfileL1 : ℝ := ∫ y : ℝ, |emFifthProfile y|

theorem emFifthProfile_integrable : Integrable (fun y : ℝ => |emFifthProfile y|) := by
  have hpow (n : ℕ) : Integrable (fun y : ℝ => y ^ n * Real.exp (-y ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
        (s := (n : ℝ)) (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith))
  have hpoly : Integrable (fun y : ℝ => emFifthProfile y) := by
    have h := (((hpow 0).const_mul 120).sub ((hpow 2).const_mul 720)).add
      ((hpow 4).const_mul 480) |>.sub ((hpow 6).const_mul 64)
    refine h.congr ?_
    filter_upwards [] with y
    change 120 * (y ^ 0 * Real.exp (-y ^ 2)) -
      720 * (y ^ 2 * Real.exp (-y ^ 2)) +
      480 * (y ^ 4 * Real.exp (-y ^ 2)) -
      64 * (y ^ 6 * Real.exp (-y ^ 2)) = emFifthProfile y
    unfold emFifthProfile
    ring
  exact hpoly.abs

theorem emFifthProfileL1_nonnegative : 0 ≤ emFifthProfileL1 := by
  unfold emFifthProfileL1
  exact integral_nonneg fun _ => abs_nonneg _

theorem emSummandD5_eq_scaled_profile (q u x : ℝ) (hu : 0 < u) :
    emSummandD5 q u x = Real.exp (u * q ^ 2 / 4) * u ^ 2 *
      emFifthProfile (Real.sqrt u * emShift q x) := by
  have hsqrt : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hsqrt4 : Real.sqrt u ^ 4 = u ^ 2 := by
    calc
      Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 := by ring
      _ = u ^ 2 := by rw [hsqrt]
  have hsqrt6 : Real.sqrt u ^ 6 = u ^ 3 := by
    calc
      Real.sqrt u ^ 6 = (Real.sqrt u ^ 2) ^ 3 := by ring
      _ = u ^ 3 := by rw [hsqrt]
  unfold emSummandD5 emGaussian emFifthProfile
  simp only [mul_pow, hsqrt, hsqrt4, hsqrt6]
  ring_nf

theorem emSummandD5_abs_integrable (q u : ℝ) (hu : 0 < u) :
    Integrable (fun x : ℝ => |emSummandD5 q u x|) := by
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hcomp : Integrable (fun x : ℝ =>
      |emFifthProfile (Real.sqrt u * emShift q x)|) := by
    have hscaled := emFifthProfile_integrable.comp_mul_left' hsqrt.ne'
    simpa [emShift, mul_add] using hscaled.comp_add_right (q / 2)
  have hscalar : 0 ≤ Real.exp (u * q ^ 2 / 4) * u ^ 2 := by positivity
  refine (hcomp.const_mul (Real.exp (u * q ^ 2 / 4) * u ^ 2)).congr ?_
  filter_upwards [] with x
  rw [emSummandD5_eq_scaled_profile q u x hu, abs_mul, abs_of_nonneg hscalar]

theorem integral_abs_emSummandD5 (q u : ℝ) (hu : 0 < u) :
    (∫ x : ℝ, |emSummandD5 q u x|) =
      Real.exp (u * q ^ 2 / 4) * u * Real.sqrt u * emFifthProfileL1 := by
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsqrtSq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have htranslate := integral_add_right_eq_self
    (μ := volume) (fun x : ℝ => |emFifthProfile (Real.sqrt u * x)|) (q / 2)
  have hscale := Measure.integral_comp_mul_left
    (fun y : ℝ => |emFifthProfile y|) (Real.sqrt u)
  have hprofile : (∫ x : ℝ, |emFifthProfile (Real.sqrt u * emShift q x)|) =
      (Real.sqrt u)⁻¹ * emFifthProfileL1 := by
    calc
      _ = ∫ x : ℝ, |emFifthProfile (Real.sqrt u * x)| := by
        simpa [emShift, mul_add] using htranslate
      _ = |(Real.sqrt u)⁻¹| * emFifthProfileL1 := by
        simpa [emFifthProfileL1, smul_eq_mul] using hscale
      _ = (Real.sqrt u)⁻¹ * emFifthProfileL1 := by
        rw [abs_of_pos (inv_pos.2 hsqrt)]
  have hscalar : 0 ≤ Real.exp (u * q ^ 2 / 4) * u ^ 2 := by positivity
  have habs (x : ℝ) : |emSummandD5 q u x| =
      (Real.exp (u * q ^ 2 / 4) * u ^ 2) *
        |emFifthProfile (Real.sqrt u * emShift q x)| := by
    rw [emSummandD5_eq_scaled_profile q u x hu, abs_mul, abs_of_nonneg hscalar]
  simp_rw [habs]
  rw [integral_const_mul, hprofile]
  field_simp [hsqrt.ne']
  rw [hsqrtSq]

theorem emSummandD5_interval_bound (q u : ℝ) (hu : 0 < u) (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ), |emSummandD5 q u x|) ≤
      Real.exp (u * q ^ 2 / 4) * u * Real.sqrt u * emFifthProfileL1 := by
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
  calc
    (∫ x in Ioc (0 : ℝ) (N : ℝ), |emSummandD5 q u x|) ≤
        ∫ x : ℝ, |emSummandD5 q u x| :=
      setIntegral_le_integral (emSummandD5_abs_integrable q u hu)
        (Eventually.of_forall fun _ => abs_nonneg _)
    _ = _ := integral_abs_emSummandD5 q u hu

theorem emGaussian_eq_unshifted (q u x : ℝ) :
    emGaussian q u x = Real.exp (-u * x * (x + q)) := by
  unfold emGaussian emShift
  rw [← Real.exp_add]
  congr 1
  ring

theorem emSummand_eq_unshifted (q u x : ℝ) :
    emSummand q u x = (2 * x + q) * Real.exp (-u * x * (x + q)) := by
  unfold emSummand emShift
  rw [emGaussian_eq_unshifted]
  ring

@[simp] theorem emGaussian_zero (q u : ℝ) : emGaussian q u 0 = 1 := by
  rw [emGaussian_eq_unshifted]
  simp

@[simp] theorem emSummand_zero (q u : ℝ) : emSummand q u 0 = q := by
  rw [emSummand_eq_unshifted]
  simp

@[simp] theorem emSummandD1_zero (q u : ℝ) : emSummandD1 q u 0 = emFirstJet q u := by
  unfold emSummandD1 emFirstJet emShift
  rw [emGaussian_zero]
  ring

@[simp] theorem emSummandD3_zero (q u : ℝ) : emSummandD3 q u 0 = emThirdJet q u := by
  unfold emSummandD3 emThirdJet emShift
  rw [emGaussian_zero]
  ring

theorem sphereHeatTerm_eq_emSummand (data : ProductThroatSpectralData) (u : ℝ)
    (level : ℕ) :
    sphereHeatTerm data (u * data.sphereRadius ^ 2) level =
      emSummand (monopoleAbsCharge data : ℝ) u ((level + 1 : ℕ) : ℝ) := by
  unfold sphereHeatTerm sphereMultiplicity sphereEigenvalueSquared
  rw [emSummand_eq_unshifted]
  have hRadius : data.sphereRadius ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos data.sphereRadiusPositive)
  congr 1
  · push_cast
    ring
  · congr 1
    field_simp [hRadius]
    push_cast
    field_simp [ne_of_gt data.sphereRadiusPositive]

theorem emSummand_summable (data : ProductThroatSpectralData) (u : ℝ) (hu : 0 < u) :
    Summable (fun n : ℕ => emSummand (monopoleAbsCharge data : ℝ) u (n : ℝ)) := by
  have htime : 0 < u * data.sphereRadius ^ 2 :=
    mul_pos hu (sq_pos_of_pos data.sphereRadiusPositive)
  have htail : Summable (fun level : ℕ =>
      emSummand (monopoleAbsCharge data : ℝ) u ((level + 1 : ℕ) : ℝ)) :=
    (sphere_heat_trace_summable data _ htime).congr
      (fun level => sphereHeatTerm_eq_emSummand data u level)
  exact (summable_nat_add_iff 1).1 (by simpa [Nat.cast_add] using htail)

theorem dimensionlessFullSphereHeatTrace_eq_tsum
    (data : ProductThroatSpectralData) (u : ℝ) (hu : 0 < u) :
    dimensionlessFullSphereHeatTrace data u =
      2 * (∑' n : ℕ, emSummand (monopoleAbsCharge data : ℝ) u (n : ℝ)) -
        (monopoleAbsCharge data : ℝ) := by
  have hsum := emSummand_summable data u hu
  have htail : sphereHeatTrace data (u * data.sphereRadius ^ 2) =
      ∑' level : ℕ,
        emSummand (monopoleAbsCharge data : ℝ) u ((level + 1 : ℕ) : ℝ) := by
    unfold sphereHeatTrace
    apply tsum_congr
    exact sphereHeatTerm_eq_emSummand data u
  have hsplit := hsum.tsum_eq_zero_add
  unfold dimensionlessFullSphereHeatTrace
  rw [htail]
  norm_num [emSummand_zero] at hsplit
  simp only [Nat.cast_add, Nat.cast_one] at hsplit ⊢
  rw [hsplit]
  ring

theorem emShift_pow_mul_emGaussian_tendsto_zero
    (q u : ℝ) (hq : 0 ≤ q) (hu : 0 < u) (k : ℕ) :
    Tendsto (fun N : ℕ => emShift q (N : ℝ) ^ k * emGaussian q u (N : ℝ))
      atTop (nhds 0) := by
  have hdecay := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hu (k : ℝ)
  rw [cocompact_eq_atBot_atTop] at hdecay
  have hdecayTop : Tendsto
      (fun x : ℝ => |x| ^ (k : ℝ) * Real.exp (-u * x ^ 2)) atTop (nhds 0) :=
    hdecay.mono_left le_sup_right
  have hshift : Tendsto (fun N : ℕ => emShift q (N : ℝ)) atTop atTop := by
    unfold emShift
    exact tendsto_atTop_add_const_right atTop (q / 2) tendsto_natCast_atTop_atTop
  have h := (hdecayTop.comp hshift).const_mul (Real.exp (u * q ^ 2 / 4))
  convert h using 1
  · funext N
    have hz : 0 ≤ emShift q (N : ℝ) := by
      unfold emShift
      positivity
    simp only [Function.comp_apply]
    rw [Real.rpow_natCast, abs_of_nonneg hz]
    unfold emGaussian
    ring
  · simp

theorem emSummand_tendsto_zero (q u : ℝ) (hq : 0 ≤ q) (hu : 0 < u) :
    Tendsto (fun N : ℕ => emSummand q u (N : ℝ)) atTop (nhds 0) := by
  have h := (emShift_pow_mul_emGaussian_tendsto_zero q u hq hu 1).const_mul 2
  convert h using 1
  · funext N
    simp [emSummand]
    ring
  · simp

theorem emSummandD1_tendsto_zero (q u : ℝ) (hq : 0 ≤ q) (hu : 0 < u) :
    Tendsto (fun N : ℕ => emSummandD1 q u (N : ℝ)) atTop (nhds 0) := by
  have h0 := (emShift_pow_mul_emGaussian_tendsto_zero q u hq hu 0).const_mul 2
  have h2 := (emShift_pow_mul_emGaussian_tendsto_zero q u hq hu 2).const_mul (-4 * u)
  have h := h0.add h2
  convert h using 1
  · funext N
    simp [emSummandD1]
    ring
  · simp

theorem emSummandD3_tendsto_zero (q u : ℝ) (hq : 0 ≤ q) (hu : 0 < u) :
    Tendsto (fun N : ℕ => emSummandD3 q u (N : ℝ)) atTop (nhds 0) := by
  have h0 := (emShift_pow_mul_emGaussian_tendsto_zero q u hq hu 0).const_mul (-12 * u)
  have h2 := (emShift_pow_mul_emGaussian_tendsto_zero q u hq hu 2).const_mul (48 * u ^ 2)
  have h4 := (emShift_pow_mul_emGaussian_tendsto_zero q u hq hu 4).const_mul (-16 * u ^ 3)
  have h := (h0.add h2).add h4
  convert h using 1
  · funext N
    simp [emSummandD3]
    ring
  · simp

def emPrimitive (q u x : ℝ) : ℝ := -Real.exp (-u * (x * (x + q))) / u

theorem hasDerivAt_emPrimitive (q u x : ℝ) (hu : 0 < u) :
    HasDerivAt (emPrimitive q u) (emSummand q u x) x := by
  unfold emPrimitive
  rw [emSummand_eq_unshifted]
  convert
    (((((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const q)).const_mul (-u)).exp).neg.div_const u)
      using 1
  all_goals first
    | rfl
    | (simp [Function.id_def, div_eq_mul_inv]; field_simp [hu.ne']; ring_nf)

theorem emSummand_interval_integral (q u : ℝ) (hu : 0 < u) (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ), emSummand q u x) =
      (1 - Real.exp (-u * (N : ℝ) * ((N : ℝ) + q))) / u := by
  have hcont : Continuous (emSummand q u) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_emSummand q u x).continuousAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (N : ℝ)) (f := emPrimitive q u) (f' := emSummand q u)
    (fun x hx => hasDerivAt_emPrimitive q u x hu)
    (hcont.intervalIntegrable (0 : ℝ) (N : ℝ))
  rw [hFTC]
  simp [emPrimitive]
  field_simp [hu.ne']
  ring

theorem emSummand_interval_integral_tendsto (q u : ℝ) (hq : 0 ≤ q) (hu : 0 < u) :
    Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ), emSummand q u x)
      atTop (nhds (1 / u)) := by
  have hgauss := emShift_pow_mul_emGaussian_tendsto_zero q u hq hu 0
  have hexp : Tendsto
      (fun N : ℕ => Real.exp (-u * (N : ℝ) * ((N : ℝ) + q))) atTop (nhds 0) := by
    simpa only [pow_zero, one_mul, emGaussian_eq_unshifted] using hgauss
  have h := (hexp.const_sub 1).div_const u
  convert h using 1
  · funext N
    rw [emSummand_interval_integral q u hu N]
  · simp

theorem euler_maclaurin_approximation_expands
    (q u : ℝ) :
    eulerMaclaurinApproximation q u =
      predictedSphereHeatExpansion q u +
        q ^ 2 * u ^ 2 / 30 - q ^ 4 * u ^ 3 / 360 := by
  unfold eulerMaclaurinApproximation predictedSphereHeatExpansion
    emFirstJet emThirdJet
  ring

theorem emSummand_euler_maclaurin_bound
    (data : ProductThroatSpectralData) (u : ℝ) (hu : 0 < u) :
    |∑' n : ℕ, emSummand (monopoleAbsCharge data : ℝ) u (n : ℝ) -
        (monopoleAbsCharge data : ℝ) / 2 - 1 / u +
        emFirstJet (monopoleAbsCharge data : ℝ) u / 12 -
        emThirdJet (monopoleAbsCharge data : ℝ) u / 720| ≤
      Real.exp (u * (monopoleAbsCharge data : ℝ) ^ 2 / 4) * u * Real.sqrt u *
        emFifthProfileL1 := by
  let q : ℝ := monopoleAbsCharge data
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have h := euler_maclaurin_tsum_error_bound
    (emSummand q u) (emSummandD1 q u) (emSummandD2 q u)
    (emSummandD3 q u) (emSummandD4 q u) (emSummandD5 q u)
    (1 / u) (Real.exp (u * q ^ 2 / 4) * u * Real.sqrt u * emFifthProfileL1)
    (hasDerivAt_emSummand q u) (hasDerivAt_emSummandD1 q u)
    (hasDerivAt_emSummandD2 q u) (hasDerivAt_emSummandD3 q u)
    (hasDerivAt_emSummandD4 q u)
    (by unfold emSummandD5 emGaussian emShift; fun_prop)
    (emSummand_summable data u hu)
    (emSummand_interval_integral_tendsto q u hq hu)
    (emSummand_tendsto_zero q u hq hu)
    (emSummandD1_tendsto_zero q u hq hu)
    (emSummandD3_tendsto_zero q u hq hu)
    (emSummandD5_interval_bound q u hu)
  simpa [q] using h

def EulerMaclaurinRemainderControlled
    (data : ProductThroatSpectralData) : Prop :=
  Tendsto
    (fun u => (dimensionlessFullSphereHeatTrace data u -
      eulerMaclaurinApproximation (monopoleAbsCharge data : ℝ) u) / u)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)

theorem dimensionless_trace_euler_maclaurin_bound
    (data : ProductThroatSpectralData) (u : ℝ) (hu : 0 < u) :
    |dimensionlessFullSphereHeatTrace data u -
        eulerMaclaurinApproximation (monopoleAbsCharge data : ℝ) u| ≤
      2 * (Real.exp (u * (monopoleAbsCharge data : ℝ) ^ 2 / 4) * u *
        Real.sqrt u * emFifthProfileL1) := by
  let q : ℝ := monopoleAbsCharge data
  have hBound := emSummand_euler_maclaurin_bound data u hu
  have hTrace := dimensionlessFullSphereHeatTrace_eq_tsum data u hu
  have hEq :
      dimensionlessFullSphereHeatTrace data u - eulerMaclaurinApproximation q u =
        2 * ((∑' n : ℕ, emSummand q u (n : ℝ)) - q / 2 - 1 / u +
          emFirstJet q u / 12 - emThirdJet q u / 720) := by
    rw [hTrace]
    unfold eulerMaclaurinApproximation
    ring
  calc
    |dimensionlessFullSphereHeatTrace data u - eulerMaclaurinApproximation q u| =
        2 * |(∑' n : ℕ, emSummand q u (n : ℝ)) - q / 2 - 1 / u +
          emFirstJet q u / 12 - emThirdJet q u / 720| := by
            rw [hEq, abs_mul]
            norm_num
    _ ≤ 2 * (Real.exp (u * q ^ 2 / 4) * u * Real.sqrt u * emFifthProfileL1) :=
      mul_le_mul_of_nonneg_left (by simpa [q] using hBound) (by norm_num)

theorem euler_maclaurin_majorant_tendsto_zero
    (data : ProductThroatSpectralData) :
    Tendsto
      (fun u : ℝ => 2 * Real.exp (u * (monopoleAbsCharge data : ℝ) ^ 2 / 4) *
        Real.sqrt u * emFifthProfileL1)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hContinuous : ContinuousAt
      (fun u : ℝ => 2 * Real.exp (u * (monopoleAbsCharge data : ℝ) ^ 2 / 4) *
        Real.sqrt u * emFifthProfileL1) 0 := by
    fun_prop
  change Tendsto
    (fun u : ℝ => 2 * Real.exp (u * (monopoleAbsCharge data : ℝ) ^ 2 / 4) *
      Real.sqrt u * emFifthProfileL1)
    (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 0)
  simpa using hContinuous.tendsto.mono_left inf_le_left

theorem euler_maclaurin_remainder_controlled
    (data : ProductThroatSpectralData) : EulerMaclaurinRemainderControlled data := by
  unfold EulerMaclaurinRemainderControlled
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun u => abs_nonneg _) ?_
    (euler_maclaurin_majorant_tendsto_zero data)
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := ne_of_gt hu
  simp only [Function.comp_apply]
  rw [abs_div, show |u| = u from abs_of_pos hu]
  calc
    |dimensionlessFullSphereHeatTrace data u -
        eulerMaclaurinApproximation (monopoleAbsCharge data : ℝ) u| / u ≤
      (2 * (Real.exp (u * (monopoleAbsCharge data : ℝ) ^ 2 / 4) * u *
        Real.sqrt u * emFifthProfileL1)) / u :=
          (div_le_div_iff_of_pos_right hu).2
            (dimensionless_trace_euler_maclaurin_bound data u hu)
    _ = 2 * Real.exp (u * (monopoleAbsCharge data : ℝ) ^ 2 / 4) *
        Real.sqrt u * emFifthProfileL1 := by
          field_simp [hu0]

def SmallTimeSphereHeatCoefficientsMatched
    (data : ProductThroatSpectralData) : Prop :=
  Tendsto
    (fun u => (dimensionlessFullSphereHeatTrace data u -
      predictedSphereHeatExpansion (monopoleAbsCharge data : ℝ) u) / u)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)

theorem polynomial_tail_ratio_tends_to_zero (q : ℝ) :
    Tendsto (fun u : ℝ => q ^ 2 * u / 30 - q ^ 4 * u ^ 2 / 360)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hContinuous : ContinuousAt
      (fun u : ℝ => q ^ 2 * u / 30 - q ^ 4 * u ^ 2 / 360) 0 := by
    fun_prop
  change Tendsto (fun u : ℝ => q ^ 2 * u / 30 - q ^ 4 * u ^ 2 / 360)
    (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 0)
  simpa using hContinuous.tendsto.mono_left inf_le_left

theorem small_time_coefficients_match_of_euler_maclaurin_control
    (data : ProductThroatSpectralData)
    (hControl : EulerMaclaurinRemainderControlled data) :
    SmallTimeSphereHeatCoefficientsMatched data := by
  unfold EulerMaclaurinRemainderControlled at hControl
  unfold SmallTimeSphereHeatCoefficientsMatched
  have hTail := polynomial_tail_ratio_tends_to_zero
    (monopoleAbsCharge data : ℝ)
  have hSum : Tendsto
      (fun u =>
        (dimensionlessFullSphereHeatTrace data u -
          eulerMaclaurinApproximation (monopoleAbsCharge data : ℝ) u) / u +
        ((monopoleAbsCharge data : ℝ) ^ 2 * u / 30 -
          (monopoleAbsCharge data : ℝ) ^ 4 * u ^ 2 / 360))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hControl.add hTail
  refine hSum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have huNonzero : u ≠ 0 := ne_of_gt hu
  rw [euler_maclaurin_approximation_expands]
  field_simp
  ring

/-- The sphere heat coefficients follow unconditionally from the proved
order-four Euler--Maclaurin remainder estimate. -/
theorem small_time_coefficients_match
    (data : ProductThroatSpectralData) :
    SmallTimeSphereHeatCoefficientsMatched data :=
  small_time_coefficients_match_of_euler_maclaurin_control data
    (euler_maclaurin_remainder_controlled data)

def spectralSphereLeadingCoefficient : ℝ := 2

def spectralSphereConstantCoefficient : ℝ := -(1 / 3)

def spectralSphereLinearCoefficient (monopoleNumber : ℤ) : ℝ :=
  (5 * (monopoleNumber : ℝ) ^ 2 - 1) / 30

def spectralProductA0 (data : ProductThroatInvariantData) : ℝ :=
  4 * data.piConstant * spectralSphereLeadingCoefficient *
    data.geometricLength ^ 3 * data.circleModulus

def spectralProductA2 (data : ProductThroatInvariantData) : ℝ :=
  4 * data.piConstant * spectralSphereConstantCoefficient *
    data.geometricLength * data.circleModulus

def spectralProductA4 (data : ProductThroatInvariantData) : ℝ :=
  4 * data.piConstant * spectralSphereLinearCoefficient data.monopoleNumber *
    data.circleModulus / data.geometricLength

theorem spectral_product_coefficients_match_universal
    (data : ProductThroatInvariantData) :
    spectralProductA0 data =
      reducedA0 (rankTwoDiracAsLaplaceData (productThroatDiracTraceData data)) ∧
    spectralProductA2 data =
      reducedA2 (rankTwoDiracAsLaplaceData (productThroatDiracTraceData data)) ∧
    spectralProductA4 data =
      reducedA4 (rankTwoDiracAsLaplaceData (productThroatDiracTraceData data)) := by
  rw [universal_product_throat_a0_formula,
    universal_product_throat_a2_formula,
    universal_product_throat_a4_formula]
  unfold spectralProductA0 spectralProductA2 spectralProductA4
    spectralSphereLeadingCoefficient spectralSphereConstantCoefficient
    spectralSphereLinearCoefficient
  constructor
  · ring
  · constructor <;> ring

end

end P0EFTJanusMonopoleHeatAsymptoticMatch
end JanusFormal
