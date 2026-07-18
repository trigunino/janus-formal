import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D

/-!
# Positive power-law classification at a diagonal zero-over-zero face

For positive natural exponents `m` and `n`, this gate replaces one numerator
coordinate by `t ^ m` and the matching denominator coordinate by `t ^ n`.
All such paths stay in the positive diagonal domain for `t > 0` and reach the
same simultaneous zero-over-zero boundary.  Their selected principal-root
coordinate is classified by comparing `m` and `n`.

This is only a classification of this explicit diagonal monomial family.  It
does not classify arbitrary nonlinear matrix paths or Jordan degenerations.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D
open P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D

abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.Coefficients4
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.CoefficientPair

/-- At coordinate `i`, the denominator magnitude is `t ^ n` and the
numerator magnitude is `t ^ m`; all other coordinates remain fixed. -/
def powerLawZeroOverZeroPath
    (point : CoefficientPair) (i : Fin 4)
    (m n : Nat) (t : Real) : CoefficientPair :=
  (replaceMagnitude point.1 i (t ^ n),
    replaceMagnitude point.2 i (t ^ m))

/-- Every positive parameter lies in the original positive diagonal domain.
-/
theorem powerLawZeroOverZeroPath_mem_globalDomain
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) (m n : Nat) {t : Real} (ht : 0 < t) :
    powerLawZeroOverZeroPath point i m n t ∈
      globalDiagonalLorentzDomain := by
  constructor <;> intro j
  · by_cases hji : j = i
    · subst j
      simpa [powerLawZeroOverZeroPath, replaceMagnitude] using pow_pos ht n
    · simpa [powerLawZeroOverZeroPath, replaceMagnitude, hji] using
        hPoint.1 j
  · by_cases hji : j = i
    · subst j
      simpa [powerLawZeroOverZeroPath, replaceMagnitude] using pow_pos ht m
    · simpa [powerLawZeroOverZeroPath, replaceMagnitude, hji] using
        hPoint.2 j

/-- Positive exponents make the endpoint the same simultaneous zero-over-zero
boundary used by the two-path witness. -/
@[simp] theorem powerLawZeroOverZeroPath_zero
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) :
    powerLawZeroOverZeroPath point i m n 0 =
      equalRateZeroOverZeroPath point i 0 := by
  simp [powerLawZeroOverZeroPath, equalRateZeroOverZeroPath,
    replaceMagnitude, zero_pow (Nat.ne_of_gt hm),
    zero_pow (Nat.ne_of_gt hn)]

/-- The distinguished endpoint coordinate is explicitly `0 / 0`. -/
theorem powerLawZeroOverZeroPath_boundary_coordinates
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) :
    (powerLawZeroOverZeroPath point i m n 0).1 i = 0 ∧
      (powerLawZeroOverZeroPath point i m n 0).2 i = 0 := by
  simp [powerLawZeroOverZeroPath, replaceMagnitude,
    zero_pow (Nat.ne_of_gt hm), zero_pow (Nat.ne_of_gt hn)]

theorem powerLawZeroOverZeroPath_continuous
    (point : CoefficientPair) (i : Fin 4) (m n : Nat) :
    Continuous (powerLawZeroOverZeroPath point i m n) := by
  have hFirstLinear := (plusCoordinateApproach_continuous point i).fst
  have hSecondLinear := (minusCoordinateApproach_continuous point i).snd
  have hDenominatorPower : Continuous (fun t : Real => t ^ n) :=
    continuous_id'.pow n
  have hNumeratorPower : Continuous (fun t : Real => t ^ m) :=
    continuous_id'.pow m
  have hFirst := hFirstLinear.comp hDenominatorPower
  have hSecond := hSecondLinear.comp hNumeratorPower
  change Continuous (fun t =>
    (replaceMagnitude point.1 i (t ^ n),
      replaceMagnitude point.2 i (t ^ m)))
  exact hFirst.prodMk hSecond

/-- Every positive-exponent path converges to the common zero-over-zero
endpoint through positive parameters. -/
theorem powerLawZeroOverZeroPath_tendsto_common_boundary
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) :
    Tendsto (powerLawZeroOverZeroPath point i m n) (𝓝[>] (0 : Real))
      (𝓝 (equalRateZeroOverZeroPath point i 0)) := by
  rw [← powerLawZeroOverZeroPath_zero point i m n hm hn]
  exact
    (powerLawZeroOverZeroPath_continuous point i m n).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds

/-- Exact principal-root coordinate along the power-law path. -/
@[simp] theorem powerLawZeroOverZeroPath_root_eq
    (point : CoefficientPair) (i : Fin 4) (m n : Nat) (t : Real) :
    principalRootSpectrum (powerLawZeroOverZeroPath point i m n t) i =
      Real.sqrt (t ^ m / t ^ n) := by
  simp [principalRootSpectrum, relativeRatio, powerLawZeroOverZeroPath,
    replaceMagnitude]

/-- When the numerator exponent is at least the denominator exponent, cancel
the common power exactly. -/
theorem powerLawZeroOverZeroPath_root_eq_sqrt_pow_sub
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hnm : n ≤ m) {t : Real} (ht : 0 < t) :
    principalRootSpectrum (powerLawZeroOverZeroPath point i m n t) i =
      Real.sqrt (t ^ (m - n)) := by
  rw [powerLawZeroOverZeroPath_root_eq]
  apply congrArg Real.sqrt
  simpa only [div_eq_mul_inv] using (pow_sub₀ t ht.ne' hnm).symm

/-- When the denominator exponent is at least the numerator exponent, the
remaining factor is the reciprocal positive power. -/
theorem powerLawZeroOverZeroPath_root_eq_sqrt_inv_pow_sub
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hmn : m ≤ n) {t : Real} (ht : 0 < t) :
    principalRootSpectrum (powerLawZeroOverZeroPath point i m n t) i =
      Real.sqrt ((t ^ (n - m))⁻¹) := by
  rw [powerLawZeroOverZeroPath_root_eq]
  apply congrArg Real.sqrt
  rw [inv_eq_one_div]
  apply (div_eq_div_iff (pow_ne_zero n ht.ne')
    (pow_ne_zero (n - m) ht.ne')).2
  calc
    t ^ m * t ^ (n - m) = t ^ (m + (n - m)) := by rw [pow_add]
    _ = t ^ n := by rw [Nat.add_sub_of_le hmn]
    _ = 1 * t ^ n := by simp

/-- A strictly positive natural power tends to zero through positive
parameters. -/
theorem positivePower_tendsto_zero
    {k : Nat} (hk : 0 < k) :
    Tendsto (fun t : Real => t ^ k) (𝓝[>] (0 : Real)) (𝓝 0) := by
  have hId : Tendsto (fun t : Real => t) (𝓝[>] (0 : Real)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa [zero_pow (Nat.ne_of_gt hk)] using hId.pow k

/-- The same positive power tends to zero while remaining positive. -/
theorem positivePower_tendsto_zeroWithin
    {k : Nat} (hk : 0 < k) :
    Tendsto (fun t : Real => t ^ k) (𝓝[>] (0 : Real))
      (𝓝[>] (0 : Real)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨positivePower_tendsto_zero hk, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  exact pow_pos ht k

/-- Equal vanishing orders give the constant root limit `1`. -/
theorem powerLawZeroOverZeroPath_equal_exponents_tendsto_one
    (point : CoefficientPair) (i : Fin 4) (m : Nat) (_hm : 0 < m) :
    Tendsto
      (fun t => principalRootSpectrum
        (powerLawZeroOverZeroPath point i m m t) i)
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  simpa only [Nat.sub_self, pow_zero, Real.sqrt_one] using
    (powerLawZeroOverZeroPath_root_eq_sqrt_pow_sub point i m m le_rfl ht).symm

/-- Faster numerator vanishing (`n < m`) forces the root coordinate to zero.
-/
theorem powerLawZeroOverZeroPath_numerator_faster_tendsto_zero
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (_hm : 0 < m) (_hn : 0 < n) (hnm : n < m) :
    Tendsto
      (fun t => principalRootSpectrum
        (powerLawZeroOverZeroPath point i m n t) i)
      (𝓝[>] (0 : Real)) (𝓝 0) := by
  have hSqrtPower :
      Tendsto (fun t : Real => Real.sqrt (t ^ (m - n)))
        (𝓝[>] (0 : Real)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
      (positivePower_tendsto_zero (Nat.sub_pos_of_lt hnm))
  apply hSqrtPower.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  exact (powerLawZeroOverZeroPath_root_eq_sqrt_pow_sub point i m n
    hnm.le ht).symm

/-- Faster denominator vanishing (`m < n`) makes the selected root coordinate
diverge to `+∞`, hence in particular it is unbounded near the common
zero-over-zero endpoint. -/
theorem powerLawZeroOverZeroPath_denominator_faster_tendsto_atTop
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (_hm : 0 < m) (_hn : 0 < n) (hmn : m < n) :
    Tendsto
      (fun t => principalRootSpectrum
        (powerLawZeroOverZeroPath point i m n t) i)
      (𝓝[>] (0 : Real)) atTop := by
  have hInversePower :
      Tendsto (fun t : Real => (t ^ (n - m))⁻¹)
        (𝓝[>] (0 : Real)) atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (positivePower_tendsto_zeroWithin (Nat.sub_pos_of_lt hmn))
  have hSqrtInverse :
      Tendsto (fun t : Real => Real.sqrt ((t ^ (n - m))⁻¹))
        (𝓝[>] (0 : Real)) atTop := by
    simpa only [Function.comp_def] using
      Real.tendsto_sqrt_atTop.comp hInversePower
  apply hSqrtInverse.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  exact (powerLawZeroOverZeroPath_root_eq_sqrt_inv_pow_sub point i m n
    hmn.le ht).symm

end
end P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D
end JanusFormal
