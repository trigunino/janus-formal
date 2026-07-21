import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

/-!
# Positive real-power classification at a diagonal zero-over-zero face

The natural monomial classification extends to arbitrary strictly positive
real exponents.  This remains a diagonal path classification; it does not
cover arbitrary nonlinear matrix paths or Jordan degenerations.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalRealPowerZeroOverZeroClassification4D

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

def realPowerZeroOverZeroPath
    (point : CoefficientPair) (i : Fin 4)
    (m n : Real) (t : Real) : CoefficientPair :=
  (replaceMagnitude point.1 i (t ^ n),
    replaceMagnitude point.2 i (t ^ m))

theorem realPowerZeroOverZeroPath_mem_globalDomain
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) (m n : Real) {t : Real} (ht : 0 < t) :
    realPowerZeroOverZeroPath point i m n t ∈
      globalDiagonalLorentzDomain := by
  constructor <;> intro j
  · by_cases hji : j = i
    · subst j
      simpa [realPowerZeroOverZeroPath, replaceMagnitude] using
        Real.rpow_pos_of_pos ht n
    · simpa [realPowerZeroOverZeroPath, replaceMagnitude, hji] using
        hPoint.1 j
  · by_cases hji : j = i
    · subst j
      simpa [realPowerZeroOverZeroPath, replaceMagnitude] using
        Real.rpow_pos_of_pos ht m
    · simpa [realPowerZeroOverZeroPath, replaceMagnitude, hji] using
        hPoint.2 j

@[simp] theorem realPowerZeroOverZeroPath_zero
    (point : CoefficientPair) (i : Fin 4) (m n : Real)
    (hm : 0 < m) (hn : 0 < n) :
    realPowerZeroOverZeroPath point i m n 0 =
      equalRateZeroOverZeroPath point i 0 := by
  simp [realPowerZeroOverZeroPath, equalRateZeroOverZeroPath,
    replaceMagnitude, Real.zero_rpow hm.ne', Real.zero_rpow hn.ne']

theorem realPowerZeroOverZeroPath_continuous
    (point : CoefficientPair) (i : Fin 4) (m n : Real)
    (hm : 0 ≤ m) (hn : 0 ≤ n) :
    Continuous (realPowerZeroOverZeroPath point i m n) := by
  have hFirst := (plusCoordinateApproach_continuous point i).fst.comp
    (Real.continuous_rpow_const hn)
  have hSecond := (minusCoordinateApproach_continuous point i).snd.comp
    (Real.continuous_rpow_const hm)
  exact hFirst.prodMk hSecond

theorem realPowerZeroOverZeroPath_tendsto_common_boundary
    (point : CoefficientPair) (i : Fin 4) (m n : Real)
    (hm : 0 < m) (hn : 0 < n) :
    Tendsto (realPowerZeroOverZeroPath point i m n) (𝓝[>] (0 : Real))
      (nhds (equalRateZeroOverZeroPath point i 0)) := by
  rw [← realPowerZeroOverZeroPath_zero point i m n hm hn]
  exact (realPowerZeroOverZeroPath_continuous point i m n hm.le hn.le)
    |>.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

@[simp] theorem realPowerZeroOverZeroPath_root_eq
    (point : CoefficientPair) (i : Fin 4) (m n t : Real) :
    principalRootSpectrum (realPowerZeroOverZeroPath point i m n t) i =
      Real.sqrt (t ^ m / t ^ n) := by
  simp [principalRootSpectrum, relativeRatio, realPowerZeroOverZeroPath,
    replaceMagnitude]

theorem realPowerZeroOverZeroPath_root_eq_sqrt_rpow_sub
    (point : CoefficientPair) (i : Fin 4) (m n : Real)
    {t : Real} (ht : 0 < t) :
    principalRootSpectrum (realPowerZeroOverZeroPath point i m n t) i =
      Real.sqrt (t ^ (m - n)) := by
  rw [realPowerZeroOverZeroPath_root_eq]
  congr 1
  exact (Real.rpow_sub ht m n).symm

theorem positiveRealPower_tendsto_zero {exponent : Real}
    (hExponent : 0 < exponent) :
    Tendsto (fun t : Real => t ^ exponent) (𝓝[>] (0 : Real)) (nhds 0) := by
  exact (tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero hExponent

theorem realPowerZeroOverZeroPath_equal_exponents_tendsto_one
    (point : CoefficientPair) (i : Fin 4) (m : Real) (_hm : 0 < m) :
    Tendsto
      (fun t => principalRootSpectrum
        (realPowerZeroOverZeroPath point i m m t) i)
      (𝓝[>] (0 : Real)) (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [realPowerZeroOverZeroPath_root_eq_sqrt_rpow_sub point i m m ht]
  simp

theorem realPowerZeroOverZeroPath_numerator_faster_tendsto_zero
    (point : CoefficientPair) (i : Fin 4) (m n : Real)
    (_hm : 0 < m) (_hn : 0 < n) (hnm : n < m) :
    Tendsto
      (fun t => principalRootSpectrum
        (realPowerZeroOverZeroPath point i m n t) i)
      (𝓝[>] (0 : Real)) (nhds 0) := by
  have hSqrt : Tendsto (fun t : Real => Real.sqrt (t ^ (m - n)))
      (𝓝[>] (0 : Real)) (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        (positiveRealPower_tendsto_zero (sub_pos.mpr hnm))
  apply hSqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  exact (realPowerZeroOverZeroPath_root_eq_sqrt_rpow_sub
    point i m n ht).symm

theorem realPowerZeroOverZeroPath_denominator_faster_tendsto_atTop
    (point : CoefficientPair) (i : Fin 4) (m n : Real)
    (_hm : 0 < m) (_hn : 0 < n) (hmn : m < n) :
    Tendsto
      (fun t => principalRootSpectrum
        (realPowerZeroOverZeroPath point i m n t) i)
      (𝓝[>] (0 : Real)) atTop := by
  have hPower : Tendsto (fun t : Real => t ^ (m - n))
      (𝓝[>] (0 : Real)) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hmn)
  have hSqrt : Tendsto (fun t : Real => Real.sqrt (t ^ (m - n)))
      (𝓝[>] (0 : Real)) atTop := Real.tendsto_sqrt_atTop.comp hPower
  apply hSqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  exact (realPowerZeroOverZeroPath_root_eq_sqrt_rpow_sub
    point i m n ht).symm

end

end P0EFTJanusGlobalDiagonalRealPowerZeroOverZeroClassification4D
end JanusFormal
