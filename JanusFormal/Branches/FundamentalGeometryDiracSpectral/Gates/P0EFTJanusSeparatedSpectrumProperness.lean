import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusDiagonalCompactResolvent

namespace JanusFormal
namespace P0EFTJanusSeparatedSpectrumProperness

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusInfiniteL2DiracDomain
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusDiagonalCompactResolvent

noncomputable section

/-- Positive representative of the separated Dirac spectrum. -/
def separatedDiracWeight (data : ProductThroatSpectralData)
    (mode : ProductDiracMode) : ℝ :=
  Real.sqrt (productDiracEigenvalueSquared data mode)

theorem separated_dirac_weight_nonnegative (data : ProductThroatSpectralData)
    (mode : ProductDiracMode) : 0 ≤ separatedDiracWeight data mode :=
  Real.sqrt_nonneg _

theorem spectrum_squared_le_of_weight_le
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) (R : ℝ)
    (hWeight : separatedDiracWeight data mode ≤ R) :
    productDiracEigenvalueSquared data mode ≤ R ^ 2 := by
  have hSpectrum : 0 ≤ productDiracEigenvalueSquared data mode :=
    le_of_lt (product_spectrum_has_positive_gap data mode)
  rw [← Real.sq_sqrt hSpectrum]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hWeight)).2 hWeight

theorem sphere_level_cast_le_of_weight_le
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) (R : ℝ)
    (hWeight : separatedDiracWeight data mode ≤ R) :
    ((mode.sphereLevel + 1 : ℕ) : ℝ) ≤ R * data.sphereRadius := by
  have hR : 0 ≤ R := (separated_dirac_weight_nonnegative data mode).trans hWeight
  have hSphere : sphereEigenvalueSquared data mode.sphereLevel ≤ R ^ 2 :=
    le_trans (by
      unfold productDiracEigenvalueSquared
      exact le_add_of_nonneg_right (sq_nonneg _))
      (spectrum_squared_le_of_weight_le data mode R hWeight)
  unfold sphereEigenvalueSquared at hSphere
  have hRadiusSq : 0 < data.sphereRadius ^ 2 := sq_pos_of_pos data.sphereRadiusPositive
  have hSq : (((mode.sphereLevel + 1 : ℕ) : ℝ)) ^ 2 ≤
      (R * data.sphereRadius) ^ 2 := by
    apply (div_le_iff₀ hRadiusSq).1 at hSphere
    nlinarith
  exact (sq_le_sq₀ (by positivity)
    (mul_nonneg hR data.sphereRadiusPositive.le)).1 hSq

theorem circle_eigenvalue_abs_le_of_weight_le
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) (R : ℝ)
    (hWeight : separatedDiracWeight data mode ≤ R) :
    |circleEigenvalue data mode.rootChoice mode.circleMode| ≤ R := by
  have hR : 0 ≤ R := (separated_dirac_weight_nonnegative data mode).trans hWeight
  have hCircleSq : circleEigenvalue data mode.rootChoice mode.circleMode ^ 2 ≤ R ^ 2 :=
    le_trans (by
      unfold productDiracEigenvalueSquared
      exact le_add_of_nonneg_left (le_of_lt
        (sphere_eigenvalue_squared_positive data mode.sphereLevel)))
      (spectrum_squared_le_of_weight_le data mode R hWeight)
  exact abs_le_of_sq_le_sq hCircleSq hR

theorem circle_numerator_abs_cast_le_of_weight_le
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) (R : ℝ)
    (hWeight : separatedDiracWeight data mode ≤ R) :
    |(normalRootModeNumerator mode.rootChoice mode.circleMode : ℝ)| ≤
      R * (2 * data.circlePeriod) / Real.pi := by
  have hCircle := circle_eigenvalue_abs_le_of_weight_le data mode R hWeight
  have hDen : 0 < 2 * data.circlePeriod := mul_pos (by norm_num) data.circlePeriodPositive
  unfold circleEigenvalue at hCircle
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hDen] at hCircle
  apply (le_div_iff₀ Real.pi_pos).2
  have hScaled := (div_le_iff₀ hDen).1 hCircle
  nlinarith

theorem circle_mode_abs_cast_le_of_weight_le
    (data : ProductThroatSpectralData) (mode : ProductDiracMode) (R : ℝ)
    (hWeight : separatedDiracWeight data mode ≤ R) :
    |(mode.circleMode : ℝ)| ≤
      (R * (2 * data.circlePeriod) / Real.pi + 1) / 4 := by
  have hNumerator := circle_numerator_abs_cast_le_of_weight_le data mode R hWeight
  rcases mode with ⟨level, circle, choice⟩
  cases choice <;>
    simp only [normalRootModeNumerator] at hNumerator <;>
    push_cast at hNumerator <;>
    rw [abs_le] at hNumerator <;>
    rw [abs_le] <;>
    constructor <;> nlinarith

theorem separated_dirac_weight_coercive (data : ProductThroatSpectralData) :
    CoerciveDiagonalWeight (separatedDiracWeight data) := by
  intro R
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (R * data.sphereRadius)
      ((R * (2 * data.circlePeriod) / Real.pi + 1) / 4))
  refine ⟨N, ?_⟩
  intro mode hMode
  have hWeight : separatedDiracWeight data mode ≤ R := by
    change ‖(separatedDiracWeight data mode : ℂ)‖ ≤ R at hMode
    simpa [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (separated_dirac_weight_nonnegative data mode)] using hMode
  have hLevelBound := sphere_level_cast_le_of_weight_le data mode R hWeight
  have hCircleBound := circle_mode_abs_cast_le_of_weight_le data mode R hWeight
  have hLevelThreshold : R * data.sphereRadius < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hCircleThreshold :
      (R * (2 * data.circlePeriod) / Real.pi + 1) / 4 < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hLevelCast : (mode.sphereLevel : ℝ) < (N : ℝ) := by
    norm_num at hLevelBound
    linarith
  have hLevel : mode.sphereLevel ≤ N := by
    exact_mod_cast hLevelCast.le
  rw [abs_le] at hCircleBound
  have hCircleLowerCast : (-(N : ℤ) : ℝ) < (mode.circleMode : ℝ) := by
    push_cast
    linarith [hCircleBound.1]
  have hCircleUpperCast : (mode.circleMode : ℝ) < ((N : ℤ) : ℝ) := by
    push_cast
    linarith [hCircleBound.2]
  have hCircleLower : -(N : ℤ) ≤ mode.circleMode := by
    exact_mod_cast hCircleLowerCast.le
  have hCircleUpper : mode.circleMode ≤ (N : ℤ) := by
    exact_mod_cast hCircleUpperCast.le
  exact ⟨hLevel, hCircleLower, hCircleUpper⟩

theorem separated_dirac_weight_proper (data : ProductThroatSpectralData) :
    ProperDiagonalWeight (separatedDiracWeight data) :=
  proper_diagonal_weight_of_coercive _ (separated_dirac_weight_coercive data)

/-- The explicit separated D2 Dirac resolvent is compact. -/
theorem separated_dirac_shift_I_resolvent_compact (data : ProductThroatSpectralData) :
    IsCompactOperator (shiftIResolventCLM (separatedDiracWeight data)) :=
  shift_I_resolvent_compact_of_proper _ (separated_dirac_weight_proper data)

end

end P0EFTJanusSeparatedSpectrumProperness
end JanusFormal
