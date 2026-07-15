import Mathlib
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusSVTStabilityCone
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPTSymmetricFlatBimetricBranch

namespace JanusFormal
namespace P0EFTJanusCosmologicalModeStability

set_option autoImplicit false

open P0EFTJanusSVTStabilityCone
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Squared propagation speed from reduced kinetic and gradient coefficients. -/
noncomputable def modeSpeedSquared (kinetic gradient : ℝ) : ℝ :=
  gradient / kinetic

/-- Reduced Fourier dispersion relation. -/
noncomputable def modeFrequencySquared
    (kinetic gradient massSquared waveNumber : ℝ) : ℝ :=
  modeSpeedSquared kinetic gradient * waveNumber ^ 2 + massSquared

/-- Positive kinetic and gradient coefficients give positive squared speed. -/
theorem positive_coefficients_give_positive_speed
    (kinetic gradient : ℝ)
    (hKinetic : 0 < kinetic)
    (hGradient : 0 < gradient) :
    0 < modeSpeedSquared kinetic gradient := by
  unfold modeSpeedSquared
  exact div_pos hGradient hKinetic

/-- No-gradient-instability and no-tachyon signs give nonnegative frequency. -/
theorem stable_mode_has_nonnegative_frequency_squared
    (kinetic gradient massSquared waveNumber : ℝ)
    (hKinetic : 0 < kinetic)
    (hGradient : 0 < gradient)
    (hMass : 0 ≤ massSquared) :
    0 ≤ modeFrequencySquared kinetic gradient massSquared waveNumber := by
  unfold modeFrequencySquared
  have hSpeed : 0 ≤ modeSpeedSquared kinetic gradient :=
    le_of_lt (positive_coefficients_give_positive_speed
      kinetic gradient hKinetic hGradient)
  positivity

/-- Every nonzero Fourier mode has strictly positive frequency squared. -/
theorem nonzero_wave_mode_has_positive_frequency_squared
    (kinetic gradient massSquared waveNumber : ℝ)
    (hKinetic : 0 < kinetic)
    (hGradient : 0 < gradient)
    (hMass : 0 ≤ massSquared)
    (hWave : waveNumber ≠ 0) :
    0 < modeFrequencySquared kinetic gradient massSquared waveNumber := by
  unfold modeFrequencySquared
  have hSpeed := positive_coefficients_give_positive_speed
    kinetic gradient hKinetic hGradient
  have hWaveSquared : 0 < waveNumber ^ 2 := sq_pos_of_ne_zero hWave
  exact add_pos_of_pos_of_nonneg (mul_pos hSpeed hWaveSquared) hMass

/-- The vector coefficients from the selected SVT cone have stable dispersion. -/
theorem vector_mode_stable_on_svt_cone
    (v planckSquared aetherScale hrMassSquared waveNumber : ℝ)
    (hV : 0 < v)
    (hPlanck : 0 < planckSquared)
    (hAether : aetherScale < planckSquared)
    (hMass : 0 ≤ hrMassSquared) :
    0 ≤ modeFrequencySquared
      (vectorAlpha v planckSquared aetherScale)
      (vectorBeta v planckSquared)
      hrMassSquared waveNumber := by
  rcases vector_stability_cone v planckSquared aetherScale hrMassSquared
    hV hPlanck hAether hMass with ⟨hAlpha, hBeta, hMassSafe⟩
  exact stable_mode_has_nonnegative_frequency_squared
    _ _ _ _ hAlpha hBeta hMassSafe

/-- The scalar coefficients from the selected SVT cone have stable dispersion. -/
theorem scalar_mode_stable_on_svt_cone
    (v planckSquared aetherScale lambdaPhi membraneTension
      hrMassSquared waveNumber : ℝ)
    (hV : 0 < v)
    (hPlanck : 0 < planckSquared)
    (hAether : aetherScale < planckSquared)
    (hLambda : 0 ≤ lambdaPhi)
    (hTension : 0 ≤ membraneTension)
    (hMass : 0 ≤ hrMassSquared) :
    0 ≤ modeFrequencySquared
      (scalarAlpha v planckSquared aetherScale lambdaPhi)
      (scalarBeta v planckSquared membraneTension hrMassSquared)
      (scalarMassSquared v lambdaPhi hrMassSquared) waveNumber := by
  rcases scalar_stability_cone
    v planckSquared aetherScale lambdaPhi membraneTension hrMassSquared
    hV hPlanck hAether hLambda hTension hMass with
      ⟨hAlpha, hBeta, hMassSafe⟩
  exact stable_mode_has_nonnegative_frequency_squared
    _ _ _ _ hAlpha hBeta hMassSafe

/-- The PT-flat coefficient cone has a strictly positive relative tensor mass. -/
theorem pt_flat_cosmological_relative_mode_not_tachyonic
    (beta1 beta2 : ℝ)
    (hBeta1 : 0 < beta1)
    (hBeta2 : 0 ≤ beta2) :
    0 < fpMassCombination (ptFlatCoefficients beta1 beta2) :=
  pt_flat_fp_mass_positive beta1 beta2 hBeta1 hBeta2

end P0EFTJanusCosmologicalModeStability
end JanusFormal
