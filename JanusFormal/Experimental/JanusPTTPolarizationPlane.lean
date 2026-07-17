import JanusFormal.Experimental.JanusPDirectTTMassiveAndModeCountAudit

namespace JanusFormal
namespace JanusPTTPolarizationPlane

set_option autoImplicit false

noncomputable section

open JanusPLinearizedEinsteinTTDispersion
open JanusPDirectTTMassiveAndModeCountAudit
open P0EFTJanusLinearizedEinsteinBianchiSymbol

/-- The second independent TT polarization, `h₁₁=-h₂₂=A`. -/
def ttPlusPolarization (amplitude : ℝ) : SymmetricPerturbation where
  tensor := fun first second =>
    if first = 1 ∧ second = 1 then amplitude
    else if first = 2 ∧ second = 2 then -amplitude
    else 0
  tensor_symmetric := by
    ext first second
    fin_cases first <;> fin_cases second <;>
      simp [Matrix.transpose_apply]

/-- P's Einstein symbol gives the same wave polynomial on the plus
polarization as on the already audited cross polarization. -/
theorem linearizedEinsteinSymbol_ttPlus_component
    (omega waveNumber amplitude : ℝ) :
    linearizedEinsteinSymbol (waveCovector omega waveNumber)
        (ttPlusPolarization amplitude) 1 1 =
      (1 / 2 : ℝ) * (omega ^ 2 - waveNumber ^ 2) * amplitude := by
  simp [linearizedEinsteinSymbol, linearizedRicciSymbol,
    linearizedScalarCurvatureSymbol, doubleMomentumContraction,
    momentumContraction, minkowskiTrace, minkowskiMetric,
    waveCovector_square, waveCovector, ttPlusPolarization, raiseCovector,
    etaSign, sum_fin_four]
  ring

theorem linearizedEinsteinSymbol_ttPlus_opposite_component
    (omega waveNumber amplitude : ℝ) :
    linearizedEinsteinSymbol (waveCovector omega waveNumber)
        (ttPlusPolarization amplitude) 2 2 =
      -(1 / 2 : ℝ) * (omega ^ 2 - waveNumber ^ 2) * amplitude := by
  simp [linearizedEinsteinSymbol, linearizedRicciSymbol,
    linearizedScalarCurvatureSymbol, doubleMomentumContraction,
    momentumContraction, minkowskiTrace, minkowskiMetric,
    waveCovector_square, waveCovector, ttPlusPolarization, raiseCovector,
    etaSign, sum_fin_four]
  ring

/-- The plus and cross TT polarizations are linearly independent. -/
theorem tt_polarizations_independent (plus cross : ℝ) :
    (ttPlusPolarization plus).tensor + (ttPolarization cross).tensor = 0 ↔
      plus = 0 ∧ cross = 0 := by
  constructor
  · intro h
    have hPlus := congrFun (congrFun h 1) 1
    have hCross := congrFun (congrFun h 1) 2
    simp [ttPlusPolarization, ttPolarization] at hPlus hCross
    exact ⟨hPlus, hCross⟩
  · rintro ⟨rfl, rfl⟩
    ext first second
    simp [ttPlusPolarization, ttPolarization]

def ttPlusEquationOnPlusSheet
    (coupling omega waveNumber hPlus hMinus : ℝ) : ℝ :=
  linearizedEinsteinSymbol (waveCovector omega waveNumber)
      (ttPlusPolarization hPlus) 1 1 - coupling * (hPlus - hMinus)

/-- The second TT polarization has the same massive relative dispersion. -/
theorem ttPlus_relative_equation_iff_massive_dispersion
    (coupling omega waveNumber amplitude : ℝ)
    (hAmplitude : amplitude ≠ 0) :
    ttPlusEquationOnPlusSheet coupling omega waveNumber
        amplitude (-amplitude) = 0 ↔
      omega ^ 2 = waveNumber ^ 2 + 4 * coupling := by
  simp only [ttPlusEquationOnPlusSheet,
    linearizedEinsteinSymbol_ttPlus_component]
  constructor
  · intro h
    have hFactor :
        (1 / 2 : ℝ) *
            (omega ^ 2 - waveNumber ^ 2 - 4 * coupling) * amplitude = 0 := by
      linarith
    rcases mul_eq_zero.mp hFactor with hDifference | hAmplitudeZero
    · linarith
    · exact False.elim (hAmplitude hAmplitudeZero)
  · intro h
    rw [h]
    ring

end
end JanusPTTPolarizationPlane
end JanusFormal
