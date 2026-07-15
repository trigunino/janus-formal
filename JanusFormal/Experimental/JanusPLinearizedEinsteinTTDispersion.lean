import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearizedEinsteinBianchiSymbol

namespace JanusFormal
namespace JanusPLinearizedEinsteinTTDispersion

set_option autoImplicit false

noncomputable section

open P0EFTJanusLinearizedEinsteinBianchiSymbol

/-- Fourier covector `(omega,0,0,k)` in the convention of the P symbol gate. -/
def waveCovector (omega waveNumber : ℝ) : Covector4 :=
  fun index => if index = 0 then omega else if index = 3 then waveNumber else 0

/-- One off-diagonal transverse-traceless polarization `h₁₂=h₂₁=A`. -/
def ttPolarization (amplitude : ℝ) : SymmetricPerturbation where
  tensor := fun first second =>
    if (first = 1 ∧ second = 2) ∨ (first = 2 ∧ second = 1)
    then amplitude else 0
  tensor_symmetric := by
    ext first second
    fin_cases first <;> fin_cases second <;>
      simp [Matrix.transpose_apply]

/-- The covector square is the Lorentzian Fourier polynomial `-ω²+k²`. -/
theorem waveCovector_square (omega waveNumber : ℝ) :
    covectorSquare (waveCovector omega waveNumber) =
      -(omega ^ 2) + waveNumber ^ 2 := by
  simp [covectorSquare, raiseCovector, waveCovector, etaSign, sum_fin_four]
  ring

/-- P's actual linearized Einstein principal symbol supplies the TT wave
operator `1/2 (ω²-k²)` on the selected polarization. -/
theorem linearizedEinsteinSymbol_tt_component
    (omega waveNumber amplitude : ℝ) :
    linearizedEinsteinSymbol (waveCovector omega waveNumber)
        (ttPolarization amplitude) 1 2 =
      (1 / 2 : ℝ) * (omega ^ 2 - waveNumber ^ 2) * amplitude := by
  simp [linearizedEinsteinSymbol, linearizedRicciSymbol,
    linearizedScalarCurvatureSymbol, doubleMomentumContraction,
    momentumContraction, minkowskiTrace, minkowskiMetric,
    waveCovector_square, waveCovector, ttPolarization, raiseCovector,
    etaSign, sum_fin_four]
  ring

/-- For a nonzero TT amplitude, the vacuum P symbol equation gives the
massless dispersion `ω²=k²`. -/
theorem vacuum_tt_symbol_eq_zero_iff_dispersion
    (omega waveNumber amplitude : ℝ) (hAmplitude : amplitude ≠ 0) :
    linearizedEinsteinSymbol (waveCovector omega waveNumber)
        (ttPolarization amplitude) 1 2 = 0 ↔
      omega ^ 2 = waveNumber ^ 2 := by
  rw [linearizedEinsteinSymbol_tt_component]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hDifference | hAmplitudeZero
    · linarith
    · exact False.elim (hAmplitude hAmplitudeZero)
  · intro h
    rw [h]
    ring

end
end JanusPLinearizedEinsteinTTDispersion
end JanusFormal
