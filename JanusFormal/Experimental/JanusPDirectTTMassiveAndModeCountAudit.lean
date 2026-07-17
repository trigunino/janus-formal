import JanusFormal.Experimental.JanusPLinearizedEinsteinTTDispersion
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedBimetricQuadraticFrechetSpectrum
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevPhysicalQuotient

namespace JanusFormal
namespace JanusPDirectTTMassiveAndModeCountAudit

set_option autoImplicit false

noncomputable section

open JanusPLinearizedEinsteinTTDispersion
open P0EFTJanusLinearizedEinsteinBianchiSymbol
open P0EFTJanusReducedBimetricQuadraticFrechetSpectrum
open P0EFTJanusLatticeFourierSaintVenantExactness

/-- Stabilizing Lorentzian TT equation on the plus sheet.  The minus sign in
front of the positive interaction Hessian is kept explicit as the field-
equation sign convention. -/
def ttEquationPlus
    (coupling omega waveNumber hPlus hMinus : ℝ) : ℝ :=
  linearizedEinsteinSymbol (waveCovector omega waveNumber)
      (ttPolarization hPlus) 1 2 - coupling * (hPlus - hMinus)

def ttEquationMinus
    (coupling omega waveNumber hPlus hMinus : ℝ) : ℝ :=
  linearizedEinsteinSymbol (waveCovector omega waveNumber)
      (ttPolarization hMinus) 1 2 - coupling * (hMinus - hPlus)

/-- The common sheet mode remains massless. -/
theorem common_tt_equations
    (coupling omega waveNumber amplitude : ℝ) :
    ttEquationPlus coupling omega waveNumber amplitude amplitude =
        (1 / 2 : ℝ) * (omega ^ 2 - waveNumber ^ 2) * amplitude ∧
      ttEquationMinus coupling omega waveNumber amplitude amplitude =
        (1 / 2 : ℝ) * (omega ^ 2 - waveNumber ^ 2) * amplitude := by
  constructor <;>
    simp [ttEquationPlus, ttEquationMinus,
      linearizedEinsteinSymbol_tt_component]

/-- The relative sheet mode receives the exact squared-frequency shift
`4 coupling` in the normalization of the P Einstein symbol. -/
theorem relative_tt_equations
    (coupling omega waveNumber amplitude : ℝ) :
    ttEquationPlus coupling omega waveNumber amplitude (-amplitude) =
        (1 / 2 : ℝ) *
          (omega ^ 2 - waveNumber ^ 2 - 4 * coupling) * amplitude ∧
      ttEquationMinus coupling omega waveNumber amplitude (-amplitude) =
        -(1 / 2 : ℝ) *
          (omega ^ 2 - waveNumber ^ 2 - 4 * coupling) * amplitude := by
  constructor <;>
    simp [ttEquationPlus, ttEquationMinus,
      linearizedEinsteinSymbol_tt_component] <;>
    ring

theorem relative_tt_equation_iff_massive_dispersion
    (coupling omega waveNumber amplitude : ℝ)
    (hAmplitude : amplitude ≠ 0) :
    ttEquationPlus coupling omega waveNumber amplitude (-amplitude) = 0 ↔
      omega ^ 2 = waveNumber ^ 2 + 4 * coupling := by
  rw [relative_tt_equations coupling omega waveNumber amplitude |>.1]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hDifference | hAmplitudeZero
    · linarith
    · exact False.elim (hAmplitude hAmplitudeZero)
  · intro h
    rw [h]
    ring

/-- A concrete infinite family of distinct nonzero modes in P's current
`Z^4` Sobolev lattice. -/
def positiveAxisMode (n : ℕ) : LatticeMode :=
  fun index => if index = 0 then Int.ofNat (n + 1) else 0

theorem positiveAxisMode_ne_zero (n : ℕ) : positiveAxisMode n ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [positiveAxisMode] at h0
  omega

theorem positiveAxisMode_injective : Function.Injective positiveAxisMode := by
  intro first second h
  have h0 := congrFun h 0
  simp [positiveAxisMode] at h0
  omega

theorem current_sobolev_lattice_has_infinitely_many_nonzero_modes :
    Set.Infinite (Set.range positiveAxisMode) :=
  Set.infinite_range_of_injective positiveAxisMode_injective

end
end JanusPDirectTTMassiveAndModeCountAudit
end JanusFormal
