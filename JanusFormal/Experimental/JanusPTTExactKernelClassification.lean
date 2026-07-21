import JanusFormal.Experimental.JanusPTTPolarizationPlane

namespace JanusFormal
namespace JanusPTTExactKernelClassification

set_option autoImplicit false

noncomputable section

open JanusPLinearizedEinsteinTTDispersion
open JanusPDirectTTMassiveAndModeCountAudit

/-- Fourier kinetic eigenvalue of one TT polarization. -/
def ttKineticEigenvalue (omega waveNumber : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (omega ^ 2 - waveNumber ^ 2)

/-- Exact diagonalization of the two-sheet TT equations into their common
and relative channels. -/
theorem tt_equation_pair_diagonalization
    (coupling omega waveNumber hPlus hMinus : ℝ) :
    ttEquationPlus coupling omega waveNumber hPlus hMinus +
          ttEquationMinus coupling omega waveNumber hPlus hMinus =
        ttKineticEigenvalue omega waveNumber * (hPlus + hMinus) ∧
      ttEquationPlus coupling omega waveNumber hPlus hMinus -
          ttEquationMinus coupling omega waveNumber hPlus hMinus =
        (ttKineticEigenvalue omega waveNumber - 2 * coupling) *
          (hPlus - hMinus) := by
  constructor <;>
    simp [ttEquationPlus, ttEquationMinus, ttKineticEigenvalue,
      linearizedEinsteinSymbol_tt_component] <;>
    ring

/-- The determinant of the two-sheet TT symbol factors into exactly the
massless and massive dispersion polynomials. -/
theorem tt_symbol_determinant_factorization
    (coupling omega waveNumber : ℝ) :
    (ttKineticEigenvalue omega waveNumber - coupling) ^ 2 - coupling ^ 2 =
      (1 / 4 : ℝ) * (omega ^ 2 - waveNumber ^ 2) *
        (omega ^ 2 - waveNumber ^ 2 - 4 * coupling) := by
  simp [ttKineticEigenvalue]
  ring

/-- Determinant of the two-sheet TT Fourier symbol. -/
def ttSymbolDeterminant (coupling omega waveNumber : ℝ) : ℝ :=
  (ttKineticEigenvalue omega waveNumber - coupling) ^ 2 - coupling ^ 2

theorem ttSymbolDeterminant_factorization
    (coupling omega waveNumber : ℝ) :
    ttSymbolDeterminant coupling omega waveNumber =
      (1 / 4 : ℝ) * (omega ^ 2 - waveNumber ^ 2) *
        (omega ^ 2 - waveNumber ^ 2 - 4 * coupling) := by
  exact tt_symbol_determinant_factorization coupling omega waveNumber

/-- Plus-sheet amplitude produced by a two-sheet TT source off shell. -/
def ttResponsePlus
    (coupling omega waveNumber sourcePlus sourceMinus : ℝ) : ℝ :=
  ((ttKineticEigenvalue omega waveNumber - coupling) * sourcePlus -
      coupling * sourceMinus) /
    ttSymbolDeterminant coupling omega waveNumber

/-- Minus-sheet amplitude produced by a two-sheet TT source off shell. -/
def ttResponseMinus
    (coupling omega waveNumber sourcePlus sourceMinus : ℝ) : ℝ :=
  ((ttKineticEigenvalue omega waveNumber - coupling) * sourceMinus -
      coupling * sourcePlus) /
    ttSymbolDeterminant coupling omega waveNumber

private theorem symmetricTwoByTwoInverse
    (diagonal offDiagonal sourcePlus sourceMinus determinant : ℝ)
    (hDeterminantFormula :
      determinant = diagonal ^ 2 - offDiagonal ^ 2)
    (hDeterminant : determinant ≠ 0) :
    diagonal * ((diagonal * sourcePlus - offDiagonal * sourceMinus) /
          determinant) +
        offDiagonal * ((diagonal * sourceMinus - offDiagonal * sourcePlus) /
          determinant) = sourcePlus ∧
      offDiagonal * ((diagonal * sourcePlus - offDiagonal * sourceMinus) /
          determinant) +
        diagonal * ((diagonal * sourceMinus - offDiagonal * sourcePlus) /
          determinant) = sourceMinus := by
  constructor <;>
    field_simp [hDeterminant] <;>
    rw [hDeterminantFormula] <;>
    ring

/-- The explicit inverse symbol solves the sourced TT equations whenever its
determinant is nonzero. -/
theorem tt_response_solves_sourced_equations
    (coupling omega waveNumber sourcePlus sourceMinus : ℝ)
    (hDeterminant : ttSymbolDeterminant coupling omega waveNumber ≠ 0) :
    ttEquationPlus coupling omega waveNumber
          (ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus)
          (ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus) =
        sourcePlus ∧
      ttEquationMinus coupling omega waveNumber
          (ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus)
          (ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus) =
        sourceMinus := by
  have hInverse := symmetricTwoByTwoInverse
    (ttKineticEigenvalue omega waveNumber - coupling) coupling
    sourcePlus sourceMinus (ttSymbolDeterminant coupling omega waveNumber)
    (by rfl) hDeterminant
  constructor
  · calc
      ttEquationPlus coupling omega waveNumber
          (ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus)
          (ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus) =
        (ttKineticEigenvalue omega waveNumber - coupling) *
            ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus +
          coupling *
            ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus := by
              simp [ttEquationPlus, ttKineticEigenvalue,
                linearizedEinsteinSymbol_tt_component]
              ring
      _ = sourcePlus := by
        simpa [ttResponsePlus, ttResponseMinus] using hInverse.1
  · calc
      ttEquationMinus coupling omega waveNumber
          (ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus)
          (ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus) =
        coupling *
            ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus +
          (ttKineticEigenvalue omega waveNumber - coupling) *
            ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus := by
              simp [ttEquationMinus, ttKineticEigenvalue,
                linearizedEinsteinSymbol_tt_component]
              ring
      _ = sourceMinus := by
        simpa [ttResponsePlus, ttResponseMinus] using hInverse.2

theorem ttSymbolDeterminant_ne_zero_of_off_shell
    (coupling omega waveNumber : ℝ)
    (hNotMassless : omega ^ 2 ≠ waveNumber ^ 2)
    (hNotMassive : omega ^ 2 ≠ waveNumber ^ 2 + 4 * coupling) :
    ttSymbolDeterminant coupling omega waveNumber ≠ 0 := by
  rw [ttSymbolDeterminant_factorization]
  have hFirst : omega ^ 2 - waveNumber ^ 2 ≠ 0 := sub_ne_zero.mpr hNotMassless
  have hSecond : omega ^ 2 - waveNumber ^ 2 - 4 * coupling ≠ 0 := by
    intro h
    apply hNotMassive
    linarith
  exact mul_ne_zero (mul_ne_zero (by norm_num) hFirst) hSecond

/-- Away from both dispersion shells, the TT Fourier kernel is trivial. -/
theorem off_shell_tt_kernel_is_trivial
    (coupling omega waveNumber hPlus hMinus : ℝ)
    (hPlusEquation :
      ttEquationPlus coupling omega waveNumber hPlus hMinus = 0)
    (hMinusEquation :
      ttEquationMinus coupling omega waveNumber hPlus hMinus = 0)
    (hNotMassless : omega ^ 2 ≠ waveNumber ^ 2)
    (hNotMassive : omega ^ 2 ≠ waveNumber ^ 2 + 4 * coupling) :
    hPlus = 0 ∧ hMinus = 0 := by
  have hDiagonal :=
    tt_equation_pair_diagonalization coupling omega waveNumber hPlus hMinus
  have hCommonProduct :
      ttKineticEigenvalue omega waveNumber * (hPlus + hMinus) = 0 := by
    rw [← hDiagonal.1, hPlusEquation, hMinusEquation]
    ring
  have hRelativeProduct :
      (ttKineticEigenvalue omega waveNumber - 2 * coupling) *
          (hPlus - hMinus) = 0 := by
    rw [← hDiagonal.2, hPlusEquation, hMinusEquation]
    ring
  have hCommonEigenvalue : ttKineticEigenvalue omega waveNumber ≠ 0 := by
    intro h
    apply hNotMassless
    simp [ttKineticEigenvalue] at h
    linarith
  have hRelativeEigenvalue :
      ttKineticEigenvalue omega waveNumber - 2 * coupling ≠ 0 := by
    intro h
    apply hNotMassive
    simp [ttKineticEigenvalue] at h
    linarith
  have hCommon : hPlus + hMinus = 0 :=
    (mul_eq_zero.mp hCommonProduct).resolve_left hCommonEigenvalue
  have hRelative : hPlus - hMinus = 0 :=
    (mul_eq_zero.mp hRelativeProduct).resolve_left hRelativeEigenvalue
  constructor <;> linarith

/-- The explicit sourced response is the unique off-shell TT solution. -/
theorem off_shell_sourced_tt_solution_is_unique
    (coupling omega waveNumber sourcePlus sourceMinus hPlus hMinus : ℝ)
    (hPlusEquation :
      ttEquationPlus coupling omega waveNumber hPlus hMinus = sourcePlus)
    (hMinusEquation :
      ttEquationMinus coupling omega waveNumber hPlus hMinus = sourceMinus)
    (hNotMassless : omega ^ 2 ≠ waveNumber ^ 2)
    (hNotMassive : omega ^ 2 ≠ waveNumber ^ 2 + 4 * coupling) :
    hPlus = ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus ∧
      hMinus = ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus := by
  have hDeterminant := ttSymbolDeterminant_ne_zero_of_off_shell
    coupling omega waveNumber hNotMassless hNotMassive
  have hResponse := tt_response_solves_sourced_equations
    coupling omega waveNumber sourcePlus sourceMinus hDeterminant
  let responsePlus :=
    ttResponsePlus coupling omega waveNumber sourcePlus sourceMinus
  let responseMinus :=
    ttResponseMinus coupling omega waveNumber sourcePlus sourceMinus
  have hDifferencePlus :
      ttEquationPlus coupling omega waveNumber
          (hPlus - responsePlus) (hMinus - responseMinus) = 0 := by
    simp [ttEquationPlus, linearizedEinsteinSymbol_tt_component,
      responsePlus, responseMinus] at hPlusEquation hResponse ⊢
    linarith [hResponse.1]
  have hDifferenceMinus :
      ttEquationMinus coupling omega waveNumber
          (hPlus - responsePlus) (hMinus - responseMinus) = 0 := by
    simp [ttEquationMinus, linearizedEinsteinSymbol_tt_component,
      responsePlus, responseMinus] at hMinusEquation hResponse ⊢
    linarith [hResponse.2]
  have hTrivial := off_shell_tt_kernel_is_trivial coupling omega waveNumber
    (hPlus - responsePlus) (hMinus - responseMinus)
    hDifferencePlus hDifferenceMinus hNotMassless hNotMassive
  dsimp [responsePlus, responseMinus] at hTrivial ⊢
  constructor <;> linarith

/-- On the massless shell and for nonzero coupling, every solution is the
common mode `hPlus = hMinus`. -/
theorem massless_shell_kernel_is_common
    (coupling omega waveNumber hPlus hMinus : ℝ)
    (hCoupling : coupling ≠ 0)
    (hDispersion : omega ^ 2 = waveNumber ^ 2)
    (hPlusEquation :
      ttEquationPlus coupling omega waveNumber hPlus hMinus = 0)
    (hMinusEquation :
      ttEquationMinus coupling omega waveNumber hPlus hMinus = 0) :
    hPlus = hMinus := by
  have hDiagonal :=
    tt_equation_pair_diagonalization coupling omega waveNumber hPlus hMinus
  have hProduct :
      (ttKineticEigenvalue omega waveNumber - 2 * coupling) *
          (hPlus - hMinus) = 0 := by
    rw [← hDiagonal.2, hPlusEquation, hMinusEquation]
    ring
  have hEigenvalue :
      ttKineticEigenvalue omega waveNumber - 2 * coupling ≠ 0 := by
    simp [ttKineticEigenvalue, hDispersion, hCoupling]
  have := (mul_eq_zero.mp hProduct).resolve_left hEigenvalue
  linarith

/-- On the massive shell and for nonzero coupling, every solution is the
relative mode `hPlus = -hMinus`. -/
theorem massive_shell_kernel_is_relative
    (coupling omega waveNumber hPlus hMinus : ℝ)
    (hCoupling : coupling ≠ 0)
    (hDispersion : omega ^ 2 = waveNumber ^ 2 + 4 * coupling)
    (hPlusEquation :
      ttEquationPlus coupling omega waveNumber hPlus hMinus = 0)
    (hMinusEquation :
      ttEquationMinus coupling omega waveNumber hPlus hMinus = 0) :
    hPlus = -hMinus := by
  have hDiagonal :=
    tt_equation_pair_diagonalization coupling omega waveNumber hPlus hMinus
  have hProduct :
      ttKineticEigenvalue omega waveNumber * (hPlus + hMinus) = 0 := by
    rw [← hDiagonal.1, hPlusEquation, hMinusEquation]
    ring
  have hEigenvalue : ttKineticEigenvalue omega waveNumber ≠ 0 := by
    simp [ttKineticEigenvalue, hDispersion, hCoupling]
  have := (mul_eq_zero.mp hProduct).resolve_left hEigenvalue
  linarith

/-- Positive coupling gives a strict homogeneous mass gap in the relative
TT channel. -/
theorem positive_coupling_relative_mass_gap
    (coupling omega waveNumber : ℝ)
    (hCoupling : 0 < coupling)
    (hDispersion : omega ^ 2 = waveNumber ^ 2 + 4 * coupling) :
    0 < omega ^ 2 ∧ omega ≠ 0 := by
  have hPositive : 0 < omega ^ 2 := by
    nlinarith [sq_nonneg waveNumber]
  refine ⟨hPositive, ?_⟩
  intro hOmega
  rw [hOmega] at hPositive
  norm_num at hPositive

/-- Negative coupling creates a low-wave-number band with no real relative
frequency, the precise tachyonic obstruction in this reduced TT model. -/
theorem negative_coupling_low_momentum_has_no_real_frequency
    (coupling waveNumber : ℝ)
    (hBand : waveNumber ^ 2 + 4 * coupling < 0) :
    ¬ ∃ omega : ℝ, omega ^ 2 = waveNumber ^ 2 + 4 * coupling := by
  rintro ⟨omega, hDispersion⟩
  nlinarith [sq_nonneg omega]

end
end JanusPTTExactKernelClassification
end JanusFormal
