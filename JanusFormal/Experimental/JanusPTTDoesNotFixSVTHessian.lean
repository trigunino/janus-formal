import JanusFormal.Experimental.JanusPTTPolarizationPlane

namespace JanusFormal
namespace JanusPTTDoesNotFixSVTHessian

set_option autoImplicit false

noncomputable section

open JanusPLinearizedEinsteinTTDispersion
open JanusPTTPolarizationPlane
open P0EFTJanusLinearizedEinsteinBianchiSymbol

/-- A quadratic deformation supported only on the lapse-like `h₀₀` entry. -/
def scalarInvisibleOnTT
    (coefficient : ℝ) (perturbation : SymmetricPerturbation) : ℝ :=
  coefficient * perturbation.tensor 0 0 ^ 2

/-- A quadratic deformation supported only on a shift-like `h₀₁` entry. -/
def vectorInvisibleOnTT
    (coefficient : ℝ) (perturbation : SymmetricPerturbation) : ℝ :=
  coefficient * perturbation.tensor 0 1 ^ 2

def lapsePolarization (amplitude : ℝ) : SymmetricPerturbation where
  tensor := fun first second =>
    if first = 0 ∧ second = 0 then amplitude else 0
  tensor_symmetric := by
    ext first second
    fin_cases first <;> fin_cases second <;>
      simp [Matrix.transpose_apply]

def shiftPolarization (amplitude : ℝ) : SymmetricPerturbation where
  tensor := fun first second =>
    if (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0)
    then amplitude else 0
  tensor_symmetric := by
    ext first second
    fin_cases first <;> fin_cases second <;>
      simp [Matrix.transpose_apply]

/-- Both independent TT polarizations are blind to arbitrary lapse-sector
quadratic coefficients. -/
theorem scalar_deformation_vanishes_on_all_tt
    (coefficient plus cross : ℝ) :
    scalarInvisibleOnTT coefficient (ttPlusPolarization plus) = 0 ∧
      scalarInvisibleOnTT coefficient (ttPolarization cross) = 0 := by
  simp [scalarInvisibleOnTT, ttPlusPolarization, ttPolarization]

/-- Both independent TT polarizations are also blind to arbitrary shift-sector
quadratic coefficients. -/
theorem vector_deformation_vanishes_on_all_tt
    (coefficient plus cross : ℝ) :
    vectorInvisibleOnTT coefficient (ttPlusPolarization plus) = 0 ∧
      vectorInvisibleOnTT coefficient (ttPolarization cross) = 0 := by
  simp [vectorInvisibleOnTT, ttPlusPolarization, ttPolarization]

theorem scalar_deformation_detects_lapse
    (coefficient amplitude : ℝ) :
    scalarInvisibleOnTT coefficient (lapsePolarization amplitude) =
      coefficient * amplitude ^ 2 := by
  simp [scalarInvisibleOnTT, lapsePolarization]

theorem vector_deformation_detects_shift
    (coefficient amplitude : ℝ) :
    vectorInvisibleOnTT coefficient (shiftPolarization amplitude) =
      coefficient * amplitude ^ 2 := by
  simp [vectorInvisibleOnTT, shiftPolarization]

/-- Agreement on the complete TT plane does not determine the scalar
quadratic extension. -/
theorem same_tt_distinct_scalar_extension
    (firstCoefficient secondCoefficient amplitude : ℝ)
    (hDifferent : firstCoefficient ≠ secondCoefficient)
    (hAmplitude : amplitude ≠ 0) :
    scalarInvisibleOnTT firstCoefficient (lapsePolarization amplitude) ≠
      scalarInvisibleOnTT secondCoefficient (lapsePolarization amplitude) := by
  rw [scalar_deformation_detects_lapse,
    scalar_deformation_detects_lapse]
  intro hEqual
  apply hDifferent
  have hPositive : 0 < amplitude ^ 2 := sq_pos_of_ne_zero hAmplitude
  nlinarith

end
end JanusPTTDoesNotFixSVTHessian
end JanusFormal
