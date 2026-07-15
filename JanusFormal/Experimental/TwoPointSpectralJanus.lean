import Mathlib

/-!
# Experimental two-point spectral Janus seed

This file is intentionally not imported by any supported Janus program head.
It tests whether a two-point internal geometry can generate a reciprocal
two-sector coupling from one off-diagonal operator.
-/

namespace JanusFormal
namespace ExperimentalTwoPointSpectralJanus

set_option autoImplicit false

noncomputable section

abbrev TwoByTwo := Matrix (Fin 2) (Fin 2) ℝ

/-- Representation of the algebra `ℝ ⊕ ℝ` on the two-sheet internal space. -/
def represent (plus minus : ℝ) : TwoByTwo :=
  !![plus, 0; 0, minus]

/-- Odd finite Dirac/link operator between the two sheets. -/
def linkDirac (link : ℝ) : TwoByTwo :=
  !![0, link; link, 0]

/-- Grading that distinguishes the two sheets. -/
def grading : TwoByTwo :=
  !![1, 0; 0, -1]

def commutator (first second : TwoByTwo) : TwoByTwo :=
  first * second - second * first

def anticommutator (first second : TwoByTwo) : TwoByTwo :=
  first * second + second * first

/-- The link operator is odd for the sheet grading. -/
theorem grading_anticommutes_linkDirac (link : ℝ) :
    anticommutator grading (linkDirac link) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [anticommutator, grading, linkDirac]

/-- Squared Frobenius magnitude of a real two-by-two matrix. -/
def frobeniusSquare (matrix : TwoByTwo) : ℝ :=
  ∑ i, ∑ j, (matrix i j) ^ 2

/-- The commutator with the finite Dirac operator measures only the difference
between the two sheet values. -/
theorem commutator_energy_formula (link plus minus : ℝ) :
    frobeniusSquare (commutator (linkDirac link) (represent plus minus)) =
      2 * link ^ 2 * (plus - minus) ^ 2 := by
  simp [frobeniusSquare, commutator, linkDirac, represent, Fin.sum_univ_two]
  ring

/-- Minimal action induced by the two-point spectral commutator. -/
def spectralLinkAction (link plus minus : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ *
    frobeniusSquare (commutator (linkDirac link) (represent plus minus))

theorem spectralLinkAction_formula (link plus minus : ℝ) :
    spectralLinkAction link plus minus =
      link ^ 2 * (plus - minus) ^ 2 := by
  rw [spectralLinkAction, commutator_energy_formula]
  ring

/-- Sheet exchange is an exact symmetry of the induced action. -/
theorem spectralLinkAction_exchange (link plus minus : ℝ) :
    spectralLinkAction link plus minus =
      spectralLinkAction link minus plus := by
  rw [spectralLinkAction_formula, spectralLinkAction_formula]
  ring

/-- Plus-sheet Euler coefficient in the scalar reduction. -/
def eulerPlus (link plus minus : ℝ) : ℝ :=
  2 * link ^ 2 * (plus - minus)

/-- Minus-sheet Euler coefficient in the scalar reduction. -/
def eulerMinus (link plus minus : ℝ) : ℝ :=
  -2 * link ^ 2 * (plus - minus)

/-- Exact first-order plus variation with its quadratic remainder. -/
theorem spectralLinkAction_plus_variation
    (link plus minus variation : ℝ) :
    spectralLinkAction link (plus + variation) minus -
        spectralLinkAction link plus minus =
      eulerPlus link plus minus * variation + link ^ 2 * variation ^ 2 := by
  rw [spectralLinkAction_formula, spectralLinkAction_formula]
  simp [eulerPlus]
  ring

/-- Exact first-order minus variation with its quadratic remainder. -/
theorem spectralLinkAction_minus_variation
    (link plus minus variation : ℝ) :
    spectralLinkAction link plus (minus + variation) -
        spectralLinkAction link plus minus =
      eulerMinus link plus minus * variation + link ^ 2 * variation ^ 2 := by
  rw [spectralLinkAction_formula, spectralLinkAction_formula]
  simp [eulerMinus]
  ring

/-- Diagonal shifts have zero exchange current. -/
theorem diagonal_noether_identity (link plus minus : ℝ) :
    eulerPlus link plus minus + eulerMinus link plus minus = 0 := by
  simp [eulerPlus, eulerMinus]

/-- A nonzero link locks the stationary scalar branch to equal sheet values. -/
theorem stationary_iff_equal_sheets
    (link plus minus : ℝ) (hLink : link ≠ 0) :
    (eulerPlus link plus minus = 0 ∧
      eulerMinus link plus minus = 0) ↔
      plus = minus := by
  constructor
  · rintro ⟨hPlus, _⟩
    simp [eulerPlus, hLink] at hPlus
    exact sub_eq_zero.mp hPlus
  · intro hEqual
    subst minus
    simp [eulerPlus, eulerMinus]

/-- Distinct link magnitudes give distinct exchange-symmetric actions.  The
two-point geometry therefore generates a coupling shape but not its scale. -/
theorem link_scale_not_selected
    (firstLink secondLink : ℝ)
    (hDistinct : firstLink ^ 2 ≠ secondLink ^ 2) :
    spectralLinkAction firstLink ≠ spectralLinkAction secondLink := by
  intro hEqual
  have hAtPoint := congrFun (congrFun hEqual 1) 0
  rw [spectralLinkAction_formula, spectralLinkAction_formula] at hAtPoint
  norm_num at hAtPoint
  exact hDistinct hAtPoint

end

end ExperimentalTwoPointSpectralJanus
end JanusFormal
