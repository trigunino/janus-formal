import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Circle Fourier--Dirac heat-trace cancellation

This gate replaces an arbitrary finite list of squared eigenvalues by the
explicit Fourier spectrum of a diagonal first-order circle model.  For an
integer mode `n` and a twist `a` in `[0,1]`, the positive-fold eigenvalue is
`n + a`; the PT fold has eigenvalue `-(n + a)`.  The squared spectrum is
therefore derived from the displayed eigenvalue and is identical on both
folds.

For every strictly positive heat time, the Gaussian weights are summable on
`Z`.  Symmetric Fourier cutoffs converge to the corresponding `tsum`, and
the two foldwise chiral summands cancel mode by mode and after summation.

The diagonal action below is an algebraic linear action on Fourier
coefficients.  No Hilbert-space domain, self-adjoint unbounded operator,
local heat-kernel coefficient, determinant line, or complete continuum
Dirac anomaly is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCircleDiracHeatTraceCancellation

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

/-- Holonomy/twist representative in one fundamental interval. -/
structure CircleTwist where
  value : ℝ
  nonnegative : 0 ≤ value
  le_one : value ≤ 1

/-- Strictly positive heat-kernel regulator time. -/
abbrev HeatTime := {time : ℝ // 0 < time}

/-- The two PT-related Fourier folds. -/
inductive Fold where
  | positive
  | pt
  deriving DecidableEq

/-- Sign of the first-order diagonal eigenvalue. -/
def Fold.spectralSign : Fold → ℝ
  | .positive => 1
  | .pt => -1

/-- Chirality sign carried by the two folds. -/
def Fold.chirality : Fold → ℝ
  | .positive => 1
  | .pt => -1

@[simp]
theorem Fold.positive_spectralSign : Fold.positive.spectralSign = 1 := rfl

@[simp]
theorem Fold.pt_spectralSign : Fold.pt.spectralSign = -1 := rfl

@[simp]
theorem Fold.positive_chirality : Fold.positive.chirality = 1 := rfl

@[simp]
theorem Fold.pt_chirality : Fold.pt.chirality = -1 := rfl

/-- Untwisted periodic spectrum. -/
def periodicTwist : CircleTwist where
  value := 0
  nonnegative := le_rfl
  le_one := zero_le_one

/-- Antiperiodic half-integer spectrum. -/
def antiperiodicTwist : CircleTwist where
  value := 1 / 2
  nonnegative := by norm_num
  le_one := by norm_num

/-- Positive-fold Fourier eigenvalue `n + a`. -/
def baseEigenvalue (twist : CircleTwist) (mode : ℤ) : ℝ :=
  (mode : ℝ) + twist.value

/-- Foldwise first-order Dirac eigenvalue. -/
def diracEigenvalue (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℝ :=
  fold.spectralSign * baseEigenvalue twist mode

/-- The squared eigenvalue is derived, not supplied. -/
def eigenvalueSq (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℝ :=
  (diracEigenvalue fold twist mode) ^ 2

@[simp]
theorem positive_diracEigenvalue (twist : CircleTwist) (mode : ℤ) :
    diracEigenvalue .positive twist mode = baseEigenvalue twist mode := by
  simp [diracEigenvalue]

@[simp]
theorem pt_diracEigenvalue (twist : CircleTwist) (mode : ℤ) :
    diracEigenvalue .pt twist mode = -baseEigenvalue twist mode := by
  simp [diracEigenvalue]

/-- PT reverses the first-order eigenvalue. -/
theorem pt_diracEigenvalue_eq_neg_positive
    (twist : CircleTwist) (mode : ℤ) :
    diracEigenvalue .pt twist mode =
      -diracEigenvalue .positive twist mode := by
  simp

/-- Both folds have the same derived squared spectrum. -/
@[simp]
theorem pt_eigenvalueSq_eq_positive
    (twist : CircleTwist) (mode : ℤ) :
    eigenvalueSq .pt twist mode = eigenvalueSq .positive twist mode := by
  simp [eigenvalueSq]

/-- Nonnegativity follows from the derived square. -/
theorem eigenvalueSq_nonnegative
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    0 ≤ eigenvalueSq fold twist mode := by
  exact sq_nonneg _

/-- Algebraic Fourier coefficient space.  No square-summability domain is
imposed in this local spectral gate. -/
abbrev FourierState := ℤ → ℝ

/-- Diagonal first-order action on Fourier coefficients. -/
def circleDiracAction
    (fold : Fold) (twist : CircleTwist) : FourierState →ₗ[ℝ] FourierState where
  toFun := fun state mode => diracEigenvalue fold twist mode * state mode
  map_add' := by
    intro first second
    funext mode
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro scalar state
    funext mode
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem circleDiracAction_apply
    (fold : Fold) (twist : CircleTwist)
    (state : FourierState) (mode : ℤ) :
    circleDiracAction fold twist state mode =
      diracEigenvalue fold twist mode * state mode := by
  rfl

/-- On every Fourier coefficient the PT action is the negative of the
positive-fold action. -/
theorem circleDiracAction_pt_eq_neg_positive
    (twist : CircleTwist) (state : FourierState) :
    circleDiracAction .pt twist state =
      -circleDiracAction .positive twist state := by
  ext mode
  simp [circleDiracAction_apply]

/-- Derived Gaussian heat weight. -/
def heatWeight
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℝ :=
  Real.exp (-time.1 * eigenvalueSq fold twist mode)

/-- Auxiliary positive-tail estimate for twists in `[0,1]`. -/
theorem natCast_le_positive_shift_square
    (twist : CircleTwist) (mode : ℕ) :
    (mode : ℝ) ≤ ((mode : ℝ) + twist.value) ^ 2 := by
  by_cases hMode : mode = 0
  · subst mode
    simp only [Nat.cast_zero, zero_add]
    exact sq_nonneg _
  · have hModeOne : (1 : ℝ) ≤ (mode : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hMode)
    have hShiftNonnegative : 0 ≤ (mode : ℝ) + twist.value :=
      add_nonneg (Nat.cast_nonneg mode) twist.nonnegative
    have hShiftOne : 1 ≤ (mode : ℝ) + twist.value := by
      linarith [twist.nonnegative]
    have hModeLeShift : (mode : ℝ) ≤ (mode : ℝ) + twist.value := by
      linarith [twist.nonnegative]
    have hProduct := mul_nonneg hShiftNonnegative
      (sub_nonneg.mpr hShiftOne)
    nlinarith [hProduct, hModeLeShift]

/-- Auxiliary negative-tail estimate after removing two initial modes. -/
theorem natCast_le_negative_shift_tail_square
    (twist : CircleTwist) (mode : ℕ) :
    (mode : ℝ) ≤
      (twist.value - ((mode + 2 : ℕ) : ℝ)) ^ 2 := by
  have hModeNonnegative : 0 ≤ (mode : ℝ) := Nat.cast_nonneg mode
  have hLower : (mode : ℝ) + 1 ≤
      ((mode + 2 : ℕ) : ℝ) - twist.value := by
    norm_num [Nat.cast_add]
    linarith [twist.le_one]
  have hShiftNonnegative :
      0 ≤ ((mode + 2 : ℕ) : ℝ) - twist.value := by
    linarith
  have hShiftOne :
      1 ≤ ((mode + 2 : ℕ) : ℝ) - twist.value := by
    linarith
  have hProduct := mul_nonneg hShiftNonnegative
    (sub_nonneg.mpr hShiftOne)
  nlinarith [hProduct]

/-- Positive integer Fourier modes have a summable Gaussian tail. -/
theorem heatWeight_positive_nat_summable
    (time : HeatTime) (twist : CircleTwist) :
    Summable (fun mode : ℕ =>
      heatWeight time .positive twist (mode : ℤ)) := by
  have hGaussian : Summable (fun mode : ℕ =>
      Real.exp ((-time.1) * (((mode : ℝ) + twist.value) ^ 2))) :=
    Real.summable_exp_nat_mul_of_ge (c := -time.1)
      (neg_lt_zero.mpr time.2)
      (natCast_le_positive_shift_square twist)
  simpa [heatWeight, eigenvalueSq, diracEigenvalue, baseEigenvalue] using
    hGaussian

/-- Negative integer Fourier modes have a summable Gaussian tail. -/
theorem heatWeight_negative_nat_summable
    (time : HeatTime) (twist : CircleTwist) :
    Summable (fun mode : ℕ =>
      heatWeight time .positive twist (-(mode : ℤ))) := by
  have hGaussian : Summable (fun mode : ℕ =>
      Real.exp ((-time.1) *
        ((twist.value - ((mode + 2 : ℕ) : ℝ)) ^ 2))) :=
    Real.summable_exp_nat_mul_of_ge (c := -time.1)
      (neg_lt_zero.mpr time.2)
      (natCast_le_negative_shift_tail_square twist)
  have hTail : Summable (fun mode : ℕ =>
      heatWeight time .positive twist (-((mode + 2 : ℕ) : ℤ))) := by
    refine hGaussian.congr (fun mode => ?_)
    simp [heatWeight, eigenvalueSq, diracEigenvalue, baseEigenvalue,
      Nat.cast_add]
    ring_nf
    simp
  exact (summable_nat_add_iff 2).mp hTail

/-- The explicit circle Gaussian is summable over all integer modes. -/
theorem heatWeight_positive_summable
    (time : HeatTime) (twist : CircleTwist) :
    Summable (heatWeight time .positive twist) := by
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨heatWeight_positive_nat_summable time twist,
    heatWeight_negative_nat_summable time twist⟩

/-- PT isospectrality transfers Gaussian summability to the partner fold. -/
theorem heatWeight_pt_summable
    (time : HeatTime) (twist : CircleTwist) :
    Summable (heatWeight time .pt twist) := by
  refine (heatWeight_positive_summable time twist).congr (fun mode => ?_)
  simp [heatWeight, eigenvalueSq, diracEigenvalue]

theorem heatWeight_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (heatWeight time fold twist) := by
  cases fold with
  | positive => exact heatWeight_positive_summable time twist
  | pt => exact heatWeight_pt_summable time twist

/-- Infinite parity-even heat trace. -/
def evenHeatTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : ℝ :=
  tsum (heatWeight time fold twist)

/-- Infinite chiral heat summand. -/
def chiralHeatSummand
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℝ :=
  fold.chirality * heatWeight time fold twist mode

theorem chiralHeatSummand_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (chiralHeatSummand time fold twist) := by
  exact (heatWeight_summable time fold twist).mul_left fold.chirality

/-- Infinite regulated chiral trace. -/
def regulatedChiralTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : ℝ :=
  tsum (chiralHeatSummand time fold twist)

/-- PT cancellation already holds mode by mode. -/
theorem chiralHeatSummand_positive_add_pt_eq_zero
    (time : HeatTime) (twist : CircleTwist) (mode : ℤ) :
    chiralHeatSummand time .positive twist mode +
      chiralHeatSummand time .pt twist mode = 0 := by
  simp [chiralHeatSummand, heatWeight]

/-- The PT partner reverses the convergent chiral trace. -/
theorem regulatedChiralTrace_pt_eq_neg_positive
    (time : HeatTime) (twist : CircleTwist) :
    regulatedChiralTrace time .pt twist =
      -regulatedChiralTrace time .positive twist := by
  rw [regulatedChiralTrace, regulatedChiralTrace]
  calc
    tsum (chiralHeatSummand time .pt twist) =
        tsum (fun mode => -chiralHeatSummand time .positive twist mode) := by
      congr 1
      funext mode
      have h := chiralHeatSummand_positive_add_pt_eq_zero time twist mode
      linarith
    _ = -tsum (chiralHeatSummand time .positive twist) := by
      exact tsum_neg

/-- Paired convergent chiral trace. -/
def pairedRegulatedChiralTrace
    (time : HeatTime) (twist : CircleTwist) : ℝ :=
  regulatedChiralTrace time .positive twist +
    regulatedChiralTrace time .pt twist

theorem pairedRegulatedChiralTrace_eq_zero
    (time : HeatTime) (twist : CircleTwist) :
    pairedRegulatedChiralTrace time twist = 0 := by
  rw [pairedRegulatedChiralTrace, regulatedChiralTrace_pt_eq_neg_positive]
  ring

/-- PT preserves the convergent parity-even heat trace. -/
theorem evenHeatTrace_pt_eq_positive
    (time : HeatTime) (twist : CircleTwist) :
    evenHeatTrace time .pt twist = evenHeatTrace time .positive twist := by
  unfold evenHeatTrace
  apply tsum_congr
  intro mode
  simp [heatWeight]

/-- Symmetric integer Fourier cutoff. -/
def symmetricCutoff (cutoff : ℕ) : Finset ℤ :=
  Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)

/-- Finite even heat trace at symmetric cutoff. -/
def cutoffEvenHeatTrace
    (cutoff : ℕ) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) : ℝ :=
  ∑ mode ∈ symmetricCutoff cutoff, heatWeight time fold twist mode

/-- Finite chiral heat trace at symmetric cutoff. -/
def cutoffChiralHeatTrace
    (cutoff : ℕ) (time : HeatTime) (fold : Fold)
    (twist : CircleTwist) : ℝ :=
  ∑ mode ∈ symmetricCutoff cutoff, chiralHeatSummand time fold twist mode

/-- Symmetric finite cutoffs converge to the infinite even heat trace. -/
theorem cutoffEvenHeatTrace_tendsto
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Tendsto (fun cutoff => cutoffEvenHeatTrace cutoff time fold twist)
      Filter.atTop (𝓝 (evenHeatTrace time fold twist)) := by
  change Tendsto
    ((fun modes : Finset ℤ =>
      ∑ mode ∈ modes, heatWeight time fold twist mode) ∘
        fun cutoff : ℕ => Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))
    Filter.atTop (𝓝 (tsum (heatWeight time fold twist)))
  exact (heatWeight_summable time fold twist).hasSum.comp
    (Finset.tendsto_Icc_neg (R := ℤ))

/-- Symmetric finite cutoffs converge to the infinite chiral trace. -/
theorem cutoffChiralHeatTrace_tendsto
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Tendsto (fun cutoff => cutoffChiralHeatTrace cutoff time fold twist)
      Filter.atTop (𝓝 (regulatedChiralTrace time fold twist)) := by
  change Tendsto
    ((fun modes : Finset ℤ =>
      ∑ mode ∈ modes, chiralHeatSummand time fold twist mode) ∘
        fun cutoff : ℕ => Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))
    Filter.atTop (𝓝 (tsum (chiralHeatSummand time fold twist)))
  exact (chiralHeatSummand_summable time fold twist).hasSum.comp
    (Finset.tendsto_Icc_neg (R := ℤ))

/-- PT cancellation also holds at every finite symmetric cutoff. -/
theorem cutoffChiralHeatTrace_positive_add_pt_eq_zero
    (cutoff : ℕ) (time : HeatTime) (twist : CircleTwist) :
    cutoffChiralHeatTrace cutoff time .positive twist +
      cutoffChiralHeatTrace cutoff time .pt twist = 0 := by
  rw [cutoffChiralHeatTrace, cutoffChiralHeatTrace, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro mode hMode
  exact chiralHeatSummand_positive_add_pt_eq_zero time twist mode

end

end P0EFTJanusCircleDiracHeatTraceCancellation
end JanusFormal
