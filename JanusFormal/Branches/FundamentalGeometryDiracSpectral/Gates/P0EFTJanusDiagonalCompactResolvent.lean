import Mathlib.Analysis.Normed.Operator.Compact.Basic
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusInfiniteL2DiracDomain

namespace JanusFormal
namespace P0EFTJanusDiagonalCompactResolvent

set_option autoImplicit false

open scoped ENNReal lp
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusInfiniteL2DiracDomain

noncomputable section

def diagonalMultiplierLinearMap (multiplier : ProductDiracMode → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1) :
    ComplexProductModeHilbert →ₗ[ℂ] ComplexProductModeHilbert where
  toFun φ := ⟨fun mode => multiplier mode * φ mode, by
    refine φ.2.mono' ?_
    intro mode
    simpa using mul_le_mul_of_nonneg_right (hBound mode) (norm_nonneg (φ mode))⟩
  map_add' := by
    intro φ ψ
    ext mode
    simp [mul_add]
  map_smul' := by
    intro c φ
    ext mode
    simp [mul_left_comm]

noncomputable def diagonalMultiplierCLM (multiplier : ProductDiracMode → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1) :
    ComplexProductModeHilbert →L[ℂ] ComplexProductModeHilbert :=
  (diagonalMultiplierLinearMap multiplier hBound).mkContinuous 1 (by
    intro φ
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
    intro mode
    change ‖multiplier mode * φ mode‖ ≤ ‖φ mode‖
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (hBound mode) (norm_nonneg (φ mode)))

@[simp] theorem diagonal_multiplier_clm_apply
    (multiplier : ProductDiracMode → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (φ : ComplexProductModeHilbert) (mode : ProductDiracMode) :
    diagonalMultiplierCLM multiplier hBound φ mode = multiplier mode * φ mode := rfl

def coordinateRankOne (mode : ProductDiracMode) :
    ComplexProductModeHilbert →L[ℂ] ComplexProductModeHilbert :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ProductDiracMode => ℂ) 2 mode).comp
    (lp.evalCLM ℂ (fun _ : ProductDiracMode => ℂ) 2 mode)

theorem coordinate_rank_one_compact (mode : ProductDiracMode) :
    IsCompactOperator (coordinateRankOne mode) := by
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (lp.evalCLM ℂ (fun _ : ProductDiracMode => ℂ) 2 mode)).clm_comp
      (lp.singleContinuousLinearMap ℂ (fun _ : ProductDiracMode => ℂ) 2 mode)

def finiteDiagonalTruncation (multiplier : ProductDiracMode → ℂ)
    (modes : Finset ProductDiracMode) :
    ComplexProductModeHilbert →L[ℂ] ComplexProductModeHilbert :=
  ∑ mode ∈ modes, multiplier mode • coordinateRankOne mode

@[simp] theorem finite_diagonal_truncation_apply
    (multiplier : ProductDiracMode → ℂ) (modes : Finset ProductDiracMode)
    (φ : ComplexProductModeHilbert) (mode : ProductDiracMode) :
    finiteDiagonalTruncation multiplier modes φ mode =
      if mode ∈ modes then multiplier mode * φ mode else 0 := by
  classical
  induction modes using Finset.induction_on with
  | empty => simp [finiteDiagonalTruncation]
  | @insert inserted modes hInserted hInduction =>
      rw [finiteDiagonalTruncation, Finset.sum_insert hInserted]
      change multiplier inserted *
          (lp.single 2 inserted (φ inserted) : ComplexProductModeHilbert) mode +
          finiteDiagonalTruncation multiplier modes φ mode = _
      by_cases hMode : mode = inserted
      · subst mode
        rw [hInduction]
        simp [hInserted]
      · rw [lp.single_apply_ne (E := fun _ : ProductDiracMode => ℂ)
          2 inserted (φ inserted) hMode, mul_zero, zero_add, hInduction]
        simp [hMode]

theorem finite_diagonal_truncation_compact (multiplier : ProductDiracMode → ℂ)
    (modes : Finset ProductDiracMode) :
    IsCompactOperator (finiteDiagonalTruncation multiplier modes) := by
  induction modes using Finset.induction_on with
  | empty =>
      simp [finiteDiagonalTruncation]
      exact isCompactOperator_zero
  | @insert mode modes hMode hInduction =>
      rw [finiteDiagonalTruncation, Finset.sum_insert hMode]
      exact ((coordinate_rank_one_compact mode).smul (multiplier mode)).add hInduction

theorem diagonal_sub_finite_truncation_norm_le
    (multiplier : ProductDiracMode → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (modes : Finset ProductDiracMode) (ε : ℝ) (hε : 0 ≤ ε)
    (hTail : ∀ mode, mode ∉ modes → ‖multiplier mode‖ ≤ ε) :
    ‖diagonalMultiplierCLM multiplier hBound - finiteDiagonalTruncation multiplier modes‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro φ
  rw [← show ‖(ε : ℂ) • φ‖ = ε * ‖φ‖ by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε] using
      (norm_smul (ε : ℂ) φ)]
  apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
  intro mode
  change ‖multiplier mode * φ mode -
      finiteDiagonalTruncation multiplier modes φ mode‖ ≤ ‖(ε : ℂ) • φ mode‖
  by_cases hMode : mode ∈ modes
  · simp [hMode]
    positivity
  · rw [finite_diagonal_truncation_apply, if_neg hMode, sub_zero,
      norm_mul, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_right (hTail mode hMode) (norm_nonneg (φ mode))

noncomputable def decayTruncationModes
    (multiplier : ProductDiracMode → ℂ)
    (hDecay : DiagonalMultiplierVanishesAtInfinity multiplier) (n : ℕ) :
    Finset ProductDiracMode :=
  (hDecay (1 / ((n : ℝ) + 1)) (by positivity)).toFinset

theorem norm_finite_decay_truncation_sub_diagonal_le
    (multiplier : ProductDiracMode → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (hDecay : DiagonalMultiplierVanishesAtInfinity multiplier) (n : ℕ) :
    ‖finiteDiagonalTruncation multiplier (decayTruncationModes multiplier hDecay n) -
        diagonalMultiplierCLM multiplier hBound‖ ≤ 1 / ((n : ℝ) + 1) := by
  rw [norm_sub_rev]
  apply diagonal_sub_finite_truncation_norm_le
  · positivity
  · intro mode hMode
    have hNotSuperlevel : mode ∉
        {mode | 1 / ((n : ℝ) + 1) ≤ ‖multiplier mode‖} := by
      simpa [decayTruncationModes] using hMode
    exact le_of_lt (not_le.1 hNotSuperlevel)

/-- A bounded diagonal multiplier vanishing at infinity is an actual compact operator. -/
theorem diagonal_multiplier_compact_of_vanishes_at_infinity
    (multiplier : ProductDiracMode → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (hDecay : DiagonalMultiplierVanishesAtInfinity multiplier) :
    IsCompactOperator (diagonalMultiplierCLM multiplier hBound) := by
  apply isCompactOperator_of_tendsto (l := Filter.atTop)
    (F := fun n : ℕ => finiteDiagonalTruncation multiplier
      (decayTruncationModes multiplier hDecay n))
    (f := diagonalMultiplierCLM multiplier hBound)
  · apply tendsto_iff_norm_sub_tendsto_zero.2
    exact squeeze_zero (fun n => norm_nonneg _)
      (norm_finite_decay_truncation_sub_diagonal_le multiplier hBound hDecay)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Filter.Eventually.of_forall fun n =>
      finite_diagonal_truncation_compact multiplier
        (decayTruncationModes multiplier hDecay n)

theorem shift_I_resolvent_multiplier_norm_le_one
    (weight : ProductDiracMode → ℝ) (mode : ProductDiracMode) :
    ‖shiftIResolventMultiplier weight mode‖ ≤ 1 := by
  unfold shiftIResolventMultiplier
  rw [norm_div, norm_one]
  have hDenPos : 0 < ‖(weight mode : ℂ) - Complex.I‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_real_sub_I (weight mode))
  apply (div_le_iff₀ hDenPos).2
  simpa using one_le_norm_real_sub_I (weight mode)

noncomputable def shiftIResolventCLM (weight : ProductDiracMode → ℝ) :
    ComplexProductModeHilbert →L[ℂ] ComplexProductModeHilbert :=
  diagonalMultiplierCLM (shiftIResolventMultiplier weight)
    (shift_I_resolvent_multiplier_norm_le_one weight)

@[simp] theorem shift_I_resolvent_clm_apply
    (weight : ProductDiracMode → ℝ) (φ : ComplexProductModeHilbert) :
    shiftIResolventCLM weight φ = complexShiftIInverse weight φ := by
  ext mode
  change shiftIResolventMultiplier weight mode * φ mode =
    complexShiftIInverse weight φ mode
  exact (complex_shift_I_inverse_is_diagonal_multiplier weight φ mode).symm

/-- Proper separated eigenvalue growth gives an actual compact `(D-i)⁻¹`. -/
theorem shift_I_resolvent_compact_of_proper
    (weight : ProductDiracMode → ℝ) (hProper : ProperDiagonalWeight weight) :
    IsCompactOperator (shiftIResolventCLM weight) :=
  diagonal_multiplier_compact_of_vanishes_at_infinity
    (shiftIResolventMultiplier weight)
    (shift_I_resolvent_multiplier_norm_le_one weight)
    (shift_I_multiplier_vanishes_at_infinity weight hProper)

end

end P0EFTJanusDiagonalCompactResolvent
end JanusFormal
