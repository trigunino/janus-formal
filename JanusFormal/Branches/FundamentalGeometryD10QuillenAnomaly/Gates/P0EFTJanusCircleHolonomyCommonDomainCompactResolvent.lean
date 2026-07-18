import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleUnboundedDiracDomain
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Common-domain holonomy family and compact circle resolvent

This gate stays on the normalized Fourier circle.  It proves that all real
holonomies have the same maximal domain, realizes holonomy variation as a
bounded scalar perturbation on that domain, complexifies it to an affine
holomorphic family, and constructs the compact Fourier resolvent `(D-i)⁻¹`.

It is not the global Janus operator, a families-index theorem, or a Quillen
construction.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHolonomyCommonDomainCompactResolvent

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open scoped ContDiff ENNReal lp

/-- Complex scalar by which changing the twist perturbs the circle Dirac operator. -/
def holonomyShift (fold : Fold) (first second : CircleTwist) : ℂ :=
  (fold.spectralSign * (second.value - first.value) : ℝ)

theorem complexDiracEigenvalue_add_holonomyShift
    (fold : Fold) (first second : CircleTwist) (mode : ℤ) :
    complexDiracEigenvalue fold second mode =
      complexDiracEigenvalue fold first mode + holonomyShift fold first second := by
  cases fold
  · simp [complexDiracEigenvalue, diracEigenvalue, baseEigenvalue,
      holonomyShift]
  · simp [complexDiracEigenvalue, diracEigenvalue, baseEigenvalue,
      holonomyShift]
    ring_nf

/-- A bounded scalar perturbation preserves membership in the maximal domain. -/
theorem circleDiracDomain_mono_holonomy
    (fold : Fold) (first second : CircleTwist) :
    circleDiracDomain fold first ≤ circleDiracDomain fold second := by
  intro state hState
  rcases hState with ⟨image, hImage⟩
  refine ⟨image + holonomyShift fold first second • state, ?_⟩
  intro mode
  change image mode + holonomyShift fold first second * state mode =
    complexDiracEigenvalue fold second mode * state mode
  rw [hImage mode]
  conv_rhs => rw [complexDiracEigenvalue_add_holonomyShift fold first second mode]
  ring

/-- All maximal Fourier domains are literally the same submodule at fixed fold. -/
theorem circleDiracDomain_eq_holonomy
    (fold : Fold) (first second : CircleTwist) :
    circleDiracDomain fold first = circleDiracDomain fold second := by
  apply le_antisymm
  · exact circleDiracDomain_mono_holonomy fold first second
  · exact circleDiracDomain_mono_holonomy fold second first

/-- The periodic representative is used only as a canonical name for the common domain. -/
abbrev CircleCommonDomain (fold : Fold) :=
  circleDiracDomain fold periodicTwist

theorem circleCommonDomain_eq (fold : Fold) (twist : CircleTwist) :
    CircleCommonDomain fold = circleDiracDomain fold twist :=
  circleDiracDomain_eq_holonomy fold periodicTwist twist

/-- Bounded scalar perturbation acting on the ambient circle Hilbert space. -/
def holonomyShiftCLM (fold : Fold) (first second : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  holonomyShift fold first second • ContinuousLinearMap.id ℂ CircleHilbert

@[simp] theorem holonomyShiftCLM_apply
    (fold : Fold) (first second : CircleTwist) (state : CircleHilbert) :
    holonomyShiftCLM fold first second state =
      holonomyShift fold first second • state := by
  rfl

theorem holonomyShiftCLM_bound
    (fold : Fold) (first second : CircleTwist) (state : CircleHilbert) :
    ‖holonomyShiftCLM fold first second state‖ =
      ‖holonomyShift fold first second‖ * ‖state‖ := by
  simpa only [holonomyShiftCLM_apply] using
    norm_smul (holonomyShift fold first second) state

/-- Exact graph-level bounded-perturbation identity on the common raw state. -/
theorem circleUnboundedDirac_holonomy_perturbation
    (fold : Fold) (first second : CircleTwist)
    (state : CircleHilbert)
    (hFirst : state ∈ circleDiracDomain fold first)
    (hSecond : state ∈ circleDiracDomain fold second) :
    circleUnboundedDirac fold second ⟨state, hSecond⟩ =
      circleUnboundedDirac fold first ⟨state, hFirst⟩ +
        holonomyShiftCLM fold first second state := by
  ext mode
  change
    (circleUnboundedDirac fold second ⟨state, hSecond⟩ : CircleHilbert) mode =
      (circleUnboundedDirac fold first ⟨state, hFirst⟩ : CircleHilbert) mode +
        (holonomyShiftCLM fold first second state) mode
  rw [circleUnboundedDirac_apply, circleUnboundedDirac_apply]
  change complexDiracEigenvalue fold second mode * state mode =
    complexDiracEigenvalue fold first mode * state mode +
      holonomyShift fold first second * state mode
  rw [complexDiracEigenvalue_add_holonomyShift fold first second mode]
  ring

/-- Periodic member written as a linear map on the explicitly named common domain. -/
def periodicCircleDiracOnCommonDomain (fold : Fold) :
    circleDiracDomain fold periodicTwist →ₗ[ℂ] CircleHilbert where
  toFun := circleDiracImage fold periodicTwist
  map_add' first second := by
    ext mode
    simp [circleDiracImage_apply]
    ring
  map_smul' scalar state := by
    ext mode
    simp [circleDiracImage_apply]
    ring

@[simp] theorem periodicCircleDiracOnCommonDomain_apply
    (fold : Fold) (state : circleDiracDomain fold periodicTwist) :
    periodicCircleDiracOnCommonDomain fold state =
      circleUnboundedDirac fold periodicTwist state := by
  rfl

/-- The real holonomy family, represented on the canonical common domain. -/
def commonDomainCircleDirac (fold : Fold) (twist : CircleTwist) :
    circleDiracDomain fold periodicTwist →ₗ[ℂ] CircleHilbert :=
  periodicCircleDiracOnCommonDomain fold +
    (holonomyShift fold periodicTwist twist •
      (circleDiracDomain fold periodicTwist).subtype)

@[simp] theorem commonDomainCircleDirac_apply
    (fold : Fold) (twist : CircleTwist)
    (state : CircleCommonDomain fold) :
    commonDomainCircleDirac fold twist state =
      circleUnboundedDirac fold periodicTwist state +
        holonomyShift fold periodicTwist twist • (state : CircleHilbert) := by
  rfl

/-- The common-domain representative agrees with the original maximal operator. -/
theorem commonDomainCircleDirac_eq_unbounded
    (fold : Fold) (twist : CircleTwist)
    (state : CircleCommonDomain fold) :
    commonDomainCircleDirac fold twist state =
      circleUnboundedDirac fold twist
        ⟨state, circleDiracDomain_mono_holonomy fold periodicTwist twist
          state.property⟩ := by
  symm
  exact circleUnboundedDirac_holonomy_perturbation fold periodicTwist twist
    state state.property
      (circleDiracDomain_mono_holonomy fold periodicTwist twist state.property)

/-- Complexified affine type-A family on the same algebraic domain. -/
def complexHolonomyCircleDirac (fold : Fold) (z : ℂ) :
    circleDiracDomain fold periodicTwist →ₗ[ℂ] CircleHilbert :=
  periodicCircleDiracOnCommonDomain fold +
    ((((fold.spectralSign : ℝ) : ℂ) * z) •
      (circleDiracDomain fold periodicTwist).subtype)

@[simp] theorem complexHolonomyCircleDirac_apply
    (fold : Fold) (z : ℂ) (state : CircleCommonDomain fold) :
    complexHolonomyCircleDirac fold z state =
      circleUnboundedDirac fold periodicTwist state +
        (((fold.spectralSign : ℝ) : ℂ) * z) • (state : CircleHilbert) := by
  rfl

/-- For every common-domain vector, the complexified family is entire. -/
theorem complexHolonomyCircleDirac_contDiff
    (fold : Fold) (state : CircleCommonDomain fold) :
    ContDiff ℂ ∞ (fun z : ℂ => complexHolonomyCircleDirac fold z state) := by
  simp only [complexHolonomyCircleDirac_apply]
  fun_prop

/-- The real physical family is the restriction of the complex affine family. -/
theorem commonDomainCircleDirac_eq_complexHolonomy
    (fold : Fold) (twist : CircleTwist) :
    commonDomainCircleDirac fold twist =
      complexHolonomyCircleDirac fold (twist.value : ℂ) := by
  apply LinearMap.ext
  intro state
  simp [commonDomainCircleDirac, complexHolonomyCircleDirac,
    holonomyShift, periodicTwist]

/-! ## Compact diagonal multipliers on the integer Fourier basis -/

def circleDiagonalMultiplierLinearMap (multiplier : ℤ → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1) :
    CircleHilbert →ₗ[ℂ] CircleHilbert where
  toFun state := ⟨fun mode => multiplier mode * state mode, by
    refine state.2.mono' ?_
    intro mode
    simpa using mul_le_mul_of_nonneg_right
      (hBound mode) (norm_nonneg (state mode))⟩
  map_add' first second := by
    ext mode
    simp [mul_add]
  map_smul' scalar state := by
    ext mode
    simp [mul_left_comm]

def circleDiagonalMultiplierCLM (multiplier : ℤ → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (circleDiagonalMultiplierLinearMap multiplier hBound).mkContinuous 1 (by
    intro state
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
    intro mode
    change ‖multiplier mode * state mode‖ ≤ ‖state mode‖
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right
      (hBound mode) (norm_nonneg (state mode)))

@[simp] theorem circleDiagonalMultiplierCLM_apply
    (multiplier : ℤ → ℂ) (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (state : CircleHilbert) (mode : ℤ) :
    circleDiagonalMultiplierCLM multiplier hBound state mode =
      multiplier mode * state mode := rfl

def circleCoordinateRankOne (mode : ℤ) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 mode).comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode)

theorem circleCoordinateRankOne_compact (mode : ℤ) :
    IsCompactOperator (circleCoordinateRankOne mode) := by
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode)).clm_comp
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 mode)

def circleFiniteDiagonalTruncation (multiplier : ℤ → ℂ)
    (modes : Finset ℤ) : CircleHilbert →L[ℂ] CircleHilbert :=
  ∑ mode ∈ modes, multiplier mode • circleCoordinateRankOne mode

@[simp] theorem circleFiniteDiagonalTruncation_apply
    (multiplier : ℤ → ℂ) (modes : Finset ℤ)
    (state : CircleHilbert) (mode : ℤ) :
    circleFiniteDiagonalTruncation multiplier modes state mode =
      if mode ∈ modes then multiplier mode * state mode else 0 := by
  classical
  induction modes using Finset.induction_on with
  | empty => simp [circleFiniteDiagonalTruncation]
  | @insert inserted modes hInserted hInduction =>
      rw [circleFiniteDiagonalTruncation, Finset.sum_insert hInserted]
      change multiplier inserted *
          (lp.single 2 inserted (state inserted) : CircleHilbert) mode +
          circleFiniteDiagonalTruncation multiplier modes state mode = _
      by_cases hMode : mode = inserted
      · subst mode
        rw [hInduction]
        simp [hInserted]
      · rw [lp.single_apply_ne (E := fun _ : ℤ => ℂ)
          2 inserted (state inserted) hMode, mul_zero, zero_add, hInduction]
        simp [hMode]

theorem circleFiniteDiagonalTruncation_compact (multiplier : ℤ → ℂ)
    (modes : Finset ℤ) :
    IsCompactOperator (circleFiniteDiagonalTruncation multiplier modes) := by
  induction modes using Finset.induction_on with
  | empty =>
      simp [circleFiniteDiagonalTruncation]
      exact isCompactOperator_zero
  | @insert mode modes hMode hInduction =>
      rw [circleFiniteDiagonalTruncation, Finset.sum_insert hMode]
      exact ((circleCoordinateRankOne_compact mode).smul
        (multiplier mode)).add hInduction

def CircleMultiplierVanishesAtInfinity (multiplier : ℤ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Finite {mode | ε ≤ ‖multiplier mode‖}

theorem circleDiagonal_sub_finite_truncation_norm_le
    (multiplier : ℤ → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (modes : Finset ℤ) (ε : ℝ) (hε : 0 ≤ ε)
    (hTail : ∀ mode, mode ∉ modes → ‖multiplier mode‖ ≤ ε) :
    ‖circleDiagonalMultiplierCLM multiplier hBound -
        circleFiniteDiagonalTruncation multiplier modes‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro state
  rw [← show ‖(ε : ℂ) • state‖ = ε * ‖state‖ by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε] using
      (norm_smul (ε : ℂ) state)]
  apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
  intro mode
  change ‖multiplier mode * state mode -
      circleFiniteDiagonalTruncation multiplier modes state mode‖ ≤
        ‖(ε : ℂ) • state mode‖
  by_cases hMode : mode ∈ modes
  · simp [hMode]
    positivity
  · rw [circleFiniteDiagonalTruncation_apply, if_neg hMode, sub_zero,
      norm_mul, norm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_right (hTail mode hMode)
      (norm_nonneg (state mode))

def circleDecayTruncationModes (multiplier : ℤ → ℂ)
    (hDecay : CircleMultiplierVanishesAtInfinity multiplier) (n : ℕ) :
    Finset ℤ :=
  (hDecay (1 / ((n : ℝ) + 1)) (by positivity)).toFinset

theorem circleNorm_finite_decay_truncation_sub_diagonal_le
    (multiplier : ℤ → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (hDecay : CircleMultiplierVanishesAtInfinity multiplier) (n : ℕ) :
    ‖circleFiniteDiagonalTruncation multiplier
        (circleDecayTruncationModes multiplier hDecay n) -
      circleDiagonalMultiplierCLM multiplier hBound‖ ≤
        1 / ((n : ℝ) + 1) := by
  rw [norm_sub_rev]
  apply circleDiagonal_sub_finite_truncation_norm_le
  · positivity
  · intro mode hMode
    have hNotSuperlevel : mode ∉
        {mode | 1 / ((n : ℝ) + 1) ≤ ‖multiplier mode‖} := by
      simpa [circleDecayTruncationModes] using hMode
    exact le_of_lt (not_le.1 hNotSuperlevel)

/-- A bounded circle Fourier multiplier vanishing at infinity is compact. -/
theorem circleDiagonalMultiplier_compact_of_vanishes_at_infinity
    (multiplier : ℤ → ℂ)
    (hBound : ∀ mode, ‖multiplier mode‖ ≤ 1)
    (hDecay : CircleMultiplierVanishesAtInfinity multiplier) :
    IsCompactOperator (circleDiagonalMultiplierCLM multiplier hBound) := by
  apply isCompactOperator_of_tendsto (l := Filter.atTop)
    (F := fun n : ℕ => circleFiniteDiagonalTruncation multiplier
      (circleDecayTruncationModes multiplier hDecay n))
    (f := circleDiagonalMultiplierCLM multiplier hBound)
  · apply tendsto_iff_norm_sub_tendsto_zero.2
    exact squeeze_zero (fun n => norm_nonneg _)
      (circleNorm_finite_decay_truncation_sub_diagonal_le
        multiplier hBound hDecay)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Filter.Eventually.of_forall fun n =>
      circleFiniteDiagonalTruncation_compact multiplier
        (circleDecayTruncationModes multiplier hDecay n)

/-! ## The actual circle `(D-i)⁻¹` -/

theorem circle_one_le_norm_real_sub_I (x : ℝ) :
    1 ≤ ‖(x : ℂ) - Complex.I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) - Complex.I)

theorem circle_norm_real_le_norm_real_sub_I (x : ℝ) :
    ‖(x : ℂ)‖ ≤ ‖(x : ℂ) - Complex.I‖ := by
  simpa using Complex.abs_re_le_norm ((x : ℂ) - Complex.I)

theorem circle_real_sub_I_ne_zero (x : ℝ) :
    (x : ℂ) - Complex.I ≠ 0 := by
  intro hZero
  have := circle_one_le_norm_real_sub_I x
  rw [hZero, norm_zero] at this
  norm_num at this

/-- Every bounded spectral window of the circle multiplier contains finitely many modes. -/
theorem circleDirac_bounded_window_finite
    (fold : Fold) (twist : CircleTwist) (radius : ℝ) :
    Set.Finite {mode : ℤ |
      ‖complexDiracEigenvalue fold twist mode‖ ≤ radius} := by
  obtain ⟨cutoff, hCutoff⟩ := exists_nat_gt (max radius 0 + 1)
  refine (Set.finite_Icc (-(cutoff : ℤ)) (cutoff : ℤ)).subset ?_
  intro mode hMode
  change ‖(diracEigenvalue fold twist mode : ℂ)‖ ≤ radius at hMode
  rw [Complex.norm_real] at hMode
  rw [Real.norm_eq_abs] at hMode
  have hBase : |(mode : ℝ) + twist.value| ≤ radius := by
    cases fold
    · simpa only [positive_diracEigenvalue, baseEigenvalue] using hMode
    · simpa only [pt_diracEigenvalue, baseEigenvalue, abs_neg] using hMode
  have hBounds := abs_le.mp hBase
  have hLowerReal : -(cutoff : ℝ) < (mode : ℝ) := by
    have hRadius : radius ≤ max radius 0 := le_max_left _ _
    linarith [twist.le_one]
  have hUpperReal : (mode : ℝ) < (cutoff : ℝ) := by
    have hRadius : radius ≤ max radius 0 := le_max_left _ _
    linarith [twist.nonnegative]
  constructor
  · exact_mod_cast le_of_lt hLowerReal
  · exact_mod_cast le_of_lt hUpperReal

/-- Fourier multiplier of the shifted resolvent. -/
def circleShiftIResolventMultiplier
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℂ :=
  1 / (complexDiracEigenvalue fold twist mode - Complex.I)

theorem circleShiftIResolventMultiplier_norm_le_one
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    ‖circleShiftIResolventMultiplier fold twist mode‖ ≤ 1 := by
  unfold circleShiftIResolventMultiplier complexDiracEigenvalue
  rw [norm_div, norm_one]
  have hDenPositive :
      0 < ‖(diracEigenvalue fold twist mode : ℂ) - Complex.I‖ :=
    lt_of_lt_of_le zero_lt_one
      (circle_one_le_norm_real_sub_I (diracEigenvalue fold twist mode))
  apply (div_le_iff₀ hDenPositive).2
  simpa using circle_one_le_norm_real_sub_I
    (diracEigenvalue fold twist mode)

theorem circleShiftIResolventMultiplier_vanishes
    (fold : Fold) (twist : CircleTwist) :
    CircleMultiplierVanishesAtInfinity
      (circleShiftIResolventMultiplier fold twist) := by
  intro ε hε
  refine (circleDirac_bounded_window_finite fold twist (1 / ε)).subset ?_
  intro mode hMode
  change ε ≤ ‖1 /
    (complexDiracEigenvalue fold twist mode - Complex.I)‖ at hMode
  rw [norm_div, norm_one] at hMode
  have hDenPositive :
      0 < ‖complexDiracEigenvalue fold twist mode - Complex.I‖ := by
    unfold complexDiracEigenvalue
    exact lt_of_lt_of_le zero_lt_one
      (circle_one_le_norm_real_sub_I (diracEigenvalue fold twist mode))
  have hMul :
      ε * ‖complexDiracEigenvalue fold twist mode - Complex.I‖ ≤ 1 :=
    (le_div_iff₀ hDenPositive).1 hMode
  have hDen :
      ‖complexDiracEigenvalue fold twist mode - Complex.I‖ ≤ 1 / ε := by
    apply (le_div_iff₀ hε).2
    simpa [mul_comm] using hMul
  unfold complexDiracEigenvalue
  exact (circle_norm_real_le_norm_real_sub_I
    (diracEigenvalue fold twist mode)).trans hDen

/-- Bounded Fourier realization of `(D-i)⁻¹`. -/
def circleShiftIResolventCLM (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  circleDiagonalMultiplierCLM
    (circleShiftIResolventMultiplier fold twist)
    (circleShiftIResolventMultiplier_norm_le_one fold twist)

@[simp] theorem circleShiftIResolventCLM_apply
    (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleShiftIResolventCLM fold twist state mode =
      circleShiftIResolventMultiplier fold twist mode * state mode := by
  rfl

/-- The resolvent maps the whole Hilbert space into the maximal Dirac domain. -/
theorem circleShiftIResolvent_mem_domain
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert) :
    circleShiftIResolventCLM fold twist state ∈
      circleDiracDomain fold twist := by
  let resolved := circleShiftIResolventCLM fold twist state
  refine ⟨state + Complex.I • resolved, ?_⟩
  intro mode
  change state mode + Complex.I * resolved mode =
    complexDiracEigenvalue fold twist mode * resolved mode
  rw [show resolved mode =
      circleShiftIResolventMultiplier fold twist mode * state mode by rfl]
  unfold circleShiftIResolventMultiplier
  field_simp [circle_real_sub_I_ne_zero
    (diracEigenvalue fold twist mode), complexDiracEigenvalue]
  ring

/-- `(D-i)(D-i)⁻¹ = 1` on the whole circle Hilbert space. -/
theorem circleShiftIResolvent_right_inverse
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert) :
    circleUnboundedDirac fold twist
        ⟨circleShiftIResolventCLM fold twist state,
          circleShiftIResolvent_mem_domain fold twist state⟩ -
      Complex.I • circleShiftIResolventCLM fold twist state = state := by
  ext mode
  change
    (circleUnboundedDirac fold twist
      ⟨circleShiftIResolventCLM fold twist state,
        circleShiftIResolvent_mem_domain fold twist state⟩ : CircleHilbert) mode -
      (Complex.I • circleShiftIResolventCLM fold twist state : CircleHilbert) mode =
        state mode
  rw [circleUnboundedDirac_apply]
  change complexDiracEigenvalue fold twist mode *
      (circleShiftIResolventMultiplier fold twist mode * state mode) -
    Complex.I *
      (circleShiftIResolventMultiplier fold twist mode * state mode) = state mode
  unfold circleShiftIResolventMultiplier
  field_simp [circle_real_sub_I_ne_zero
    (diracEigenvalue fold twist mode), complexDiracEigenvalue]

/-- `(D-i)⁻¹(D-i) = 1` on the maximal circle domain. -/
theorem circleShiftIResolvent_left_inverse
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracDomain fold twist) :
    circleShiftIResolventCLM fold twist
      (circleUnboundedDirac fold twist state - Complex.I • (state : CircleHilbert)) =
        (state : CircleHilbert) := by
  ext mode
  change
    (circleShiftIResolventCLM fold twist
      (circleUnboundedDirac fold twist state -
        Complex.I • (state : CircleHilbert))) mode = state.1 mode
  rw [circleShiftIResolventCLM_apply]
  change circleShiftIResolventMultiplier fold twist mode *
      ((circleUnboundedDirac fold twist state : CircleHilbert) mode -
        Complex.I * state.1 mode) = state.1 mode
  rw [circleUnboundedDirac_apply]
  change circleShiftIResolventMultiplier fold twist mode *
      (complexDiracEigenvalue fold twist mode * state.1 mode -
        Complex.I * state.1 mode) = state.1 mode
  unfold circleShiftIResolventMultiplier
  field_simp [circle_real_sub_I_ne_zero
    (diracEigenvalue fold twist mode), complexDiracEigenvalue]

/-- The genuine shifted circle resolvent is compact. -/
theorem circleShiftIResolvent_compact
    (fold : Fold) (twist : CircleTwist) :
    IsCompactOperator (circleShiftIResolventCLM fold twist) := by
  exact circleDiagonalMultiplier_compact_of_vanishes_at_infinity
    (circleShiftIResolventMultiplier fold twist)
    (circleShiftIResolventMultiplier_norm_le_one fold twist)
    (circleShiftIResolventMultiplier_vanishes fold twist)

end

end P0EFTJanusCircleHolonomyCommonDomainCompactResolvent
end JanusFormal
