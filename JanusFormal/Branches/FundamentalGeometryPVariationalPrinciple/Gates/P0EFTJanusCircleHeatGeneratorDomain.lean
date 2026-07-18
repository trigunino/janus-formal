import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatSemigroupStrongContinuity

/-!
# Maximal generator domain of the circle heat semigroup

For the explicit diagonal circle model, the maximal spectral `D²` domain is
the weighted `ℓ²` domain of the squared Dirac eigenvalues.  The strong
right-hand derivative at time zero exists exactly on this domain and equals
`-D²`.  Thus the generator-domain statement is proved on the full Fourier
Hilbert space, not merely on the dense basis.

This is still the normalized circle operator, not the global Janus Dirac
family or an abstract functional-calculus identification.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatGeneratorDomain

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatSemigroupStrongContinuity
open scoped ENNReal lp

/-- Maximal diagonal domain of the squared circle Dirac operator. -/
def circleDiracSquaredDomain
    (fold : Fold) (twist : CircleTwist) : Submodule ℂ CircleHilbert where
  carrier := {state | ∃ image : CircleHilbert, ∀ mode,
    image mode =
      (circleOperatorSquaredEigenvalue fold twist mode : ℂ) * state mode}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro mode
    simp
  add_mem' := by
    rintro first second ⟨firstImage, hFirst⟩ ⟨secondImage, hSecond⟩
    refine ⟨firstImage + secondImage, ?_⟩
    intro mode
    change firstImage mode + secondImage mode =
      (circleOperatorSquaredEigenvalue fold twist mode : ℂ) *
        (first mode + second mode)
    rw [hFirst mode, hSecond mode]
    ring
  smul_mem' := by
    intro scalar state
    rintro ⟨image, hImage⟩
    refine ⟨scalar • image, ?_⟩
    intro mode
    change scalar * image mode =
      (circleOperatorSquaredEigenvalue fold twist mode : ℂ) *
        (scalar * state mode)
    rw [hImage mode]
    ring

/-- The uniquely determined squared spectral image. -/
def circleDiracSquaredImage
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) : CircleHilbert :=
  state.property.choose

@[simp]
theorem circleDiracSquaredImage_apply
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) (mode : ℤ) :
    circleDiracSquaredImage fold twist state mode =
      (circleOperatorSquaredEigenvalue fold twist mode : ℂ) * state.1 mode :=
  state.property.choose_spec mode

/-- The genuine maximal-domain diagonal `D²` partial linear operator. -/
def circleUnboundedDiracSquared
    (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →ₗ.[ℂ] CircleHilbert where
  domain := circleDiracSquaredDomain fold twist
  toFun :=
    { toFun := circleDiracSquaredImage fold twist
      map_add' := by
        intro first second
        ext mode
        simp [circleDiracSquaredImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [circleDiracSquaredImage_apply]
        ring }

@[simp]
theorem circleUnboundedDiracSquared_apply
    (fold : Fold) (twist : CircleTwist)
    (state : (circleUnboundedDiracSquared fold twist).domain) (mode : ℤ) :
    circleUnboundedDiracSquared fold twist state mode =
      (circleOperatorSquaredEigenvalue fold twist mode : ℂ) * state.1 mode :=
  circleDiracSquaredImage_apply fold twist state mode

theorem circleOperatorSquaredEigenvalue_coe_eq_mul
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    (circleOperatorSquaredEigenvalue fold twist mode : ℂ) =
      complexDiracEigenvalue fold twist mode *
        complexDiracEigenvalue fold twist mode := by
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  simp [eigenvalueSq, complexDiracEigenvalue, pow_two]

/-- The first Dirac image is square summable whenever the squared image is.
This is the elementary graph interpolation needed to identify the spectral
square with the actual iterated operator domain. -/
def circleDiracFirstImageOfSquared
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) : CircleHilbert := by
  let first : ℤ → ℂ := fun mode =>
    complexDiracEigenvalue fold twist mode * state.1 mode
  have hBoundMem : Memℓp
      (fun mode : ℤ => ‖state.1 mode‖ +
        ‖circleDiracSquaredImage fold twist state mode‖) 2 := by
    exact (lp.memℓp state.1).norm.add
      (lp.memℓp (circleDiracSquaredImage fold twist state)).norm
  have hFirstMem : Memℓp first 2 := hBoundMem.mono' (fun mode => by
    have hEigenvalueSq :
        0 ≤ circleOperatorSquaredEigenvalue fold twist mode := by
      rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
      exact eigenvalueSq_nonnegative fold twist mode
    have hAbs :
        |diracEigenvalue fold twist mode| ≤
          1 + circleOperatorSquaredEigenvalue fold twist mode := by
      rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq, eigenvalueSq]
      have hSqAbs : |diracEigenvalue fold twist mode| ^ 2 =
          diracEigenvalue fold twist mode ^ 2 := sq_abs _
      nlinarith [sq_nonneg (|diracEigenvalue fold twist mode| - (1 / 2 : ℝ))]
    have hMul := mul_le_mul_of_nonneg_right hAbs
      (norm_nonneg (state.1 mode))
    have hEigenNorm :
        ‖complexDiracEigenvalue fold twist mode‖ =
          |diracEigenvalue fold twist mode| := by
      simp [complexDiracEigenvalue, Real.norm_eq_abs]
    have hSquaredImageNorm :
        ‖circleDiracSquaredImage fold twist state mode‖ =
          circleOperatorSquaredEigenvalue fold twist mode *
            ‖state.1 mode‖ := by
      rw [circleDiracSquaredImage_apply, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hEigenvalueSq]
    change ‖complexDiracEigenvalue fold twist mode * state.1 mode‖ ≤
      ‖(‖state.1 mode‖ +
        ‖circleDiracSquaredImage fold twist state mode‖ : ℝ)‖
    rw [norm_mul, hEigenNorm]
    calc
      _ ≤ (1 + circleOperatorSquaredEigenvalue fold twist mode) *
          ‖state.1 mode‖ := hMul
      _ = ‖state.1 mode‖ +
          circleOperatorSquaredEigenvalue fold twist mode * ‖state.1 mode‖ := by
        ring
      _ = ‖state.1 mode‖ +
          ‖circleDiracSquaredImage fold twist state mode‖ := by
        rw [hSquaredImageNorm]
      _ = ‖(‖state.1 mode‖ +
          ‖circleDiracSquaredImage fold twist state mode‖ : ℝ)‖ := by
        symm
        exact Real.norm_of_nonneg
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  exact ⟨first, hFirstMem⟩

@[simp]
theorem circleDiracFirstImageOfSquared_apply
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) (mode : ℤ) :
    circleDiracFirstImageOfSquared fold twist state mode =
      complexDiracEigenvalue fold twist mode * state.1 mode := by
  rfl

/-- Domain on which the already constructed unbounded Dirac operator can be
applied twice. -/
def circleDiracIteratedDomain
    (fold : Fold) (twist : CircleTwist) : Set CircleHilbert :=
  {state | ∃ hState : state ∈ circleDiracDomain fold twist,
    circleDiracImage fold twist ⟨state, hState⟩ ∈
      circleDiracDomain fold twist}

theorem mem_circleDiracIteratedDomain_of_mem_squaredDomain
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) :
    state.1 ∈ circleDiracIteratedDomain fold twist := by
  let first := circleDiracFirstImageOfSquared fold twist state
  have hFirst : state.1 ∈ circleDiracDomain fold twist := by
    refine ⟨first, ?_⟩
    intro mode
    exact circleDiracFirstImageOfSquared_apply fold twist state mode
  refine ⟨hFirst, ?_⟩
  have hImageEq :
      circleDiracImage fold twist ⟨state.1, hFirst⟩ = first := by
    ext mode
    rw [circleDiracImage_apply]
    exact (circleDiracFirstImageOfSquared_apply fold twist state mode).symm
  rw [hImageEq]
  refine ⟨circleDiracSquaredImage fold twist state, ?_⟩
  intro mode
  rw [circleDiracSquaredImage_apply,
    circleDiracFirstImageOfSquared_apply,
    circleOperatorSquaredEigenvalue_coe_eq_mul]
  ring

theorem mem_squaredDomain_of_mem_circleDiracIteratedDomain
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert)
    (hState : state ∈ circleDiracIteratedDomain fold twist) :
    state ∈ circleDiracSquaredDomain fold twist := by
  rcases hState with ⟨hFirst, hSecond⟩
  rcases hSecond with ⟨second, hSecond⟩
  refine ⟨second, ?_⟩
  intro mode
  rw [hSecond mode, circleDiracImage_apply,
    circleOperatorSquaredEigenvalue_coe_eq_mul]
  ring

/-- The maximal spectral square is exactly the domain of the actual
composition `D ∘ D`. -/
theorem circleDiracSquaredDomain_eq_iteratedDomain
    (fold : Fold) (twist : CircleTwist) :
    (circleDiracSquaredDomain fold twist : Set CircleHilbert) =
      circleDiracIteratedDomain fold twist := by
  ext state
  constructor
  · intro hState
    exact mem_circleDiracIteratedDomain_of_mem_squaredDomain fold twist
      ⟨state, hState⟩
  · exact mem_squaredDomain_of_mem_circleDiracIteratedDomain fold twist state

/-- Scalar right difference quotient of `exp (-t a)`. -/
def circleHeatScalarSlope (time eigenvalueSq : ℝ) : ℝ :=
  time⁻¹ * (Real.exp (-time * eigenvalueSq) - 1)

theorem circleHeatScalarSlope_tendsto
    (eigenvalueSq : ℝ) :
    Tendsto (fun time : ℝ => circleHeatScalarSlope time eigenvalueSq)
      (𝓝[>] (0 : ℝ)) (𝓝 (-eigenvalueSq)) := by
  have hExponent :
      HasDerivAt (fun time : ℝ => -time * eigenvalueSq)
        (-eigenvalueSq) 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).neg.mul_const eigenvalueSq
  have hExp :=
    (Real.hasDerivAt_exp (-0 * eigenvalueSq)).comp 0 hExponent
  simpa [circleHeatScalarSlope, Function.comp_def] using
    hExp.tendsto_slope_zero_right

theorem circleHeatScalarSlope_abs_le
    {time eigenvalueSq : ℝ} (hTime : 0 < time)
    (hEigenvalueSq : 0 ≤ eigenvalueSq) :
    |circleHeatScalarSlope time eigenvalueSq| ≤ eigenvalueSq := by
  have hProduct : 0 ≤ time * eigenvalueSq :=
    mul_nonneg hTime.le hEigenvalueSq
  have hExpLe : Real.exp (-time * eigenvalueSq) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hOneSub :
      1 - Real.exp (-time * eigenvalueSq) ≤ time * eigenvalueSq := by
    have hBound := Real.one_sub_le_exp_neg (time * eigenvalueSq)
    rw [show -(time * eigenvalueSq) = -time * eigenvalueSq by ring] at hBound
    linarith
  calc
    |circleHeatScalarSlope time eigenvalueSq| =
        time⁻¹ * (1 - Real.exp (-time * eigenvalueSq)) := by
      rw [circleHeatScalarSlope, abs_mul, abs_inv, abs_of_pos hTime,
        abs_of_nonpos (sub_nonpos.mpr hExpLe)]
      ring
    _ ≤ time⁻¹ * (time * eigenvalueSq) :=
      mul_le_mul_of_nonneg_left hOneSub (inv_nonneg.mpr hTime.le)
    _ = eigenvalueSq := by field_simp

/-- Strong difference quotient, extended by zero away from positive times.
Only its germ in `𝓝[>] 0` is used. -/
def circleHeatDifferenceQuotient
    (time : ℝ) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) : CircleHilbert :=
  if hTime : 0 < time then
    (time : ℂ)⁻¹ •
      (circleHeatSemigroup ⟨time, hTime.le⟩ fold twist state - state)
  else 0

theorem circleHeatDifferenceQuotient_apply_of_pos
    {time : ℝ} (hTime : 0 < time)
    (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleHeatDifferenceQuotient time fold twist state mode =
      (circleHeatScalarSlope time
        (circleOperatorSquaredEigenvalue fold twist mode) : ℂ) * state mode := by
  simp [circleHeatDifferenceQuotient, hTime, circleHeatSemigroup_apply,
    circleHeatMultiplier, circleHeatScalarSlope]
  ring

theorem circleHeatDifferenceQuotient_apply_tendsto
    (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    Tendsto (fun time : ℝ =>
      circleHeatDifferenceQuotient time fold twist state mode)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-(circleOperatorSquaredEigenvalue fold twist mode) : ℂ) *
        state mode)) := by
  have hScalar := circleHeatScalarSlope_tendsto
    (circleOperatorSquaredEigenvalue fold twist mode)
  have hComplex :
      Tendsto (fun time : ℝ =>
        (circleHeatScalarSlope time
          (circleOperatorSquaredEigenvalue fold twist mode) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(circleOperatorSquaredEigenvalue fold twist mode) : ℂ)) :=
    by
      simpa [Function.comp_def] using
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hScalar)
  have hProduct := hComplex.mul_const (state mode)
  apply hProduct.congr'
  filter_upwards [self_mem_nhdsWithin] with time hTime
  exact (circleHeatDifferenceQuotient_apply_of_pos hTime
    fold twist state mode).symm

/-- Squared coordinate error against the candidate generator `-D² state`. -/
def circleHeatGeneratorCoordinateErrorSquare
    (time : ℝ) (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) (mode : ℤ) : ℝ :=
  ‖circleHeatDifferenceQuotient time fold twist state.1 mode -
      (-circleDiracSquaredImage fold twist state) mode‖ ^ 2

theorem circleHeatGeneratorCoordinateErrorSquare_tendsto
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) (mode : ℤ) :
    Tendsto (fun time : ℝ =>
      circleHeatGeneratorCoordinateErrorSquare time fold twist state mode)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hCoordinate := circleHeatDifferenceQuotient_apply_tendsto
    fold twist state.1 mode
  have hTarget :
      ((-(circleOperatorSquaredEigenvalue fold twist mode) : ℂ) *
          state.1 mode) =
        (-circleDiracSquaredImage fold twist state) mode := by
    simp [circleDiracSquaredImage_apply]
  rw [hTarget] at hCoordinate
  simpa [circleHeatGeneratorCoordinateErrorSquare] using
    ((hCoordinate.sub_const
      ((-circleDiracSquaredImage fold twist state) mode)).norm.pow 2)

theorem circleHeatGeneratorCoordinateErrorSquare_le
    {time : ℝ} (hTime : 0 < time)
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) (mode : ℤ) :
    circleHeatGeneratorCoordinateErrorSquare time fold twist state mode ≤
      4 * ‖circleDiracSquaredImage fold twist state mode‖ ^ 2 := by
  have hEigenvalueSq :
      0 ≤ circleOperatorSquaredEigenvalue fold twist mode := by
    rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
    exact eigenvalueSq_nonnegative fold twist mode
  have hSlope := circleHeatScalarSlope_abs_le hTime hEigenvalueSq
  have hTargetNorm :
      ‖(-circleDiracSquaredImage fold twist state) mode‖ =
        circleOperatorSquaredEigenvalue fold twist mode * ‖state.1 mode‖ := by
    simp [circleDiracSquaredImage_apply, Real.norm_eq_abs,
      abs_of_nonneg hEigenvalueSq]
  have hSlopeMul := mul_le_mul_of_nonneg_right hSlope
    (norm_nonneg (state.1 mode))
  have hDifference :
      ‖circleHeatDifferenceQuotient time fold twist state.1 mode -
          (-circleDiracSquaredImage fold twist state) mode‖ ≤
        2 * ‖circleDiracSquaredImage fold twist state mode‖ := by
    rw [circleHeatDifferenceQuotient_apply_of_pos hTime]
    calc
      _ ≤ ‖(circleHeatScalarSlope time
              (circleOperatorSquaredEigenvalue fold twist mode) : ℂ) *
            state.1 mode‖ +
          ‖(-circleDiracSquaredImage fold twist state) mode‖ :=
        norm_sub_le _ _
      _ ≤ 2 * ‖circleDiracSquaredImage fold twist state mode‖ := by
        rw [circleDiracSquaredImage_apply]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [hTargetNorm]
        rw [abs_of_nonneg hEigenvalueSq]
        nlinarith
  unfold circleHeatGeneratorCoordinateErrorSquare
  calc
    _ ≤ (2 * ‖circleDiracSquaredImage fold twist state mode‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg _))).2 hDifference
    _ = 4 * ‖circleDiracSquaredImage fold twist state mode‖ ^ 2 := by ring

theorem circleDiracSquaredImage_bound_summable
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) :
    Summable (fun mode : ℤ =>
      4 * ‖circleDiracSquaredImage fold twist state mode‖ ^ 2) := by
  have hImage := (lp.memℓp (circleDiracSquaredImage fold twist state)).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa [Real.rpow_two] using hImage.mul_left 4

/-- Every state in the maximal squared-Dirac domain has strong right
derivative `-D² state` under the heat semigroup. -/
theorem circleHeatDifferenceQuotient_tendsto_of_mem_squaredDomain
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) :
    Tendsto (fun time : ℝ =>
      circleHeatDifferenceQuotient time fold twist state.1)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-circleDiracSquaredImage fold twist state)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hTsum :
      Tendsto
        (fun time : ℝ => ∑' mode : ℤ,
          circleHeatGeneratorCoordinateErrorSquare
            time fold twist state mode)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hDominated := tendsto_tsum_of_dominated_convergence
      (circleDiracSquaredImage_bound_summable fold twist state)
      (fun mode => circleHeatGeneratorCoordinateErrorSquare_tendsto
        fold twist state mode)
      (show ∀ᶠ time : ℝ in 𝓝[>] (0 : ℝ), ∀ mode : ℤ,
          ‖circleHeatGeneratorCoordinateErrorSquare
              time fold twist state mode‖ ≤
            4 * ‖circleDiracSquaredImage fold twist state mode‖ ^ 2 by
        filter_upwards [self_mem_nhdsWithin] with time hTime mode
        have hNonnegative :
            0 ≤ circleHeatGeneratorCoordinateErrorSquare
              time fold twist state mode := by
          unfold circleHeatGeneratorCoordinateErrorSquare
          positivity
        simpa [Real.norm_eq_abs, abs_of_nonneg hNonnegative] using
          circleHeatGeneratorCoordinateErrorSquare_le hTime
            fold twist state mode)
    simpa using hDominated
  have hRoot := hTsum.rpow_const_nhds_zero
    (by norm_num : 0 < (1 / 2 : ℝ))
  apply hRoot.congr'
  filter_upwards [] with time
  rw [lp.norm_eq_tsum_rpow
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  congr 2

/-- Maximal strong right-generator domain at time zero. -/
def circleHeatGeneratorDomain
    (fold : Fold) (twist : CircleTwist) : Set CircleHilbert :=
  {state | ∃ generator : CircleHilbert,
    Tendsto (fun time : ℝ =>
      circleHeatDifferenceQuotient time fold twist state)
      (𝓝[>] (0 : ℝ)) (𝓝 generator)}

theorem mem_circleHeatGeneratorDomain_of_mem_squaredDomain
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist) :
    state.1 ∈ circleHeatGeneratorDomain fold twist :=
  ⟨-circleDiracSquaredImage fold twist state,
    circleHeatDifferenceQuotient_tendsto_of_mem_squaredDomain
      fold twist state⟩

theorem mem_squaredDomain_of_mem_circleHeatGeneratorDomain
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert)
    (hState : state ∈ circleHeatGeneratorDomain fold twist) :
    state ∈ circleDiracSquaredDomain fold twist := by
  rcases hState with ⟨generator, hGenerator⟩
  refine ⟨-generator, ?_⟩
  intro mode
  have hCoordinate :
      Tendsto (fun time : ℝ =>
        circleHeatDifferenceQuotient time fold twist state mode)
        (𝓝[>] (0 : ℝ)) (𝓝 (generator mode)) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode).continuous.continuousAt.tendsto).comp
      hGenerator
  have hExpected := circleHeatDifferenceQuotient_apply_tendsto
    fold twist state mode
  have hUnique :
      generator mode =
        (-(circleOperatorSquaredEigenvalue fold twist mode) : ℂ) *
          state mode :=
    tendsto_nhds_unique hCoordinate hExpected
  change -generator mode =
    (circleOperatorSquaredEigenvalue fold twist mode : ℂ) * state mode
  rw [hUnique]
  ring

/-- Exact maximal-domain identification: the heat generator domain is the
spectral domain of the genuine diagonal `D²` partial operator. -/
theorem circleHeatGeneratorDomain_eq_circleDiracSquaredDomain
    (fold : Fold) (twist : CircleTwist) :
    circleHeatGeneratorDomain fold twist =
      (circleDiracSquaredDomain fold twist : Set CircleHilbert) := by
  ext state
  constructor
  · exact mem_squaredDomain_of_mem_circleHeatGeneratorDomain fold twist state
  · intro hState
    exact mem_circleHeatGeneratorDomain_of_mem_squaredDomain fold twist
      ⟨state, hState⟩

/-- On the maximal generator domain the strong derivative is uniquely `-D²`. -/
theorem circleHeatGenerator_eq_neg_diracSquared
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracSquaredDomain fold twist)
    (generator : CircleHilbert)
    (hGenerator : Tendsto (fun time : ℝ =>
      circleHeatDifferenceQuotient time fold twist state.1)
      (𝓝[>] (0 : ℝ)) (𝓝 generator)) :
    generator = -circleDiracSquaredImage fold twist state :=
  tendsto_nhds_unique hGenerator
    (circleHeatDifferenceQuotient_tendsto_of_mem_squaredDomain
      fold twist state)

end

end P0EFTJanusCircleHeatGeneratorDomain
end JanusFormal
