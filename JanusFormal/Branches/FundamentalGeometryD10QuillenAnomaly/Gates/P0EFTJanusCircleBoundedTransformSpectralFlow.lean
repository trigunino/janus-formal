import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleGraphFredholmIndex
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Norm-continuous bounded transform of the circle Dirac family

This gate applies the standard normalizing function
`x ↦ x / sqrt (1 + x²) = sin (arctan x)` to the actual infinite Fourier
circle family.  It proves norm-Lipschitz dependence on holonomy,
self-adjointness, the Fredholm criterion and exact endpoint crossings.

The construction is confined to the normalized circle model.  It is not yet
a global Janus spectral-flow or family-index theorem.
-/

namespace JanusFormal
namespace P0EFTJanusCircleBoundedTransformSpectralFlow

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleHolonomyCommonDomainCompactResolvent
open P0EFTJanusCircleGraphFredholmIndex
open scoped ENNReal lp

theorem circleTwist_value_injective :
    Function.Injective CircleTwist.value := by
  intro first second hValue
  cases first
  cases second
  simp_all

/-- Metric inherited from the holonomy coordinate in `[0,1]`. -/
noncomputable instance circleTwistMetricSpace : MetricSpace CircleTwist :=
  MetricSpace.induced CircleTwist.value circleTwist_value_injective inferInstance

@[simp] theorem circleTwist_dist_eq (first second : CircleTwist) :
    dist first second = |first.value - second.value| := by
  change dist first.value second.value = _
  exact Real.dist_eq _ _

/-! ## The scalar normalizing function -/

/-- Standard real bounded transform `x / sqrt (1 + x²)`. -/
def circleBoundedTransformScalar (x : ℝ) : ℝ :=
  Real.sin (Real.arctan x)

theorem circleBoundedTransformScalar_eq (x : ℝ) :
    circleBoundedTransformScalar x = x / Real.sqrt (1 + x ^ 2) := by
  exact Real.sin_arctan x

@[simp] theorem circleBoundedTransformScalar_zero :
    circleBoundedTransformScalar 0 = 0 := by
  simp [circleBoundedTransformScalar]

@[simp] theorem circleBoundedTransformScalar_neg (x : ℝ) :
    circleBoundedTransformScalar (-x) = -circleBoundedTransformScalar x := by
  simp [circleBoundedTransformScalar]

theorem abs_circleBoundedTransformScalar_le_one (x : ℝ) :
    |circleBoundedTransformScalar x| ≤ 1 := by
  exact Real.abs_sin_le_one _

theorem circleBoundedTransformScalar_eq_zero_iff (x : ℝ) :
    circleBoundedTransformScalar x = 0 ↔ x = 0 := by
  exact Real.sin_arctan_eq_zero

theorem circleArctan_lipschitz :
    LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
  intro x
  rw [Real.deriv_arctan]
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + x ^ 2))]
  exact (div_le_one (by positivity : 0 < 1 + x ^ 2)).2
    (by nlinarith [sq_nonneg x])

theorem circleBoundedTransformScalar_lipschitz :
    LipschitzWith 1 circleBoundedTransformScalar := by
  change LipschitzWith 1 (fun x => Real.sin (Real.arctan x))
  simpa [Function.comp_def] using
    Real.lipschitzWith_sin.comp circleArctan_lipschitz

/-! ## The bounded diagonal family -/

/-- Complex Fourier multiplier of the bounded transform. -/
def circleBoundedTransformMultiplier
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℂ :=
  (circleBoundedTransformScalar (diracEigenvalue fold twist mode) : ℂ)

theorem circleBoundedTransformMultiplier_norm_le_one
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    ‖circleBoundedTransformMultiplier fold twist mode‖ ≤ 1 := by
  simpa [circleBoundedTransformMultiplier, Complex.norm_real,
    Real.norm_eq_abs] using
      abs_circleBoundedTransformScalar_le_one
        (diracEigenvalue fold twist mode)

theorem circleBoundedTransformMultiplier_eq_zero_iff_eigenvalue
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleBoundedTransformMultiplier fold twist mode = 0 ↔
      complexDiracEigenvalue fold twist mode = 0 := by
  simp [circleBoundedTransformMultiplier, complexDiracEigenvalue,
    circleBoundedTransformScalar_eq_zero_iff]

/-- Actual bounded transform on the whole circle Hilbert space. -/
def circleBoundedTransform (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  circleDiagonalMultiplierCLM
    (circleBoundedTransformMultiplier fold twist)
    (circleBoundedTransformMultiplier_norm_le_one fold twist)

@[simp] theorem circleBoundedTransform_apply
    (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleBoundedTransform fold twist state mode =
      circleBoundedTransformMultiplier fold twist mode * state mode := by
  rfl

theorem circleBoundedTransform_apply_eq_normalizedDirac
    (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleBoundedTransform fold twist state mode =
      ((diracEigenvalue fold twist mode /
          Real.sqrt (1 + (diracEigenvalue fold twist mode) ^ 2) : ℝ) : ℂ) *
        state mode := by
  simp [circleBoundedTransformMultiplier,
    circleBoundedTransformScalar_eq]

/-- PT reverses the bounded first-order transform. -/
theorem circleBoundedTransformMultiplier_pt
    (twist : CircleTwist) (mode : ℤ) :
    circleBoundedTransformMultiplier .pt twist mode =
      -circleBoundedTransformMultiplier .positive twist mode := by
  simp [circleBoundedTransformMultiplier]

theorem circleBoundedTransform_pt
    (twist : CircleTwist) :
    circleBoundedTransform .pt twist =
      -circleBoundedTransform .positive twist := by
  ext state mode
  simp [circleBoundedTransformMultiplier_pt]

/-- The bounded transform is genuinely self-adjoint. -/
theorem circleBoundedTransform_isSelfAdjoint
    (fold : Fold) (twist : CircleTwist) :
    IsSelfAdjoint (circleBoundedTransform fold twist) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  simp [circleBoundedTransformMultiplier, mul_left_comm, mul_assoc]

theorem circleBoundedTransformMultiplier_sub_norm_le
    (fold : Fold) (first second : CircleTwist) (mode : ℤ) :
    ‖circleBoundedTransformMultiplier fold first mode -
        circleBoundedTransformMultiplier fold second mode‖ ≤
      |first.value - second.value| := by
  have hLip := circleBoundedTransformScalar_lipschitz.dist_le_mul
    (diracEigenvalue fold first mode) (diracEigenvalue fold second mode)
  change ‖(circleBoundedTransformScalar (diracEigenvalue fold first mode) : ℂ) -
      (circleBoundedTransformScalar (diracEigenvalue fold second mode) : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    |circleBoundedTransformScalar (diracEigenvalue fold first mode) -
        circleBoundedTransformScalar (diracEigenvalue fold second mode)|
        ≤ |diracEigenvalue fold first mode -
            diracEigenvalue fold second mode| := by
              simpa [Real.dist_eq] using hLip
    _ = |first.value - second.value| := by
      cases fold
      · simp [diracEigenvalue, baseEigenvalue]
      · simp only [diracEigenvalue, Fold.pt_spectralSign, baseEigenvalue]
        rw [show -1 * ((mode : ℝ) + first.value) -
            -1 * ((mode : ℝ) + second.value) =
              second.value - first.value by ring,
          abs_sub_comm]

/-- Operator-norm Lipschitz estimate for the holonomy family. -/
theorem circleBoundedTransform_norm_sub_le
    (fold : Fold) (first second : CircleTwist) :
    ‖circleBoundedTransform fold first -
        circleBoundedTransform fold second‖ ≤
      |first.value - second.value| := by
  let distance : ℝ := |first.value - second.value|
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro state
  calc
    ‖(circleBoundedTransform fold first -
        circleBoundedTransform fold second) state‖
        ≤ ‖(distance : ℂ) • state‖ := by
          apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
          intro mode
          have hCoordinate :
              ‖(circleBoundedTransformMultiplier fold first mode -
                  circleBoundedTransformMultiplier fold second mode) * state mode‖ ≤
                ‖(distance : ℂ) * state mode‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (abs_nonneg _)]
            exact mul_le_mul_of_nonneg_right
              (circleBoundedTransformMultiplier_sub_norm_le
                fold first second mode) (norm_nonneg _)
          have hLeft :
              ((circleBoundedTransform fold first -
                  circleBoundedTransform fold second) state) mode =
                (circleBoundedTransformMultiplier fold first mode -
                  circleBoundedTransformMultiplier fold second mode) * state mode := by
            change circleBoundedTransformMultiplier fold first mode * state mode -
                circleBoundedTransformMultiplier fold second mode * state mode = _
            ring
          have hRight :
              (((distance : ℂ) • state) : CircleHilbert) mode =
                (distance : ℂ) * state mode := rfl
          rw [hLeft, hRight]
          exact hCoordinate
    _ = distance * ‖state‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (abs_nonneg _)]

theorem circleBoundedTransform_lipschitz
    (fold : Fold) :
    LipschitzWith 1 fun twist : CircleTwist => circleBoundedTransform fold twist := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa [dist_eq_norm] using
    circleBoundedTransform_norm_sub_le fold first second

theorem circleBoundedTransform_continuous
    (fold : Fold) :
    Continuous fun twist : CircleTwist => circleBoundedTransform fold twist :=
  (circleBoundedTransform_lipschitz fold).continuous

/-! ## Fredholm pseudoinverse -/

theorem circleBoundedTransformScalar_inv_norm_le
    (x : ℝ) (hx : x ≠ 0) :
    ‖((circleBoundedTransformScalar x : ℂ))⁻¹‖ ≤
      ‖((x : ℂ))⁻¹‖ + 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    circleBoundedTransformScalar_eq, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_div,
    norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hxAbs : 0 < |x| := abs_pos.mpr hx
  have hSqrt : Real.sqrt (1 + x ^ 2) ≤ 1 + |x| := by
    simpa [Real.norm_eq_abs] using sqrt_one_add_norm_sq_le x
  calc
    Real.sqrt (1 + x ^ 2) / |x| ≤ (1 + |x|) / |x| :=
      (div_le_div_iff_of_pos_right hxAbs).2 hSqrt
    _ = |x|⁻¹ + 1 := by
      field_simp

/-- Uniform bound for the bounded-transform pseudoinverse at fixed holonomy. -/
def circleBoundedTransformPseudoinverseBound (twist : CircleTwist) : ℝ :=
  circlePseudoinverseBound twist + 1

theorem circleBoundedTransformPseudoinverseBound_nonnegative
    (twist : CircleTwist) :
    0 ≤ circleBoundedTransformPseudoinverseBound twist := by
  unfold circleBoundedTransformPseudoinverseBound
  linarith [circlePseudoinverseBound_nonnegative twist]

/-- Reciprocal bounded-transform multiplier, set to zero on the true kernel. -/
def circleBoundedTransformPseudoinverseMultiplier
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℂ :=
  if complexDiracEigenvalue fold twist mode = 0 then 0
  else (circleBoundedTransformMultiplier fold twist mode)⁻¹

theorem circleBoundedTransformPseudoinverseMultiplier_bound
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    ‖circleBoundedTransformPseudoinverseMultiplier fold twist mode‖ ≤
      circleBoundedTransformPseudoinverseBound twist := by
  by_cases hEigen : complexDiracEigenvalue fold twist mode = 0
  · simp [circleBoundedTransformPseudoinverseMultiplier, hEigen,
      circleBoundedTransformPseudoinverseBound_nonnegative]
  · have hReal : diracEigenvalue fold twist mode ≠ 0 := by
      intro hZero
      apply hEigen
      simp [complexDiracEigenvalue, hZero]
    have hScalar := circleBoundedTransformScalar_inv_norm_le
      (diracEigenvalue fold twist mode) hReal
    have hDiracInv :
        ‖(complexDiracEigenvalue fold twist mode)⁻¹‖ ≤
          circlePseudoinverseBound twist := by
      simpa [circleDiracPseudoinverseMultiplier, hEigen] using
        circleDiracPseudoinverseMultiplier_bound fold twist mode
    simp only [circleBoundedTransformPseudoinverseMultiplier, hEigen,
      ↓reduceIte]
    have hScalar' :
        ‖(circleBoundedTransformMultiplier fold twist mode)⁻¹‖ ≤
          ‖(complexDiracEigenvalue fold twist mode)⁻¹‖ + 1 := by
      simpa [circleBoundedTransformMultiplier, complexDiracEigenvalue] using
        hScalar
    exact hScalar'.trans (by
      unfold circleBoundedTransformPseudoinverseBound
      linarith)

def circleBoundedTransformPseudoinverseLinearMap
    (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →ₗ[ℂ] CircleHilbert where
  toFun state := ⟨fun mode =>
    circleBoundedTransformPseudoinverseMultiplier fold twist mode * state mode, by
      refine ((circleBoundedTransformPseudoinverseBound twist : ℂ) • state).2.mono' ?_
      intro mode
      change ‖circleBoundedTransformPseudoinverseMultiplier fold twist mode *
          state mode‖ ≤
        ‖(circleBoundedTransformPseudoinverseBound twist : ℂ) • state mode‖
      rw [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (circleBoundedTransformPseudoinverseBound_nonnegative twist)]
      exact mul_le_mul_of_nonneg_right
        (circleBoundedTransformPseudoinverseMultiplier_bound fold twist mode)
        (norm_nonneg _)⟩
  map_add' first second := by
    ext mode
    simp [mul_add]
  map_smul' scalar state := by
    ext mode
    simp [mul_left_comm]

def circleBoundedTransformPseudoinverseCLM
    (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (circleBoundedTransformPseudoinverseLinearMap fold twist).mkContinuous
    (circleBoundedTransformPseudoinverseBound twist) (by
      intro state
      rw [← show
        ‖(circleBoundedTransformPseudoinverseBound twist : ℂ) • state‖ =
            circleBoundedTransformPseudoinverseBound twist * ‖state‖ by
          simpa [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg
              (circleBoundedTransformPseudoinverseBound_nonnegative twist)] using
            norm_smul (circleBoundedTransformPseudoinverseBound twist : ℂ) state]
      apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
      intro mode
      change ‖circleBoundedTransformPseudoinverseMultiplier fold twist mode *
          state mode‖ ≤
        ‖(circleBoundedTransformPseudoinverseBound twist : ℂ) • state mode‖
      rw [norm_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (circleBoundedTransformPseudoinverseBound_nonnegative twist)]
      exact mul_le_mul_of_nonneg_right
        (circleBoundedTransformPseudoinverseMultiplier_bound fold twist mode)
        (norm_nonneg _))

@[simp] theorem circleBoundedTransformPseudoinverseCLM_apply
    (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleBoundedTransformPseudoinverseCLM fold twist state mode =
      circleBoundedTransformPseudoinverseMultiplier fold twist mode * state mode :=
  rfl

theorem circleBoundedTransform_mul_pseudoinverse_of_zeroRestriction
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert)
    (hRestriction : circleZeroRestriction fold twist state = 0)
    (mode : ℤ) :
    circleBoundedTransformMultiplier fold twist mode *
      circleBoundedTransformPseudoinverseCLM fold twist state mode =
        state mode := by
  by_cases hEigen : complexDiracEigenvalue fold twist mode = 0
  · have hAt := congrFun hRestriction
      (⟨mode, hEigen⟩ : CircleZeroMode fold twist)
    have hState : state mode = 0 := by
      change state mode = 0 at hAt
      exact hAt
    rw [circleBoundedTransformPseudoinverseCLM_apply]
    simp [circleBoundedTransformPseudoinverseMultiplier, hEigen, hState]
  · have hReal : diracEigenvalue fold twist mode ≠ 0 := by
      intro hZero
      apply hEigen
      simp [complexDiracEigenvalue, hZero]
    have hMultiplier :
        circleBoundedTransformMultiplier fold twist mode ≠ 0 := by
      intro hZero
      have hScalar :
          circleBoundedTransformScalar (diracEigenvalue fold twist mode) = 0 := by
        exact Complex.ofReal_eq_zero.mp hZero
      exact hReal (circleBoundedTransformScalar_eq_zero_iff _ |>.mp hScalar)
    rw [circleBoundedTransformPseudoinverseCLM_apply]
    simp [circleBoundedTransformPseudoinverseMultiplier, hEigen,
      hMultiplier]

/-- The bounded transform has exactly the same closed range as the graph Dirac operator. -/
theorem circleBoundedTransform_range_eq_zeroRestriction_ker
    (fold : Fold) (twist : CircleTwist) :
    LinearMap.range (circleBoundedTransform fold twist).toLinearMap =
      LinearMap.ker (circleZeroRestriction fold twist) := by
  apply le_antisymm
  · intro output hOutput
    rcases hOutput with ⟨state, rfl⟩
    rw [LinearMap.mem_ker]
    ext zeroMode
    change circleBoundedTransform fold twist state zeroMode.1 = 0
    rw [circleBoundedTransform_apply]
    have hReal : diracEigenvalue fold twist zeroMode.1 = 0 := by
      exact Complex.ofReal_eq_zero.mp zeroMode.property
    have hMultiplier :
        circleBoundedTransformMultiplier fold twist zeroMode.1 = 0 := by
      simp [circleBoundedTransformMultiplier, hReal]
    rw [hMultiplier, zero_mul]
  · intro output hOutput
    rw [LinearMap.mem_ker] at hOutput
    refine ⟨circleBoundedTransformPseudoinverseCLM fold twist output, ?_⟩
    ext mode
    exact circleBoundedTransform_mul_pseudoinverse_of_zeroRestriction
      fold twist output hOutput mode

theorem circleBoundedTransform_range_isClosed
    (fold : Fold) (twist : CircleTwist) :
    IsClosed
      (LinearMap.range (circleBoundedTransform fold twist).toLinearMap :
        Set CircleHilbert) := by
  rw [circleBoundedTransform_range_eq_zeroRestriction_ker]
  change IsClosed ((circleZeroRestrictionCLM fold twist).ker : Set CircleHilbert)
  exact (circleZeroRestrictionCLM fold twist).isClosed_ker

/-- Zero-mode coordinates on the kernel of the bounded transform. -/
def circleBoundedKernelZeroRestriction
    (fold : Fold) (twist : CircleTwist) :
    LinearMap.ker (circleBoundedTransform fold twist).toLinearMap →ₗ[ℂ]
      (CircleZeroMode fold twist → ℂ) where
  toFun state mode := state.1 mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem circleBoundedKernelZeroRestriction_injective
    (fold : Fold) (twist : CircleTwist) :
    Function.Injective (circleBoundedKernelZeroRestriction fold twist) := by
  intro first second hCoordinates
  apply Subtype.ext
  ext mode
  by_cases hEigen : complexDiracEigenvalue fold twist mode = 0
  · have hAt := congrFun hCoordinates
      (⟨mode, hEigen⟩ : CircleZeroMode fold twist)
    exact hAt
  · have hMultiplier :
        circleBoundedTransformMultiplier fold twist mode ≠ 0 := by
      exact fun hZero => hEigen
        ((circleBoundedTransformMultiplier_eq_zero_iff_eigenvalue
          fold twist mode).mp hZero)
    have hFirstImage : circleBoundedTransform fold twist first.1 = 0 :=
      first.property
    have hSecondImage : circleBoundedTransform fold twist second.1 = 0 :=
      second.property
    have hFirstAt := congrArg (fun state : CircleHilbert => state mode) hFirstImage
    have hSecondAt := congrArg (fun state : CircleHilbert => state mode) hSecondImage
    have hFirstZero : first.1 mode = 0 := by
      change circleBoundedTransformMultiplier fold twist mode * first.1 mode = 0 at hFirstAt
      exact (mul_eq_zero.mp hFirstAt).resolve_left hMultiplier
    have hSecondZero : second.1 mode = 0 := by
      change circleBoundedTransformMultiplier fold twist mode * second.1 mode = 0 at hSecondAt
      exact (mul_eq_zero.mp hSecondAt).resolve_left hMultiplier
    rw [hFirstZero, hSecondZero]

noncomputable instance circleBoundedTransformKernelFiniteDimensional
    (fold : Fold) (twist : CircleTwist) :
    FiniteDimensional ℂ
      (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap) :=
  FiniteDimensional.of_injective
    (circleBoundedKernelZeroRestriction fold twist)
    (circleBoundedKernelZeroRestriction_injective fold twist)

theorem circleBoundedKernelZeroRestriction_surjective
    (fold : Fold) (twist : CircleTwist) :
    Function.Surjective (circleBoundedKernelZeroRestriction fold twist) := by
  intro coefficients
  let state : CircleHilbert := circleZeroExtension fold twist coefficients
  have hKernel : state ∈
      LinearMap.ker (circleBoundedTransform fold twist).toLinearMap := by
    rw [LinearMap.mem_ker]
    ext mode
    by_cases hEigen : complexDiracEigenvalue fold twist mode = 0
    · have hMultiplier :
          circleBoundedTransformMultiplier fold twist mode = 0 :=
        (circleBoundedTransformMultiplier_eq_zero_iff_eigenvalue
          fold twist mode).2 hEigen
      change circleBoundedTransformMultiplier fold twist mode * state mode = 0
      rw [hMultiplier, zero_mul]
    · have hState : state mode = 0 := by
        simp [state, circleZeroExtension_apply, hEigen]
      change circleBoundedTransformMultiplier fold twist mode * state mode = 0
      rw [hState, mul_zero]
  refine ⟨⟨state, hKernel⟩, ?_⟩
  ext zeroMode
  change state zeroMode.1 = coefficients zeroMode
  simp [state, circleZeroExtension_apply, zeroMode.property]

theorem circleBoundedTransformKernel_finrank_eq_zeroModes
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ
        (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap) =
      Module.finrank ℂ (CircleZeroMode fold twist → ℂ) := by
  let equivalence := LinearEquiv.ofBijective
    (circleBoundedKernelZeroRestriction fold twist)
    ⟨circleBoundedKernelZeroRestriction_injective fold twist,
      circleBoundedKernelZeroRestriction_surjective fold twist⟩
  exact equivalence.finrank_eq

/-- Algebraic cokernel of the whole-space bounded transform. -/
abbrev CircleBoundedTransformCokernel
    (fold : Fold) (twist : CircleTwist) :=
  CircleHilbert ⧸ LinearMap.range
    (circleBoundedTransform fold twist).toLinearMap

noncomputable instance circleBoundedTransformCokernelFiniteDimensional
    (fold : Fold) (twist : CircleTwist) :
    FiniteDimensional ℂ (CircleBoundedTransformCokernel fold twist) := by
  let quotientEquivalence :
      CircleBoundedTransformCokernel fold twist ≃ₗ[ℂ]
        (CircleHilbert ⧸ LinearMap.ker (circleZeroRestriction fold twist)) :=
    Submodule.quotEquivOfEq _ _
      (circleBoundedTransform_range_eq_zeroRestriction_ker fold twist)
  let rangeEquivalence :=
    (circleZeroRestriction fold twist).quotKerEquivRange
  let finiteEmbedding := quotientEquivalence.trans rangeEquivalence
  exact FiniteDimensional.of_injective
    finiteEmbedding.toLinearMap finiteEmbedding.injective

theorem circleBoundedTransformCokernel_finrank_eq_zeroModes
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleBoundedTransformCokernel fold twist) =
      Module.finrank ℂ (CircleZeroMode fold twist → ℂ) := by
  let quotientEquivalence :
      CircleBoundedTransformCokernel fold twist ≃ₗ[ℂ]
        (CircleHilbert ⧸ LinearMap.ker (circleZeroRestriction fold twist)) :=
    Submodule.quotEquivOfEq _ _
      (circleBoundedTransform_range_eq_zeroRestriction_ker fold twist)
  let rangeEquivalence :=
    (circleZeroRestriction fold twist).quotKerEquivRange
  have hRange : LinearMap.range (circleZeroRestriction fold twist) = ⊤ :=
    LinearMap.range_eq_top.mpr (circleZeroRestriction_surjective fold twist)
  let topEquivalence :
      LinearMap.range (circleZeroRestriction fold twist) ≃ₗ[ℂ]
        (CircleZeroMode fold twist → ℂ) :=
    LinearEquiv.ofTop _ hRange
  exact (quotientEquivalence.trans
    (rangeEquivalence.trans topEquivalence)).finrank_eq

/-- All analytic Fredholm criteria for the bounded transform. -/
theorem circleBoundedTransform_fredholm_criterion
    (fold : Fold) (twist : CircleTwist) :
    IsClosed
        (LinearMap.range (circleBoundedTransform fold twist).toLinearMap :
          Set CircleHilbert) ∧
      FiniteDimensional ℂ
        (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap) ∧
      FiniteDimensional ℂ (CircleBoundedTransformCokernel fold twist) := by
  exact ⟨circleBoundedTransform_range_isClosed fold twist,
    inferInstance, inferInstance⟩

def circleBoundedTransformFredholmIndex
    (fold : Fold) (twist : CircleTwist) : ℤ :=
  (Module.finrank ℂ
      (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap) : ℤ) -
    (Module.finrank ℂ (CircleBoundedTransformCokernel fold twist) : ℤ)

theorem circleBoundedTransformFredholmIndex_zero
    (fold : Fold) (twist : CircleTwist) :
    circleBoundedTransformFredholmIndex fold twist = 0 := by
  rw [circleBoundedTransformFredholmIndex,
    circleBoundedTransformKernel_finrank_eq_zeroModes,
    circleBoundedTransformCokernel_finrank_eq_zeroModes]
  ring

/-! ## Exact zero crossings on the fundamental holonomy interval -/

/-- The second endpoint of the chosen fundamental holonomy interval. -/
def unitCircleTwist : CircleTwist where
  value := 1
  nonnegative := zero_le_one
  le_one := le_rfl

/-- Quarter holonomy. -/
def quarterCircleTwist : CircleTwist where
  value := 1 / 4
  nonnegative := by norm_num
  le_one := by norm_num

/-- Three-quarter holonomy. -/
def threeQuarterCircleTwist : CircleTwist where
  value := 3 / 4
  nonnegative := by norm_num
  le_one := by norm_num

theorem complexDiracEigenvalue_eq_zero_iff_endpoints
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    complexDiracEigenvalue fold twist mode = 0 ↔
      (twist.value = 0 ∧ mode = 0) ∨
      (twist.value = 1 ∧ mode = -1) := by
  constructor
  · intro hEigen
    have hReal : diracEigenvalue fold twist mode = 0 := by
      apply Complex.ofReal_eq_zero.mp
      exact hEigen
    have hBase : (mode : ℝ) + twist.value = 0 := by
      cases fold
      · simpa [diracEigenvalue, baseEigenvalue] using hReal
      · simp [diracEigenvalue, baseEigenvalue] at hReal
        linarith
    have hLowerReal : (-1 : ℝ) ≤ (mode : ℝ) := by
      linarith [twist.le_one]
    have hUpperReal : (mode : ℝ) ≤ 0 := by
      linarith [twist.nonnegative]
    have hLower : (-1 : ℤ) ≤ mode := by
      exact_mod_cast hLowerReal
    have hUpper : mode ≤ (0 : ℤ) := by
      exact_mod_cast hUpperReal
    interval_cases mode
    · right
      constructor
      · norm_num at hBase ⊢
        linarith
      · rfl
    · left
      constructor
      · norm_num at hBase ⊢
        linarith
      · rfl
  · rintro (⟨hTwist, rfl⟩ | ⟨hTwist, rfl⟩) <;>
      cases fold <;>
      simp [complexDiracEigenvalue, diracEigenvalue, baseEigenvalue, hTwist]

theorem circleBoundedTransformMultiplier_eq_zero_iff_endpoints
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleBoundedTransformMultiplier fold twist mode = 0 ↔
      (twist.value = 0 ∧ mode = 0) ∨
      (twist.value = 1 ∧ mode = -1) := by
  rw [circleBoundedTransformMultiplier,
    Complex.ofReal_eq_zero, circleBoundedTransformScalar_eq_zero_iff]
  simpa [complexDiracEigenvalue] using
    complexDiracEigenvalue_eq_zero_iff_endpoints fold twist mode

theorem circleBoundedTransformMultiplier_ne_zero_of_interior
    (fold : Fold) (twist : CircleTwist)
    (hLower : 0 < twist.value) (hUpper : twist.value < 1)
    (mode : ℤ) :
    circleBoundedTransformMultiplier fold twist mode ≠ 0 := by
  intro hZero
  rcases (circleBoundedTransformMultiplier_eq_zero_iff_endpoints
    fold twist mode).mp hZero with hEndpoint | hEndpoint
  · exact hLower.ne' hEndpoint.1
  · exact hUpper.ne hEndpoint.1

theorem quarterCircleTwist_no_crossing
    (fold : Fold) (mode : ℤ) :
    circleBoundedTransformMultiplier fold quarterCircleTwist mode ≠ 0 := by
  apply circleBoundedTransformMultiplier_ne_zero_of_interior
  · norm_num [quarterCircleTwist]
  · norm_num [quarterCircleTwist]

theorem threeQuarterCircleTwist_no_crossing
    (fold : Fold) (mode : ℤ) :
    circleBoundedTransformMultiplier fold threeQuarterCircleTwist mode ≠ 0 := by
  apply circleBoundedTransformMultiplier_ne_zero_of_interior
  · norm_num [threeQuarterCircleTwist]
  · norm_num [threeQuarterCircleTwist]

/-- At the periodic endpoint the unique zero Fourier label is `0`. -/
theorem periodic_crossing_mode_iff
    (fold : Fold) (mode : ℤ) :
    circleBoundedTransformMultiplier fold periodicTwist mode = 0 ↔ mode = 0 := by
  simp [circleBoundedTransformMultiplier_eq_zero_iff_endpoints, periodicTwist]

/-- At the unit endpoint the unique zero Fourier label is `-1`. -/
theorem unit_crossing_mode_iff
    (fold : Fold) (mode : ℤ) :
    circleBoundedTransformMultiplier fold unitCircleTwist mode = 0 ↔ mode = -1 := by
  simp [circleBoundedTransformMultiplier_eq_zero_iff_endpoints, unitCircleTwist]

theorem circleBoundedTransformKernel_finrank_eq_zeroMode_card
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ
        (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap) =
      Fintype.card (CircleZeroMode fold twist) := by
  rw [circleBoundedTransformKernel_finrank_eq_zeroModes]
  simp

/-- The periodic endpoint kernel is exactly one-dimensional. -/
theorem periodic_boundedTransform_kernel_finrank_one
    (fold : Fold) :
    Module.finrank ℂ
        (LinearMap.ker (circleBoundedTransform fold periodicTwist).toLinearMap) = 1 := by
  letI : Unique (CircleZeroMode fold periodicTwist) := {
    default := ⟨0, by
      simp [complexDiracEigenvalue, diracEigenvalue, baseEigenvalue,
        periodicTwist]⟩
    uniq zeroMode := by
      apply Subtype.ext
      apply (periodic_crossing_mode_iff fold zeroMode.1).mp
      exact (circleBoundedTransformMultiplier_eq_zero_iff_eigenvalue
        fold periodicTwist zeroMode.1).2 zeroMode.property }
  rw [circleBoundedTransformKernel_finrank_eq_zeroMode_card]
  exact Fintype.card_unique

/-- The unit endpoint kernel is exactly one-dimensional. -/
theorem unit_boundedTransform_kernel_finrank_one
    (fold : Fold) :
    Module.finrank ℂ
        (LinearMap.ker (circleBoundedTransform fold unitCircleTwist).toLinearMap) = 1 := by
  letI : Unique (CircleZeroMode fold unitCircleTwist) := {
    default := ⟨-1, by
      simp [complexDiracEigenvalue, diracEigenvalue, baseEigenvalue,
        unitCircleTwist]⟩
    uniq zeroMode := by
      apply Subtype.ext
      apply (unit_crossing_mode_iff fold zeroMode.1).mp
      exact (circleBoundedTransformMultiplier_eq_zero_iff_eigenvalue
        fold unitCircleTwist zeroMode.1).2 zeroMode.property }
  rw [circleBoundedTransformKernel_finrank_eq_zeroMode_card]
  exact Fintype.card_unique

/-- Every strict-interior holonomy has zero-dimensional kernel. -/
theorem interior_boundedTransform_kernel_finrank_zero
    (fold : Fold) (twist : CircleTwist)
    (hLower : 0 < twist.value) (hUpper : twist.value < 1) :
    Module.finrank ℂ
        (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap) = 0 := by
  letI : IsEmpty (CircleZeroMode fold twist) :=
    ⟨fun zeroMode =>
      (circleBoundedTransformMultiplier_ne_zero_of_interior
        fold twist hLower hUpper zeroMode.1)
        ((circleBoundedTransformMultiplier_eq_zero_iff_eigenvalue
          fold twist zeroMode.1).2 zeroMode.property)⟩
  rw [circleBoundedTransformKernel_finrank_eq_zeroMode_card]
  exact Fintype.card_eq_zero

/-- The bounded transform is actually bijective away from the two endpoint crossings. -/
theorem circleBoundedTransform_bijective_of_interior
    (fold : Fold) (twist : CircleTwist)
    (hLower : 0 < twist.value) (hUpper : twist.value < 1) :
    Function.Bijective (circleBoundedTransform fold twist) := by
  constructor
  · intro first second hImage
    ext mode
    have hAt := congrArg (fun state : CircleHilbert => state mode) hImage
    change circleBoundedTransformMultiplier fold twist mode * first mode =
      circleBoundedTransformMultiplier fold twist mode * second mode at hAt
    exact mul_left_cancel₀
      (circleBoundedTransformMultiplier_ne_zero_of_interior
        fold twist hLower hUpper mode) hAt
  · intro output
    have hRestriction : circleZeroRestriction fold twist output = 0 := by
      ext zeroMode
      exact False.elim
        ((circleBoundedTransformMultiplier_ne_zero_of_interior
          fold twist hLower hUpper zeroMode.1)
          ((circleBoundedTransformMultiplier_eq_zero_iff_eigenvalue
            fold twist zeroMode.1).2 zeroMode.property))
    refine ⟨circleBoundedTransformPseudoinverseCLM fold twist output, ?_⟩
    ext mode
    exact circleBoundedTransform_mul_pseudoinverse_of_zeroRestriction
      fold twist output hRestriction mode

theorem quarterCircleBoundedTransform_bijective
    (fold : Fold) :
    Function.Bijective (circleBoundedTransform fold quarterCircleTwist) := by
  apply circleBoundedTransform_bijective_of_interior
  · norm_num [quarterCircleTwist]
  · norm_num [quarterCircleTwist]

theorem threeQuarterCircleBoundedTransform_bijective
    (fold : Fold) :
    Function.Bijective (circleBoundedTransform fold threeQuarterCircleTwist) := by
  apply circleBoundedTransform_bijective_of_interior
  · norm_num [threeQuarterCircleTwist]
  · norm_num [threeQuarterCircleTwist]

theorem quarter_to_threeQuarter_norm_le_half
    (fold : Fold) :
    ‖circleBoundedTransform fold quarterCircleTwist -
        circleBoundedTransform fold threeQuarterCircleTwist‖ ≤ 1 / 2 := by
  exact (circleBoundedTransform_norm_sub_le
    fold quarterCircleTwist threeQuarterCircleTwist).trans_eq (by
      norm_num [quarterCircleTwist, threeQuarterCircleTwist])

/-- Unit holonomy is periodic holonomy after the exact Fourier relabeling `n ↦ n+1`. -/
theorem diracEigenvalue_unit_relabel
    (fold : Fold) (mode : ℤ) :
    diracEigenvalue fold unitCircleTwist mode =
      diracEigenvalue fold periodicTwist (mode + 1) := by
  cases fold <;> simp [diracEigenvalue, baseEigenvalue,
    unitCircleTwist, periodicTwist]

/-- The two endpoint kernels are the same crossing after large-gauge relabeling. -/
def unitPeriodicZeroModeEquiv (fold : Fold) :
    CircleZeroMode fold unitCircleTwist ≃
      CircleZeroMode fold periodicTwist where
  toFun zeroMode := ⟨zeroMode.1 + 1, by
    change (diracEigenvalue fold periodicTwist (zeroMode.1 + 1) : ℂ) = 0
    rw [← diracEigenvalue_unit_relabel]
    exact zeroMode.property⟩
  invFun zeroMode := ⟨zeroMode.1 - 1, by
    change (diracEigenvalue fold unitCircleTwist (zeroMode.1 - 1) : ℂ) = 0
    rw [diracEigenvalue_unit_relabel]
    simpa [complexDiracEigenvalue] using zeroMode.property⟩
  left_inv zeroMode := by
    apply Subtype.ext
    change zeroMode.1 + 1 - 1 = zeroMode.1
    omega
  right_inv zeroMode := by
    apply Subtype.ext
    change zeroMode.1 - 1 + 1 = zeroMode.1
    omega

theorem boundedTransformMultiplier_unit_relabel
    (fold : Fold) (mode : ℤ) :
    circleBoundedTransformMultiplier fold unitCircleTwist mode =
      circleBoundedTransformMultiplier fold periodicTwist (mode + 1) := by
  simp [circleBoundedTransformMultiplier, diracEigenvalue_unit_relabel]

/-- The affine eigenvalue path has PT-opposite constant crossing orientation. -/
theorem diracEigenvalue_holonomy_difference
    (fold : Fold) (first second : CircleTwist) (mode : ℤ) :
    diracEigenvalue fold second mode - diracEigenvalue fold first mode =
      fold.spectralSign * (second.value - first.value) := by
  simp [diracEigenvalue, baseEigenvalue]
  ring

/-- Oriented crossing count for one fundamental holonomy winding. -/
def circleFundamentalCrossing : Fold → ℤ
  | .positive => 1
  | .pt => -1

@[simp] theorem positive_fundamental_crossing :
    circleFundamentalCrossing .positive = 1 := rfl

@[simp] theorem pt_fundamental_crossing :
    circleFundamentalCrossing .pt = -1 := rfl

theorem fundamental_holonomy_eigenvalue_increment
    (fold : Fold) (mode : ℤ) :
    diracEigenvalue fold unitCircleTwist mode -
        diracEigenvalue fold periodicTwist mode =
      (circleFundamentalCrossing fold : ℝ) := by
  cases fold <;> simp [diracEigenvalue, baseEigenvalue,
    unitCircleTwist, periodicTwist, circleFundamentalCrossing]

theorem pt_reverses_fundamental_crossing :
    circleFundamentalCrossing .pt =
      -circleFundamentalCrossing .positive := by
  rfl

end

end P0EFTJanusCircleBoundedTransformSpectralFlow
end JanusFormal
