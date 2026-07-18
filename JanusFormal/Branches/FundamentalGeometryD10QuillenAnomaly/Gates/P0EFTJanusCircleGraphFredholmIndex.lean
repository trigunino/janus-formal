import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleHolonomyCommonDomainCompactResolvent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Graph-norm Fredholm structure of the infinite circle Dirac operator

The closed graph is used as the Banach/Hilbert graph-norm domain.  The same
infinite Fourier operator then becomes bounded into the ambient Hilbert space.
This gate identifies its finite kernel and cokernel from the actual zero
Fourier modes and proves index zero.  It also constructs the corresponding
one-dimensional determinant-line fiber.

This remains the normalized circle family, not the global Janus family or a
Quillen metric/connection.
-/

namespace JanusFormal
namespace P0EFTJanusCircleGraphFredholmIndex

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleHolonomyCommonDomainCompactResolvent
open scoped ENNReal lp

/-- Closed graph, carrying the inherited graph norm from `H × H`. -/
abbrev CircleGraphDomain (fold : Fold) (twist : CircleTwist) :=
  (circleUnboundedDirac fold twist).graph

noncomputable instance circleGraphDomainCompleteSpace
    (fold : Fold) (twist : CircleTwist) :
    CompleteSpace (CircleGraphDomain fold twist) := by
  letI : IsClosed
      ((circleUnboundedDirac fold twist).graph :
        Set (CircleHilbert × CircleHilbert)) :=
    circleUnboundedDirac_isClosed fold twist
  infer_instance

/-- First projection is the graph-norm inclusion into the circle Hilbert space. -/
def circleGraphFstCLM (fold : Fold) (twist : CircleTwist) :
    CircleGraphDomain fold twist →L[ℂ] CircleHilbert :=
  (ContinuousLinearMap.fst ℂ CircleHilbert CircleHilbert).comp
    ((circleUnboundedDirac fold twist).graph.subtypeL)

/-- The unbounded Dirac operator becomes bounded on its graph-norm domain. -/
def circleGraphDiracCLM (fold : Fold) (twist : CircleTwist) :
    CircleGraphDomain fold twist →L[ℂ] CircleHilbert :=
  (ContinuousLinearMap.snd ℂ CircleHilbert CircleHilbert).comp
    ((circleUnboundedDirac fold twist).graph.subtypeL)

@[simp] theorem circleGraphFstCLM_apply
    (fold : Fold) (twist : CircleTwist)
    (state : CircleGraphDomain fold twist) :
    circleGraphFstCLM fold twist state = state.1.1 := rfl

@[simp] theorem circleGraphDiracCLM_apply
    (fold : Fold) (twist : CircleTwist)
    (state : CircleGraphDomain fold twist) :
    circleGraphDiracCLM fold twist state = state.1.2 := rfl

theorem circleGraphDiracCLM_norm_le
    (fold : Fold) (twist : CircleTwist)
    (state : CircleGraphDomain fold twist) :
    ‖circleGraphDiracCLM fold twist state‖ ≤ ‖state‖ := by
  exact norm_snd_le _

/-- The graph relation is the original infinite Fourier multiplier relation. -/
theorem circleGraphDomain_relation
    (fold : Fold) (twist : CircleTwist)
    (state : CircleGraphDomain fold twist) (mode : ℤ) :
    state.1.2 mode =
      complexDiracEigenvalue fold twist mode * state.1.1 mode := by
  exact (mem_circleUnboundedDirac_graph_iff fold twist state.1).mp
    state.property mode

/-- Integer Fourier modes where the actual circle eigenvalue vanishes. -/
def CircleZeroMode (fold : Fold) (twist : CircleTwist) :=
  {mode : ℤ // complexDiracEigenvalue fold twist mode = 0}

theorem circleZeroMode_set_finite (fold : Fold) (twist : CircleTwist) :
    Set.Finite {mode : ℤ | complexDiracEigenvalue fold twist mode = 0} := by
  apply (circleDirac_bounded_window_finite fold twist 0).subset
  intro mode hMode
  simp [hMode]

noncomputable instance circleZeroModeFintype
    (fold : Fold) (twist : CircleTwist) :
    Fintype (CircleZeroMode fold twist) :=
  (circleZeroMode_set_finite fold twist).fintype

/-- Restriction of an `ℓ²` state to the finite set of zero Fourier modes. -/
def circleZeroRestriction (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →ₗ[ℂ] (CircleZeroMode fold twist → ℂ) where
  toFun state mode := state mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the finite zero-mode set is bounded by the ambient `ℓ²` norm. -/
def circleZeroRestrictionCLM (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] (CircleZeroMode fold twist → ℂ) :=
  LinearMap.mkContinuous (circleZeroRestriction fold twist) 1 (by
    intro state
    rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg state)]
    intro mode
    exact lp.norm_apply_le_norm (by norm_num) state mode.1)

@[simp] theorem circleZeroRestrictionCLM_apply
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert) :
    circleZeroRestrictionCLM fold twist state =
      circleZeroRestriction fold twist state := rfl

/-- Finite Fourier extension supported exactly on the zero modes. -/
def circleZeroExtension (fold : Fold) (twist : CircleTwist) :
    (CircleZeroMode fold twist → ℂ) →ₗ[ℂ] CircleHilbert where
  toFun coefficients := ⟨fun mode =>
    if hZero : complexDiracEigenvalue fold twist mode = 0 then
      coefficients ⟨mode, hZero⟩
    else 0, by
      apply memℓp_gen
      apply summable_of_ne_finset_zero
        (s := (circleZeroMode_set_finite fold twist).toFinset)
      intro mode hMode
      have hNotZero : complexDiracEigenvalue fold twist mode ≠ 0 := by
        intro hZero
        apply hMode
        simpa using hZero
      simp [hNotZero]⟩
  map_add' first second := by
    ext mode
    by_cases hZero : complexDiracEigenvalue fold twist mode = 0
    · simp [hZero]
    · simp [hZero]
  map_smul' scalar coefficients := by
    ext mode
    by_cases hZero : complexDiracEigenvalue fold twist mode = 0
    · simp [hZero]
    · simp [hZero]

theorem circleZeroExtension_apply
    (fold : Fold) (twist : CircleTwist)
    (coefficients : CircleZeroMode fold twist → ℂ) (mode : ℤ) :
    circleZeroExtension fold twist coefficients mode =
      if hZero : complexDiracEigenvalue fold twist mode = 0 then
        coefficients ⟨mode, hZero⟩
      else 0 := by
  rfl

theorem circleZeroRestriction_zeroExtension
    (fold : Fold) (twist : CircleTwist)
    (coefficients : CircleZeroMode fold twist → ℂ) :
    circleZeroRestriction fold twist
      (circleZeroExtension fold twist coefficients) = coefficients := by
  ext mode
  simp [circleZeroRestriction, circleZeroExtension_apply, mode.property]

theorem circleZeroRestriction_surjective
    (fold : Fold) (twist : CircleTwist) :
    Function.Surjective (circleZeroRestriction fold twist) := by
  intro coefficients
  exact ⟨circleZeroExtension fold twist coefficients,
    circleZeroRestriction_zeroExtension fold twist coefficients⟩

/-- Coordinates of a graph-kernel element on the finite zero-mode set. -/
def circleGraphKernelZeroRestriction (fold : Fold) (twist : CircleTwist) :
    LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap →ₗ[ℂ]
      (CircleZeroMode fold twist → ℂ) where
  toFun state mode := state.1.1.1 mode.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem circleGraphKernelZeroRestriction_injective
    (fold : Fold) (twist : CircleTwist) :
    Function.Injective (circleGraphKernelZeroRestriction fold twist) := by
  intro first second hCoordinates
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · ext mode
    by_cases hZero : complexDiracEigenvalue fold twist mode = 0
    · have hAt := congrFun hCoordinates ⟨mode, hZero⟩
      exact hAt
    · have hFirstImage : first.1.1.2 = 0 := by
        exact first.property
      have hSecondImage : second.1.1.2 = 0 := by
        exact second.property
      have hFirstRelation := circleGraphDomain_relation fold twist first.1 mode
      have hSecondRelation := circleGraphDomain_relation fold twist second.1 mode
      have hFirstAt : first.1.1.2 mode = 0 := by
        have hAt := congrArg (fun state : CircleHilbert => state mode) hFirstImage
        simpa using hAt
      have hSecondAt : second.1.1.2 mode = 0 := by
        have hAt := congrArg (fun state : CircleHilbert => state mode) hSecondImage
        simpa using hAt
      rw [hFirstAt] at hFirstRelation
      rw [hSecondAt] at hSecondRelation
      have hFirstZero : first.1.1.1 mode = 0 := by
        exact (mul_eq_zero.mp hFirstRelation.symm).resolve_left hZero
      have hSecondZero : second.1.1.1 mode = 0 := by
        exact (mul_eq_zero.mp hSecondRelation.symm).resolve_left hZero
      rw [hFirstZero, hSecondZero]
  · exact first.property.trans second.property.symm

/-- The graph-norm circle Dirac kernel is genuinely finite-dimensional. -/
noncomputable instance circleGraphDiracKernelFiniteDimensional
    (fold : Fold) (twist : CircleTwist) :
    FiniteDimensional ℂ
      (LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap) :=
  FiniteDimensional.of_injective
    (circleGraphKernelZeroRestriction fold twist)
    (circleGraphKernelZeroRestriction_injective fold twist)

/-! ## Closed range and finite cokernel -/

theorem complexDiracEigenvalue_norm_eq_abs_base
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    ‖complexDiracEigenvalue fold twist mode‖ =
      |baseEigenvalue twist mode| := by
  cases fold <;>
    simp [complexDiracEigenvalue, diracEigenvalue,
      Complex.norm_real, Real.norm_eq_abs]

theorem one_le_abs_baseEigenvalue_of_ne_zero_neg_one
    (twist : CircleTwist) (mode : ℤ)
    (hZero : mode ≠ 0) (hNegOne : mode ≠ -1) :
    1 ≤ |baseEigenvalue twist mode| := by
  rcases lt_or_gt_of_ne hZero with hNegative | hPositive
  · have hMode : mode ≤ -2 := by omega
    have hModeReal : (mode : ℝ) ≤ -2 := by exact_mod_cast hMode
    have hBase : baseEigenvalue twist mode ≤ -1 := by
      unfold baseEigenvalue
      linarith [twist.le_one]
    rw [abs_of_nonpos (hBase.trans (by norm_num))]
    linarith
  · have hMode : (1 : ℤ) ≤ mode := by omega
    have hModeReal : (1 : ℝ) ≤ (mode : ℝ) := by exact_mod_cast hMode
    have hBase : 1 ≤ baseEigenvalue twist mode := by
      unfold baseEigenvalue
      linarith [twist.nonnegative]
    rw [abs_of_nonneg (zero_le_one.trans hBase)]
    exact hBase

/-- Uniform bound for the reciprocal of every nonzero circle eigenvalue. -/
def circlePseudoinverseBound (twist : CircleTwist) : ℝ :=
  max 1 (max twist.value⁻¹ (1 - twist.value)⁻¹)

theorem circlePseudoinverseBound_nonnegative (twist : CircleTwist) :
    0 ≤ circlePseudoinverseBound twist :=
  zero_le_one.trans (le_max_left _ _)

/-- Reciprocal on nonzero modes and zero on the actual zero modes. -/
def circleDiracPseudoinverseMultiplier
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℂ :=
  if complexDiracEigenvalue fold twist mode = 0 then 0
  else (complexDiracEigenvalue fold twist mode)⁻¹

theorem circleDiracPseudoinverseMultiplier_bound
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    ‖circleDiracPseudoinverseMultiplier fold twist mode‖ ≤
      circlePseudoinverseBound twist := by
  by_cases hEigen : complexDiracEigenvalue fold twist mode = 0
  · simp [circleDiracPseudoinverseMultiplier, hEigen,
      circlePseudoinverseBound_nonnegative]
  · simp only [circleDiracPseudoinverseMultiplier, hEigen, ↓reduceIte,
      norm_inv]
    by_cases hModeZero : mode = 0
    · subst mode
      have hNorm : ‖complexDiracEigenvalue fold twist 0‖ = twist.value := by
        rw [complexDiracEigenvalue_norm_eq_abs_base]
        simp [baseEigenvalue, abs_of_nonneg twist.nonnegative]
      rw [hNorm]
      exact (le_max_left twist.value⁻¹ (1 - twist.value)⁻¹).trans
        (le_max_right 1 (max twist.value⁻¹ (1 - twist.value)⁻¹))
    · by_cases hModeNegOne : mode = -1
      · subst mode
        have hNorm :
            ‖complexDiracEigenvalue fold twist (-1)‖ = 1 - twist.value := by
          rw [complexDiracEigenvalue_norm_eq_abs_base]
          simp only [baseEigenvalue, Int.cast_neg, Int.cast_one]
          rw [abs_of_nonpos]
          · ring
          · linarith [twist.le_one]
        rw [hNorm]
        exact (le_max_right twist.value⁻¹ (1 - twist.value)⁻¹).trans
          (le_max_right 1 (max twist.value⁻¹ (1 - twist.value)⁻¹))
      · have hNorm : 1 ≤ ‖complexDiracEigenvalue fold twist mode‖ := by
          rw [complexDiracEigenvalue_norm_eq_abs_base]
          exact one_le_abs_baseEigenvalue_of_ne_zero_neg_one
            twist mode hModeZero hModeNegOne
        exact (inv_le_one_of_one_le₀ hNorm).trans
          (le_max_left 1 (max twist.value⁻¹ (1 - twist.value)⁻¹))

def circleDiracPseudoinverseLinearMap
    (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →ₗ[ℂ] CircleHilbert where
  toFun state := ⟨fun mode =>
    circleDiracPseudoinverseMultiplier fold twist mode * state mode, by
      refine ((circlePseudoinverseBound twist : ℂ) • state).2.mono' ?_
      intro mode
      change ‖circleDiracPseudoinverseMultiplier fold twist mode * state mode‖ ≤
        ‖(circlePseudoinverseBound twist : ℂ) • state mode‖
      rw [norm_mul, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (circlePseudoinverseBound_nonnegative twist)]
      exact mul_le_mul_of_nonneg_right
        (circleDiracPseudoinverseMultiplier_bound fold twist mode)
        (norm_nonneg (state mode))⟩
  map_add' first second := by
    ext mode
    simp [mul_add]
  map_smul' scalar state := by
    ext mode
    simp [mul_left_comm]

def circleDiracPseudoinverseCLM
    (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (circleDiracPseudoinverseLinearMap fold twist).mkContinuous
    (circlePseudoinverseBound twist)
    (by
      intro state
      rw [← show
        ‖(circlePseudoinverseBound twist : ℂ) • state‖ =
          circlePseudoinverseBound twist * ‖state‖ by
        simpa [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (circlePseudoinverseBound_nonnegative twist)] using
            norm_smul (circlePseudoinverseBound twist : ℂ) state]
      apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
      intro mode
      change ‖circleDiracPseudoinverseMultiplier fold twist mode * state mode‖ ≤
        ‖(circlePseudoinverseBound twist : ℂ) • state mode‖
      rw [norm_mul, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (circlePseudoinverseBound_nonnegative twist)]
      exact mul_le_mul_of_nonneg_right
        (circleDiracPseudoinverseMultiplier_bound fold twist mode)
        (norm_nonneg (state mode)))

@[simp] theorem circleDiracPseudoinverseCLM_apply
    (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleDiracPseudoinverseCLM fold twist state mode =
      circleDiracPseudoinverseMultiplier fold twist mode * state mode := rfl

theorem circleDirac_mul_pseudoinverse_of_zeroRestriction
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert)
    (hRestriction : circleZeroRestriction fold twist state = 0)
    (mode : ℤ) :
    complexDiracEigenvalue fold twist mode *
      circleDiracPseudoinverseCLM fold twist state mode = state mode := by
  by_cases hEigen : complexDiracEigenvalue fold twist mode = 0
  · have hAt := congrFun hRestriction
      (⟨mode, hEigen⟩ : CircleZeroMode fold twist)
    have hState : state mode = 0 := by
      change state mode = 0 at hAt
      exact hAt
    rw [hEigen, zero_mul, hState]
  · rw [circleDiracPseudoinverseCLM_apply]
    simp [circleDiracPseudoinverseMultiplier, hEigen]

/-- The actual graph-operator range is exactly the subspace vanishing on zero modes. -/
theorem circleGraphDirac_range_eq_zeroRestriction_ker
    (fold : Fold) (twist : CircleTwist) :
    LinearMap.range (circleGraphDiracCLM fold twist).toLinearMap =
      LinearMap.ker (circleZeroRestriction fold twist) := by
  apply le_antisymm
  · intro output hOutput
    rcases hOutput with ⟨graphState, rfl⟩
    rw [LinearMap.mem_ker]
    ext zeroMode
    change graphState.1.2 zeroMode.1 = 0
    rw [circleGraphDomain_relation fold twist graphState zeroMode.1,
      zeroMode.property, zero_mul]
  · intro output hOutput
    rw [LinearMap.mem_ker] at hOutput
    let preimage : CircleHilbert :=
      circleDiracPseudoinverseCLM fold twist output
    have hGraph : (preimage, output) ∈
        (circleUnboundedDirac fold twist).graph := by
      rw [mem_circleUnboundedDirac_graph_iff]
      intro mode
      exact (circleDirac_mul_pseudoinverse_of_zeroRestriction
        fold twist output hOutput mode).symm
    let graphState : CircleGraphDomain fold twist :=
      ⟨(preimage, output), hGraph⟩
    refine ⟨graphState, ?_⟩
    rfl

/-- The graph-norm realization has closed range. -/
theorem circleGraphDirac_range_isClosed
    (fold : Fold) (twist : CircleTwist) :
    IsClosed
      (LinearMap.range (circleGraphDiracCLM fold twist).toLinearMap :
        Set CircleHilbert) := by
  rw [circleGraphDirac_range_eq_zeroRestriction_ker]
  change IsClosed ((circleZeroRestrictionCLM fold twist).ker : Set CircleHilbert)
  exact (circleZeroRestrictionCLM fold twist).isClosed_ker

/-- Algebraic cokernel of the bounded graph-norm realization. -/
abbrev CircleGraphCokernel (fold : Fold) (twist : CircleTwist) :=
  CircleHilbert ⧸ LinearMap.range
    (circleGraphDiracCLM fold twist).toLinearMap

/-- The graph-norm circle Dirac cokernel is genuinely finite-dimensional. -/
noncomputable instance circleGraphDiracCokernelFiniteDimensional
    (fold : Fold) (twist : CircleTwist) :
    FiniteDimensional ℂ (CircleGraphCokernel fold twist) := by
  let quotientEquivalence :
      CircleGraphCokernel fold twist ≃ₗ[ℂ]
        (CircleHilbert ⧸ LinearMap.ker (circleZeroRestriction fold twist)) :=
    Submodule.quotEquivOfEq _ _
      (circleGraphDirac_range_eq_zeroRestriction_ker fold twist)
  let rangeEquivalence :=
    (circleZeroRestriction fold twist).quotKerEquivRange
  let finiteEmbedding := quotientEquivalence.trans rangeEquivalence
  exact FiniteDimensional.of_injective
    finiteEmbedding.toLinearMap finiteEmbedding.injective

/-- The three analytic Fredholm criteria hold for the bounded graph realization. -/
theorem circleGraphDirac_fredholm_criterion
    (fold : Fold) (twist : CircleTwist) :
    IsClosed
        (LinearMap.range (circleGraphDiracCLM fold twist).toLinearMap :
          Set CircleHilbert) ∧
      FiniteDimensional ℂ
        (LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap) ∧
      FiniteDimensional ℂ (CircleGraphCokernel fold twist) := by
  exact ⟨circleGraphDirac_range_isClosed fold twist,
    inferInstance, inferInstance⟩

theorem circleGraphKernelZeroRestriction_surjective
    (fold : Fold) (twist : CircleTwist) :
    Function.Surjective (circleGraphKernelZeroRestriction fold twist) := by
  intro coefficients
  let state : CircleHilbert := circleZeroExtension fold twist coefficients
  have hGraph : (state, (0 : CircleHilbert)) ∈
      (circleUnboundedDirac fold twist).graph := by
    rw [mem_circleUnboundedDirac_graph_iff]
    intro mode
    change 0 = complexDiracEigenvalue fold twist mode * state mode
    by_cases hEigen : complexDiracEigenvalue fold twist mode = 0
    · rw [hEigen, zero_mul]
    · rw [show state mode = 0 by
        simp [state, circleZeroExtension_apply, hEigen], mul_zero]
  let graphState : CircleGraphDomain fold twist :=
    ⟨(state, 0), hGraph⟩
  have hKernel : graphState ∈
      LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap := by
    rfl
  refine ⟨⟨graphState, hKernel⟩, ?_⟩
  ext zeroMode
  change state zeroMode.1 = coefficients zeroMode
  simp [state, circleZeroExtension_apply, zeroMode.property]

theorem circleGraphKernel_finrank_eq_zeroModes
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ
        (LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap) =
      Module.finrank ℂ (CircleZeroMode fold twist → ℂ) := by
  let equivalence := LinearEquiv.ofBijective
    (circleGraphKernelZeroRestriction fold twist)
    ⟨circleGraphKernelZeroRestriction_injective fold twist,
      circleGraphKernelZeroRestriction_surjective fold twist⟩
  exact equivalence.finrank_eq

theorem circleGraphCokernel_finrank_eq_zeroModes
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleGraphCokernel fold twist) =
      Module.finrank ℂ (CircleZeroMode fold twist → ℂ) := by
  let quotientEquivalence :
      CircleGraphCokernel fold twist ≃ₗ[ℂ]
        (CircleHilbert ⧸ LinearMap.ker (circleZeroRestriction fold twist)) :=
    Submodule.quotEquivOfEq _ _
      (circleGraphDirac_range_eq_zeroRestriction_ker fold twist)
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

/-- Fourier zero-mode coordinates identify the graph kernel exactly. -/
noncomputable def circleGraphKernelZeroModeEquiv
    (fold : Fold) (twist : CircleTwist) :
    LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap ≃ₗ[ℂ]
      (CircleZeroMode fold twist → ℂ) :=
  LinearEquiv.ofBijective
    (circleGraphKernelZeroRestriction fold twist)
    ⟨circleGraphKernelZeroRestriction_injective fold twist,
      circleGraphKernelZeroRestriction_surjective fold twist⟩

/-- Fourier zero-mode coordinates identify the algebraic graph cokernel exactly. -/
noncomputable def circleGraphCokernelZeroModeEquiv
    (fold : Fold) (twist : CircleTwist) :
    CircleGraphCokernel fold twist ≃ₗ[ℂ]
      (CircleZeroMode fold twist → ℂ) := by
  let quotientEquivalence :
      CircleGraphCokernel fold twist ≃ₗ[ℂ]
        (CircleHilbert ⧸ LinearMap.ker (circleZeroRestriction fold twist)) :=
    Submodule.quotEquivOfEq _ _
      (circleGraphDirac_range_eq_zeroRestriction_ker fold twist)
  let rangeEquivalence :=
    (circleZeroRestriction fold twist).quotKerEquivRange
  have hRange : LinearMap.range (circleZeroRestriction fold twist) = ⊤ :=
    LinearMap.range_eq_top.mpr (circleZeroRestriction_surjective fold twist)
  let topEquivalence :
      LinearMap.range (circleZeroRestriction fold twist) ≃ₗ[ℂ]
        (CircleZeroMode fold twist → ℂ) :=
    LinearEquiv.ofTop _ hRange
  exact quotientEquivalence.trans
    (rangeEquivalence.trans topEquivalence)

/-- Pointwise kernel/cokernel identification induced by the same zero Fourier modes. -/
noncomputable def circleGraphCokernelKernelEquiv
    (fold : Fold) (twist : CircleTwist) :
    CircleGraphCokernel fold twist ≃ₗ[ℂ]
      LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap :=
  (circleGraphCokernelZeroModeEquiv fold twist).trans
    (circleGraphKernelZeroModeEquiv fold twist).symm

noncomputable instance circleGraphDiracKernelFree
    (fold : Fold) (twist : CircleTwist) :
    Module.Free ℂ
      (LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap) :=
  Module.Free.of_equiv (circleGraphKernelZeroModeEquiv fold twist).symm

noncomputable instance circleGraphDiracCokernelFree
    (fold : Fold) (twist : CircleTwist) :
    Module.Free ℂ (CircleGraphCokernel fold twist) :=
  Module.Free.of_equiv (circleGraphCokernelZeroModeEquiv fold twist).symm

/-- Algebraic Fredholm index of the bounded graph-norm realization. -/
def circleGraphFredholmIndex (fold : Fold) (twist : CircleTwist) : ℤ :=
  (Module.finrank ℂ
      (LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap) : ℤ) -
    (Module.finrank ℂ (CircleGraphCokernel fold twist) : ℤ)

/-- The actual infinite circle family has Fredholm index zero at every holonomy. -/
theorem circleGraphFredholmIndex_zero
    (fold : Fold) (twist : CircleTwist) :
    circleGraphFredholmIndex fold twist = 0 := by
  rw [circleGraphFredholmIndex,
    circleGraphKernel_finrank_eq_zeroModes,
    circleGraphCokernel_finrank_eq_zeroModes]
  ring

/-- Common top-exterior degree, computed from the finite zero-mode space. -/
abbrev CircleGraphDeterminantDegree (fold : Fold) (twist : CircleTwist) : ℕ :=
  Module.finrank ℂ (CircleZeroMode fold twist → ℂ)

/-- Top exterior power of the graph kernel. -/
abbrev CircleGraphKernelTopExterior (fold : Fold) (twist : CircleTwist) :=
  ⋀[ℂ]^(CircleGraphDeterminantDegree fold twist)
    (LinearMap.ker (circleGraphDiracCLM fold twist).toLinearMap)

/-- Top exterior power of the graph cokernel. -/
abbrev CircleGraphCokernelTopExterior (fold : Fold) (twist : CircleTwist) :=
  ⋀[ℂ]^(CircleGraphDeterminantDegree fold twist)
    (CircleGraphCokernel fold twist)

/-- Pointwise determinant-line fiber `Hom(det coker, det ker)`. -/
abbrev CircleGraphDeterminantLine (fold : Fold) (twist : CircleTwist) :=
  CircleGraphCokernelTopExterior fold twist →ₗ[ℂ]
    CircleGraphKernelTopExterior fold twist

/-- Algebraic determinant section induced by the Fourier zero-mode identification. -/
noncomputable def circleGraphDeterminantSection
    (fold : Fold) (twist : CircleTwist) :
    CircleGraphDeterminantLine fold twist :=
  exteriorPower.map (CircleGraphDeterminantDegree fold twist)
    (circleGraphCokernelKernelEquiv fold twist).toLinearMap

theorem circleGraphKernelTopExterior_finrank_one
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleGraphKernelTopExterior fold twist) = 1 := by
  rw [exteriorPower.finrank_eq,
    circleGraphKernel_finrank_eq_zeroModes, Nat.choose_self]

theorem circleGraphCokernelTopExterior_finrank_one
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleGraphCokernelTopExterior fold twist) = 1 := by
  rw [exteriorPower.finrank_eq,
    circleGraphCokernel_finrank_eq_zeroModes, Nat.choose_self]

/-- The pointwise determinant-line fiber is genuinely one-dimensional. -/
theorem circleGraphDeterminantLine_finrank_one
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleGraphDeterminantLine fold twist) = 1 := by
  rw [Module.finrank_linearMap,
    circleGraphCokernelTopExterior_finrank_one,
    circleGraphKernelTopExterior_finrank_one]

/-- The chosen pointwise determinant section is an isomorphism on top powers. -/
theorem circleGraphDeterminantSection_injective
    (fold : Fold) (twist : CircleTwist) :
    Function.Injective (circleGraphDeterminantSection fold twist) := by
  exact exteriorPower.map_injective_field
    (circleGraphCokernelKernelEquiv fold twist).injective

/-- The Fourier-coordinate determinant section is nonzero at every twist. -/
theorem circleGraphDeterminantSection_ne_zero
    (fold : Fold) (twist : CircleTwist) :
    circleGraphDeterminantSection fold twist ≠ 0 := by
  letI : Nontrivial (CircleGraphCokernelTopExterior fold twist) :=
    Module.nontrivial_of_finrank_eq_succ (R := ℂ)
      (circleGraphCokernelTopExterior_finrank_one fold twist)
  exact LinearMap.ne_zero_of_injective
    (circleGraphDeterminantSection_injective fold twist)

end

end P0EFTJanusCircleGraphFredholmIndex
end JanusFormal
