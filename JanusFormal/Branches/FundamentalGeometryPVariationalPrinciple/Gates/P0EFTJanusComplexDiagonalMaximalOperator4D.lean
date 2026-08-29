import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Generic maximal complex diagonal operator

This gate packages the argument already used by the circle and product-throat
operators for an arbitrary mode type.  A real diagonal weight defines a dense
maximal-domain self-adjoint operator on complex `ℓ²`.  A uniform positive gap
gives a bounded reciprocal, hence bijectivity and Fredholm index zero.
-/

namespace JanusFormal
namespace P0EFTJanusComplexDiagonalMaximalOperator4D

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal lp LinearPMap

variable (Mode : Type*) [DecidableEq Mode]

/-- Complex square-summable coefficient space over an arbitrary mode type. -/
abbrev ComplexDiagonalHilbert :=
  lp (fun _ : Mode => Complex) 2

/-- Reindexing the mode set preserves the complex coefficient Hilbert
space isometrically. -/
def complexDiagonalHilbertCongr
    {Other : Type*} [DecidableEq Other]
    (equiv : Mode ≃ Other) :
    ComplexDiagonalHilbert Mode ≃ₗᵢ[Complex]
      ComplexDiagonalHilbert Other where
  toFun state :=
    ⟨fun mode => state (equiv.symm mode), by
      apply memℓp_gen
      have hSummable :
          Summable
            (fun mode : Mode =>
              ‖state mode‖ ^ (2 : ENNReal).toReal) :=
        (memℓp_gen_iff (by norm_num)).1 state.2
      simpa only [Function.comp_def] using
        equiv.symm.summable_iff.mpr hSummable⟩
  invFun state :=
    ⟨fun mode => state (equiv mode), by
      apply memℓp_gen
      have hSummable :
          Summable
            (fun mode : Other =>
              ‖state mode‖ ^ (2 : ENNReal).toReal) :=
        (memℓp_gen_iff (by norm_num)).1 state.2
      simpa only [Function.comp_def] using
        equiv.summable_iff.mpr hSummable⟩
  left_inv state := by
    ext mode
    simp
  right_inv state := by
    ext mode
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' state := by
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact equiv.symm.tsum_eq
      (fun mode : Mode =>
        ‖state mode‖ ^ (2 : ENNReal).toReal)

@[simp]
theorem complexDiagonalHilbertCongr_apply
    {Other : Type*} [DecidableEq Other]
    (equiv : Mode ≃ Other)
    (state : ComplexDiagonalHilbert Mode)
    (mode : Other) :
    complexDiagonalHilbertCongr Mode equiv state mode =
      state (equiv.symm mode) :=
  rfl

@[simp]
theorem complexDiagonalHilbertCongr_single
    {Other : Type*} [DecidableEq Other]
    (equiv : Mode ≃ Other)
    (mode : Mode) (value : Complex) :
    complexDiagonalHilbertCongr Mode equiv
        (lp.single 2 mode value) =
      lp.single 2 (equiv mode) value := by
  ext coordinate
  by_cases hCoordinate : coordinate = equiv mode
  · subst coordinate
    simp [complexDiagonalHilbertCongr_apply, lp.single_apply]
  · have hSymm : equiv.symm coordinate ≠ mode := by
      intro hEqual
      apply hCoordinate
      rw [← equiv.apply_symm_apply coordinate, hEqual]
    simp [complexDiagonalHilbertCongr_apply, lp.single_apply,
      hCoordinate, hSymm]

/-- Maximal domain of multiplication by a real diagonal weight. -/
def complexDiagonalDomain
    (weight : Mode → Real) :
    Submodule Complex (ComplexDiagonalHilbert Mode) where
  carrier := {state | ∃ image : ComplexDiagonalHilbert Mode, ∀ mode,
    image mode = (weight mode : Complex) * state mode}
  zero_mem' := ⟨0, by intro mode; simp⟩
  add_mem' := by
    rintro first second ⟨firstImage, hFirst⟩ ⟨secondImage, hSecond⟩
    refine ⟨firstImage + secondImage, ?_⟩
    intro mode
    change firstImage mode + secondImage mode =
      (weight mode : Complex) * (first mode + second mode)
    rw [hFirst mode, hSecond mode]
    ring
  smul_mem' := by
    intro scalar state
    rintro ⟨image, hImage⟩
    refine ⟨scalar • image, ?_⟩
    intro mode
    change scalar * image mode =
      (weight mode : Complex) * (scalar * state mode)
    rw [hImage mode]
    ring

/-- The weighted image selected by maximal-domain membership. -/
def complexDiagonalImage
    (weight : Mode → Real)
    (state : complexDiagonalDomain Mode weight) :
    ComplexDiagonalHilbert Mode :=
  state.property.choose

@[simp]
theorem complexDiagonalImage_apply
    (weight : Mode → Real)
    (state : complexDiagonalDomain Mode weight) (mode : Mode) :
    complexDiagonalImage Mode weight state mode =
      (weight mode : Complex) * state.1 mode :=
  state.property.choose_spec mode

/-- Genuine maximal-domain diagonal operator. -/
def complexDiagonalOperator
    (weight : Mode → Real) :
    ComplexDiagonalHilbert Mode →ₗ.[Complex]
      ComplexDiagonalHilbert Mode where
  domain := complexDiagonalDomain Mode weight
  toFun :=
    { toFun := complexDiagonalImage Mode weight
      map_add' := by
        intro first second
        ext mode
        simp [complexDiagonalImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [complexDiagonalImage_apply]
        ring }

@[simp]
theorem complexDiagonalOperator_apply
    (weight : Mode → Real)
    (state : (complexDiagonalOperator Mode weight).domain)
    (mode : Mode) :
    complexDiagonalOperator Mode weight state mode =
      (weight mode : Complex) * state.1 mode :=
  complexDiagonalImage_apply Mode weight state mode

/-- Canonical coordinate Hilbert basis. -/
def complexDiagonalBasis :
    HilbertBasis Mode Complex (ComplexDiagonalHilbert Mode) :=
  HilbertBasis.ofRepr
    (LinearIsometryEquiv.refl Complex (ComplexDiagonalHilbert Mode))

@[simp]
theorem complexDiagonalBasis_eq_single
    (mode : Mode) :
    complexDiagonalBasis Mode mode =
      lp.single 2 mode (1 : Complex) := by
  rw [← HilbertBasis.repr_symm_single (complexDiagonalBasis Mode) mode]
  change (complexDiagonalBasis Mode).repr.symm
    (lp.single 2 mode (1 : Complex)) =
      lp.single 2 mode (1 : Complex)
  rw [show (complexDiagonalBasis Mode).repr =
      LinearIsometryEquiv.refl Complex
        (ComplexDiagonalHilbert Mode) by rfl]
  simpa only [LinearIsometryEquiv.coe_refl, id_eq] using
    (LinearIsometryEquiv.refl Complex
      (ComplexDiagonalHilbert Mode)).symm_apply_apply
        (lp.single 2 mode (1 : Complex))

theorem complexDiagonalBasis_mem_domain
    (weight : Mode → Real) (mode : Mode) :
    complexDiagonalBasis Mode mode ∈
      complexDiagonalDomain Mode weight := by
  refine ⟨(weight mode : Complex) •
    complexDiagonalBasis Mode mode, ?_⟩
  intro other
  change (weight mode : Complex) *
      (complexDiagonalBasis Mode mode other) =
    (weight other : Complex) *
      (complexDiagonalBasis Mode mode other)
  by_cases hOther : other = mode
  · subst other
    rfl
  · rw [complexDiagonalBasis_eq_single, lp.single_apply]
    simp [hOther]

/-- Every maximal real diagonal domain is dense. -/
theorem complexDiagonalDomain_dense
    (weight : Mode → Real) :
    Dense (complexDiagonalDomain Mode weight :
      Set (ComplexDiagonalHilbert Mode)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule Complex (ComplexDiagonalHilbert Mode)) =
        (Submodule.span Complex
          (Set.range (complexDiagonalBasis Mode))).topologicalClosure :=
      (HilbertBasis.dense_span (complexDiagonalBasis Mode)).symm
    _ ≤ (complexDiagonalDomain Mode weight).topologicalClosure :=
      Submodule.topologicalClosure_mono
        (Submodule.span_le.mpr (by
          rintro state ⟨mode, rfl⟩
          exact complexDiagonalBasis_mem_domain Mode weight mode))

theorem complexDiagonalOperator_on_basis
    (weight : Mode → Real) (mode : Mode) :
    complexDiagonalOperator Mode weight
        ⟨complexDiagonalBasis Mode mode,
          complexDiagonalBasis_mem_domain Mode weight mode⟩ =
      (weight mode : Complex) • complexDiagonalBasis Mode mode := by
  ext other
  rw [complexDiagonalOperator_apply]
  change (weight other : Complex) *
      (complexDiagonalBasis Mode mode other) =
    (weight mode : Complex) *
      (complexDiagonalBasis Mode mode other)
  by_cases hOther : other = mode
  · subst other
    rfl
  · rw [complexDiagonalBasis_eq_single, lp.single_apply]
    simp [hOther]

theorem complexDiagonalBasis_inner_left
    (mode : Mode) (state : ComplexDiagonalHilbert Mode) :
    inner Complex (complexDiagonalBasis Mode mode) state =
      state mode := by
  rw [complexDiagonalBasis_eq_single, lp.inner_single_left]
  simp

theorem complexDiagonalOperator_isFormalAdjoint_self
    (weight : Mode → Real) :
    (complexDiagonalOperator Mode weight).IsFormalAdjoint
      (complexDiagonalOperator Mode weight) := by
  intro first second
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  simp
  ring

/-- Maximality of the real weighted domain gives self-adjointness. -/
theorem complexDiagonalOperator_isSelfAdjoint
    (weight : Mode → Real) :
    IsSelfAdjoint (complexDiagonalOperator Mode weight) := by
  let operator := complexDiagonalOperator Mode weight
  have hDense :
      Dense (operator.domain : Set (ComplexDiagonalHilbert Mode)) :=
    complexDiagonalDomain_dense Mode weight
  have hSymmetric : operator.IsFormalAdjoint operator :=
    complexDiagonalOperator_isFormalAdjoint_self Mode weight
  have hOperatorLeAdjoint : operator ≤ operator.adjoint :=
    hSymmetric.le_adjoint hDense
  have hAdjointDomain : operator.adjoint.domain ≤ operator.domain := by
    intro state hState
    let adjointState : operator.adjoint.domain := ⟨state, hState⟩
    let image : ComplexDiagonalHilbert Mode :=
      operator.adjoint adjointState
    refine ⟨image, ?_⟩
    intro mode
    let basisState : operator.domain :=
      ⟨complexDiagonalBasis Mode mode,
        complexDiagonalBasis_mem_domain Mode weight mode⟩
    have hInner := (LinearPMap.adjoint_isFormalAdjoint hDense).symm
      basisState adjointState
    change inner Complex (operator basisState)
        (adjointState : ComplexDiagonalHilbert Mode) =
      inner Complex
        (basisState : ComplexDiagonalHilbert Mode) image at hInner
    rw [show operator basisState =
        (weight mode : Complex) • complexDiagonalBasis Mode mode by
      exact complexDiagonalOperator_on_basis Mode weight mode,
      inner_smul_left,
      complexDiagonalBasis_inner_left,
      complexDiagonalBasis_inner_left] at hInner
    simpa using hInner.symm
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt
    (le_antisymm hAdjointDomain hOperatorLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hOperatorLeAdjoint.2 hState.symm).symm

theorem complexDiagonalOperator_isClosed
    (weight : Mode → Real) :
    (complexDiagonalOperator Mode weight).IsClosed :=
  (complexDiagonalOperator_isSelfAdjoint Mode weight).isClosed

/-- Reciprocal coefficient of a nonzero real diagonal weight. -/
def complexDiagonalInverseCoefficient
    (weight : Mode → Real) (mode : Mode) : Complex :=
  (weight mode : Complex)⁻¹

theorem complexDiagonalWeight_ne_zero_of_gap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (mode : Mode) :
    weight mode ≠ 0 := by
  intro hZero
  have := hGap mode
  rw [hZero, abs_zero] at this
  exact (not_lt_of_ge this) hGapPositive

theorem complexDiagonalInverseCoefficient_norm_le
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (mode : Mode) :
    ‖complexDiagonalInverseCoefficient Mode weight mode‖ ≤ gap⁻¹ := by
  rw [complexDiagonalInverseCoefficient, norm_inv,
    Complex.norm_real, Real.norm_eq_abs]
  exact inv_anti₀ hGapPositive (hGap mode)

/-- Bounded reciprocal multiplier supplied by a uniform spectral gap. -/
def complexDiagonalInverseImage
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : ComplexDiagonalHilbert Mode) :
    ComplexDiagonalHilbert Mode := by
  let inverse : Mode → Complex := fun mode =>
    complexDiagonalInverseCoefficient Mode weight mode * state mode
  have hBound : Memℓp
      (fun mode : Mode => (gap⁻¹ : Complex) * state mode) 2 :=
    (lp.memℓp state).const_mul (gap⁻¹ : Complex)
  have hInverse : Memℓp inverse 2 :=
    hBound.mono' (fun mode => by
      rw [show inverse mode =
          complexDiagonalInverseCoefficient Mode weight mode *
            state mode by rfl,
        norm_mul, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hGapPositive.le]
      exact mul_le_mul_of_nonneg_right
        (complexDiagonalInverseCoefficient_norm_le
          Mode weight gap hGapPositive hGap mode)
        (norm_nonneg _))
  exact ⟨inverse, hInverse⟩

@[simp]
theorem complexDiagonalInverseImage_apply
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : ComplexDiagonalHilbert Mode) (mode : Mode) :
    complexDiagonalInverseImage Mode weight gap hGapPositive hGap
        state mode =
      complexDiagonalInverseCoefficient Mode weight mode * state mode :=
  rfl

/-- Complex-linear reciprocal multiplier on the ambient Hilbert space. -/
def complexDiagonalInverseLinearMap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    ComplexDiagonalHilbert Mode →ₗ[Complex]
      ComplexDiagonalHilbert Mode where
  toFun :=
    complexDiagonalInverseImage
      Mode weight gap hGapPositive hGap
  map_add' first second := by
    ext mode
    simp [complexDiagonalInverseImage_apply, mul_add]
  map_smul' scalar state := by
    ext mode
    simp [complexDiagonalInverseImage_apply]
    ring

/-- Bounded inverse multiplier, with norm controlled by the reciprocal
spectral gap. -/
def complexDiagonalInverseCLM
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    ComplexDiagonalHilbert Mode →L[Complex]
      ComplexDiagonalHilbert Mode :=
  (complexDiagonalInverseLinearMap
      Mode weight gap hGapPositive hGap).mkContinuous
    gap⁻¹ (by
      intro state
      rw [← show
        ‖(gap⁻¹ : Complex) • state‖ = gap⁻¹ * ‖state‖ by
          rw [norm_smul, norm_inv, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hGapPositive]]
      apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
      intro mode
      change
        ‖complexDiagonalInverseCoefficient Mode weight mode *
            state mode‖ ≤
          ‖(gap⁻¹ : Complex) • state mode‖
      rw [norm_mul, norm_smul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hGapPositive]
      exact mul_le_mul_of_nonneg_right
        (complexDiagonalInverseCoefficient_norm_le
          Mode weight gap hGapPositive hGap mode)
        (norm_nonneg (state mode)))

@[simp]
theorem complexDiagonalInverseCLM_apply
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalInverseCLM
        Mode weight gap hGapPositive hGap state =
      complexDiagonalInverseImage
        Mode weight gap hGapPositive hGap state :=
  rfl

theorem complexDiagonalInverseImage_mem_domain
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalInverseImage Mode weight gap hGapPositive hGap state ∈
      complexDiagonalDomain Mode weight := by
  refine ⟨state, fun mode => ?_⟩
  rw [complexDiagonalInverseImage_apply,
    complexDiagonalInverseCoefficient]
  have hWeight : (weight mode : Complex) ≠ 0 := by
    exact_mod_cast complexDiagonalWeight_ne_zero_of_gap
      Mode weight gap hGapPositive hGap mode
  field_simp

def complexDiagonalInverse
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : ComplexDiagonalHilbert Mode) :
    (complexDiagonalOperator Mode weight).domain :=
  ⟨complexDiagonalInverseImage Mode weight gap hGapPositive hGap state,
    complexDiagonalInverseImage_mem_domain
      Mode weight gap hGapPositive hGap state⟩

theorem complexDiagonalOperator_rightInverse
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : ComplexDiagonalHilbert Mode) :
    complexDiagonalOperator Mode weight
        (complexDiagonalInverse
          Mode weight gap hGapPositive hGap state) = state := by
  ext mode
  rw [complexDiagonalOperator_apply]
  change (weight mode : Complex) *
      complexDiagonalInverseImage
        Mode weight gap hGapPositive hGap state mode = state mode
  rw [
    complexDiagonalInverseImage_apply,
    complexDiagonalInverseCoefficient]
  have hWeight : (weight mode : Complex) ≠ 0 := by
    exact_mod_cast complexDiagonalWeight_ne_zero_of_gap
      Mode weight gap hGapPositive hGap mode
  field_simp

theorem complexDiagonalOperator_leftInverse
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : (complexDiagonalOperator Mode weight).domain) :
    complexDiagonalInverse Mode weight gap hGapPositive hGap
        (complexDiagonalOperator Mode weight state) = state := by
  apply Subtype.ext
  ext mode
  change complexDiagonalInverseImage Mode weight gap hGapPositive hGap
      (complexDiagonalOperator Mode weight state) mode = state.1 mode
  rw [complexDiagonalInverseImage_apply,
    complexDiagonalOperator_apply,
    complexDiagonalInverseCoefficient]
  have hWeight : (weight mode : Complex) ≠ 0 := by
    exact_mod_cast complexDiagonalWeight_ne_zero_of_gap
      Mode weight gap hGapPositive hGap mode
  field_simp

@[simp]
theorem complexDiagonalInverseCLM_operator
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : (complexDiagonalOperator Mode weight).domain) :
    complexDiagonalInverseCLM
        Mode weight gap hGapPositive hGap
        (complexDiagonalOperator Mode weight state) =
      state.1 := by
  exact congrArg Subtype.val
    (complexDiagonalOperator_leftInverse
      Mode weight gap hGapPositive hGap state)

theorem complexDiagonalInverseCLM_norm_le
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    ‖complexDiagonalInverseCLM
        Mode weight gap hGapPositive hGap‖ ≤ gap⁻¹ := by
  apply LinearMap.mkContinuous_norm_le
  exact (inv_pos.mpr hGapPositive).le

/-- Quantitative coercivity of every real diagonal maximal operator with a
positive spectral gap. -/
theorem complexDiagonalOperator_coercive
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|)
    (state : (complexDiagonalOperator Mode weight).domain) :
    ‖state.1‖ ≤ gap⁻¹ *
      ‖complexDiagonalOperator Mode weight state‖ := by
  rw [← complexDiagonalInverseCLM_operator
    Mode weight gap hGapPositive hGap state]
  exact
    (complexDiagonalInverseCLM
      Mode weight gap hGapPositive hGap).le_of_opNorm_le
        (complexDiagonalInverseCLM_norm_le
          Mode weight gap hGapPositive hGap)
        (complexDiagonalOperator Mode weight state)

theorem complexDiagonalOperator_injective_of_gap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    Function.Injective (complexDiagonalOperator Mode weight) := by
  intro first second hEqual
  rw [← complexDiagonalOperator_leftInverse
      Mode weight gap hGapPositive hGap first,
    ← complexDiagonalOperator_leftInverse
      Mode weight gap hGapPositive hGap second,
    hEqual]

theorem complexDiagonalOperator_surjective_of_gap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    Function.Surjective (complexDiagonalOperator Mode weight) :=
  fun state =>
    ⟨complexDiagonalInverse Mode weight gap hGapPositive hGap state,
      complexDiagonalOperator_rightInverse
        Mode weight gap hGapPositive hGap state⟩

theorem complexDiagonalOperator_ker_eq_bot_of_gap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    LinearMap.ker (complexDiagonalOperator Mode weight).toFun = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (complexDiagonalOperator_injective_of_gap
      Mode weight gap hGapPositive hGap)

theorem complexDiagonalOperator_range_eq_top_of_gap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    LinearMap.range (complexDiagonalOperator Mode weight).toFun = ⊤ :=
  LinearMap.range_eq_top.mpr
    (complexDiagonalOperator_surjective_of_gap
      Mode weight gap hGapPositive hGap)

abbrev ComplexDiagonalCokernel
    (weight : Mode → Real) :=
  ComplexDiagonalHilbert Mode ⧸
    LinearMap.range (complexDiagonalOperator Mode weight).toFun

theorem complexDiagonalOperator_fredholm_of_gap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    IsClosed
        (LinearMap.range (complexDiagonalOperator Mode weight).toFun :
          Set (ComplexDiagonalHilbert Mode)) ∧
      FiniteDimensional Complex
        (LinearMap.ker (complexDiagonalOperator Mode weight).toFun) ∧
      FiniteDimensional Complex
        (ComplexDiagonalCokernel Mode weight) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [complexDiagonalOperator_range_eq_top_of_gap
      Mode weight gap hGapPositive hGap]
    exact isClosed_univ
  · rw [complexDiagonalOperator_ker_eq_bot_of_gap
      Mode weight gap hGapPositive hGap]
    infer_instance
  · change FiniteDimensional Complex
      (ComplexDiagonalHilbert Mode ⧸
        LinearMap.range (complexDiagonalOperator Mode weight).toFun)
    rw [complexDiagonalOperator_range_eq_top_of_gap
      Mode weight gap hGapPositive hGap]
    infer_instance

def complexDiagonalOperatorIndex
    (weight : Mode → Real) : Int :=
  (complexDiagonalOperator Mode weight).toFun.index

theorem complexDiagonalOperatorIndex_zero_of_gap
    (weight : Mode → Real) (gap : Real)
    (hGapPositive : 0 < gap)
    (hGap : ∀ mode, gap ≤ |weight mode|) :
    complexDiagonalOperatorIndex Mode weight = 0 := by
  unfold complexDiagonalOperatorIndex
  rw [LinearMap.index_of_surjective
      (complexDiagonalOperator_surjective_of_gap
        Mode weight gap hGapPositive hGap),
    complexDiagonalOperator_ker_eq_bot_of_gap
      Mode weight gap hGapPositive hGap]
  simp

end
end P0EFTJanusComplexDiagonalMaximalOperator4D
end JanusFormal
