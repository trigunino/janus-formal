import Mathlib.Analysis.InnerProductSpace.l2Space
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusGlobalSeparatedDiracModel

namespace JanusFormal
namespace P0EFTJanusInfiniteL2DiracDomain

set_option autoImplicit false

open scoped ENNReal lp
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions

noncomputable section

/-- The completed real Hilbert space of square-summable separated modes. -/
abbrev ProductModeHilbert := lp (fun _ : ProductDiracMode => ℝ) 2

example : CompleteSpace ProductModeHilbert := inferInstance
example : InnerProductSpace ℝ ProductModeHilbert := inferInstance

/-- Maximal weighted domain of a real diagonal mode operator. -/
def weightedDiracDomain (weight : ProductDiracMode → ℝ) :
    Submodule ℝ ProductModeHilbert where
  carrier := {ψ | Memℓp (fun mode => weight mode * ψ mode) 2}
  zero_mem' := by
    change Memℓp (fun mode => weight mode * (0 : ProductModeHilbert) mode) 2
    convert (zero_memℓp : Memℓp (0 : ProductDiracMode → ℝ) 2) using 1
    ext mode
    simp
  add_mem' := by
    intro ψ φ hψ hφ
    change Memℓp (fun mode => weight mode * (ψ + φ) mode) 2
    convert hψ.add hφ using 1
    ext mode
    simp [mul_add]
  smul_mem' := by
    intro c ψ hψ
    change Memℓp (fun mode => weight mode * (c • ψ) mode) 2
    convert hψ.const_smul c using 1
    ext mode
    simp [mul_left_comm]

/-- The unbounded diagonal Dirac operator, defined on its maximal weighted domain. -/
noncomputable def diagonalL2Dirac (weight : ProductDiracMode → ℝ)
    (ψ : weightedDiracDomain weight) : ProductModeHilbert :=
  ⟨fun mode => weight mode * ψ.1 mode, ψ.2⟩

@[simp] theorem diagonal_l2_dirac_apply (weight : ProductDiracMode → ℝ)
    (ψ : weightedDiracDomain weight) (mode : ProductDiracMode) :
    diagonalL2Dirac weight ψ mode = weight mode * ψ.1 mode := rfl

/-- Linear realization of the diagonal operator on its weighted domain. -/
noncomputable def diagonalL2DiracLinearMap (weight : ProductDiracMode → ℝ) :
    weightedDiracDomain weight →ₗ[ℝ] ProductModeHilbert where
  toFun := diagonalL2Dirac weight
  map_add' := by
    intro ψ φ
    ext mode
    simp [diagonalL2Dirac, mul_add]
  map_smul' := by
    intro c ψ
    ext mode
    simp [diagonalL2Dirac, mul_left_comm]

/-- A real diagonal weight makes the maximal-domain operator formally symmetric. -/
theorem diagonal_l2_dirac_formally_symmetric (weight : ProductDiracMode → ℝ)
    (ψ φ : weightedDiracDomain weight) :
    inner ℝ (diagonalL2Dirac weight ψ) φ.1 =
      inner ℝ ψ.1 (diagonalL2Dirac weight φ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext mode
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- Every coordinate mode lies in the maximal domain, hence finite mode sums form a core candidate. -/
theorem single_mem_weighted_domain (weight : ProductDiracMode → ℝ)
    (mode : ProductDiracMode) (coefficient : ℝ) :
    (lp.single 2 mode coefficient : ProductModeHilbert) ∈ weightedDiracDomain weight := by
  refine (memℓp_zero ?_).of_exponent_ge zero_le
  refine (Set.finite_singleton mode).subset ?_
  intro other hOther
  by_contra hNe
  have hOtherMode : other ≠ mode := by simpa using hNe
  have : (lp.single 2 mode coefficient : ProductModeHilbert) other = 0 := by
    exact lp.single_apply_ne (E := fun _ : ProductDiracMode => ℝ)
      2 mode coefficient hOtherMode
  exact hOther (by rw [this, mul_zero])

/-- Algebraic span of the canonical coordinate modes. -/
def finiteModeSpan : Submodule ℝ ProductModeHilbert :=
  Submodule.span ℝ (Set.range fun mode : ProductDiracMode =>
    (lp.single 2 mode 1 : ProductModeHilbert))

theorem single_mem_finite_mode_span (mode : ProductDiracMode) (coefficient : ℝ) :
    (lp.single 2 mode coefficient : ProductModeHilbert) ∈ finiteModeSpan := by
  have hUnit : (lp.single 2 mode 1 : ProductModeHilbert) ∈ finiteModeSpan :=
    Submodule.subset_span (Set.mem_range_self mode)
  convert finiteModeSpan.smul_mem coefficient hUnit using 1
  ext other
  by_cases h : other = mode
  · subst other
    simp
  · simp [h]

/-- Finite mode combinations are contained in every diagonal weighted domain. -/
theorem finite_mode_span_le_weighted_domain (weight : ProductDiracMode → ℝ) :
    finiteModeSpan ≤ weightedDiracDomain weight := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨mode, rfl⟩
  exact single_mem_weighted_domain weight mode 1

/-- Coordinate-mode combinations are dense in the completed separated-mode Hilbert space. -/
theorem finite_mode_span_dense : Dense (finiteModeSpan : Set ProductModeHilbert) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro ψ _
  have hSum : HasSum
      (fun mode : ProductDiracMode =>
        (lp.single 2 mode (ψ mode) : ProductModeHilbert)) ψ :=
    lp.hasSum_single ENNReal.ofNat_ne_top ψ
  apply finiteModeSpan.isClosed_topologicalClosure.mem_of_tendsto hSum
  filter_upwards [] with modes
  apply finiteModeSpan.le_topologicalClosure
  exact finiteModeSpan.sum_mem fun mode _ => single_mem_finite_mode_span mode (ψ mode)

/-- The maximal diagonal domain is densely defined because it contains the finite-mode span. -/
theorem weighted_dirac_domain_dense (weight : ProductDiracMode → ℝ) :
    Dense (weightedDiracDomain weight : Set ProductModeHilbert) :=
  finite_mode_span_dense.mono (finite_mode_span_le_weighted_domain weight)

/-- Coordinate description of the graph of the maximal diagonal operator. -/
def diagonalL2Graph (weight : ProductDiracMode → ℝ) :
    Set (ProductModeHilbert × ProductModeHilbert) :=
  {pair | ∀ mode, pair.2 mode = weight mode * pair.1 mode}

theorem diagonal_l2_graph_iff (weight : ProductDiracMode → ℝ)
    (pair : ProductModeHilbert × ProductModeHilbert) :
    pair ∈ diagonalL2Graph weight ↔
      ∃ ψ : weightedDiracDomain weight,
        ψ.1 = pair.1 ∧ diagonalL2Dirac weight ψ = pair.2 := by
  constructor
  · intro hPair
    have hWeighted : Memℓp (fun mode => weight mode * pair.1 mode) 2 := by
      rw [show (fun mode => weight mode * pair.1 mode) =
          (fun mode => pair.2 mode) by
        funext mode
        exact (hPair mode).symm]
      exact pair.2.2
    let ψ : weightedDiracDomain weight := ⟨pair.1, hWeighted⟩
    refine ⟨ψ, rfl, ?_⟩
    ext mode
    exact (hPair mode).symm
  · rintro ⟨ψ, hψ, hD⟩ mode
    rw [← hD]
    simp [hψ]

/-- The maximal real diagonal operator has a closed graph. -/
theorem diagonal_l2_graph_closed (weight : ProductDiracMode → ℝ) :
    IsClosed (diagonalL2Graph weight) := by
  rw [show diagonalL2Graph weight = ⋂ mode : ProductDiracMode,
      {pair | pair.2 mode = weight mode * pair.1 mode} by
    ext pair
    simp [diagonalL2Graph]]
  apply isClosed_iInter
  intro mode
  exact isClosed_eq
    ((lp.evalCLM ℝ (fun _ : ProductDiracMode => ℝ) 2 mode).continuous.comp continuous_snd)
    (continuous_const.mul
      ((lp.evalCLM ℝ (fun _ : ProductDiracMode => ℝ) 2 mode).continuous.comp continuous_fst))

/-- Complexification used for the non-real resolvent criterion. -/
abbrev ComplexProductModeHilbert := lp (fun _ : ProductDiracMode => ℂ) 2

def complexWeightedDiracDomain (weight : ProductDiracMode → ℝ) :
    Submodule ℂ ComplexProductModeHilbert where
  carrier := {ψ | Memℓp (fun mode => (weight mode : ℂ) * ψ mode) 2}
  zero_mem' := by
    change Memℓp (fun mode => (weight mode : ℂ) * (0 : ComplexProductModeHilbert) mode) 2
    convert (zero_memℓp : Memℓp (0 : ProductDiracMode → ℂ) 2) using 1
    ext mode
    simp
  add_mem' := by
    intro ψ φ hψ hφ
    change Memℓp (fun mode => (weight mode : ℂ) * (ψ + φ) mode) 2
    convert hψ.add hφ using 1
    ext mode
    simp [mul_add]
  smul_mem' := by
    intro c ψ hψ
    change Memℓp (fun mode => (weight mode : ℂ) * (c • ψ) mode) 2
    convert hψ.const_smul c using 1
    ext mode
    simp [mul_left_comm]

noncomputable def complexDiagonalL2Dirac (weight : ProductDiracMode → ℝ)
    (ψ : complexWeightedDiracDomain weight) : ComplexProductModeHilbert :=
  ⟨fun mode => (weight mode : ℂ) * ψ.1 mode, ψ.2⟩

def complexFiniteModeSpan : Submodule ℂ ComplexProductModeHilbert :=
  Submodule.span ℂ (Set.range fun mode : ProductDiracMode =>
    (lp.single 2 mode 1 : ComplexProductModeHilbert))

theorem complex_single_mem_weighted_domain (weight : ProductDiracMode → ℝ)
    (mode : ProductDiracMode) (coefficient : ℂ) :
    (lp.single 2 mode coefficient : ComplexProductModeHilbert) ∈
      complexWeightedDiracDomain weight := by
  refine (memℓp_zero ?_).of_exponent_ge zero_le
  refine (Set.finite_singleton mode).subset ?_
  intro other hOther
  by_contra hNe
  have hOtherMode : other ≠ mode := by simpa using hNe
  have : (lp.single 2 mode coefficient : ComplexProductModeHilbert) other = 0 :=
    lp.single_apply_ne (E := fun _ : ProductDiracMode => ℂ) 2 mode coefficient hOtherMode
  exact hOther (by rw [this, mul_zero])

theorem complex_finite_mode_span_dense :
    Dense (complexFiniteModeSpan : Set ComplexProductModeHilbert) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  intro ψ _
  have hSum : HasSum
      (fun mode : ProductDiracMode =>
        (lp.single 2 mode (ψ mode) : ComplexProductModeHilbert)) ψ :=
    lp.hasSum_single ENNReal.ofNat_ne_top ψ
  apply complexFiniteModeSpan.isClosed_topologicalClosure.mem_of_tendsto hSum
  filter_upwards [] with modes
  apply complexFiniteModeSpan.le_topologicalClosure
  apply complexFiniteModeSpan.sum_mem
  intro mode _
  have hUnit : (lp.single 2 mode 1 : ComplexProductModeHilbert) ∈ complexFiniteModeSpan :=
    Submodule.subset_span (Set.mem_range_self mode)
  convert complexFiniteModeSpan.smul_mem (ψ mode) hUnit using 1
  ext other
  by_cases h : other = mode <;> simp [h]

theorem complex_weighted_dirac_domain_dense (weight : ProductDiracMode → ℝ) :
    Dense (complexWeightedDiracDomain weight : Set ComplexProductModeHilbert) := by
  apply complex_finite_mode_span_dense.mono
  exact Submodule.span_le.2 fun _ h => by
    rcases h with ⟨mode, rfl⟩
    exact complex_single_mem_weighted_domain weight mode 1

theorem complex_diagonal_l2_formally_symmetric (weight : ProductDiracMode → ℝ)
    (ψ φ : complexWeightedDiracDomain weight) :
    inner ℂ (complexDiagonalL2Dirac weight ψ) φ.1 =
      inner ℂ ψ.1 (complexDiagonalL2Dirac weight φ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext mode
  simp [complexDiagonalL2Dirac, mul_left_comm, mul_assoc]

theorem one_le_norm_real_sub_I (x : ℝ) :
    1 ≤ ‖(x : ℂ) - Complex.I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) - Complex.I)

theorem norm_real_le_norm_real_sub_I (x : ℝ) :
    ‖(x : ℂ)‖ ≤ ‖(x : ℂ) - Complex.I‖ := by
  simpa using Complex.abs_re_le_norm ((x : ℂ) - Complex.I)

/-- Explicit candidate for `(D-i)⁻¹`; its pointwise multiplier has norm at most one. -/
noncomputable def complexShiftIInverse (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) : ComplexProductModeHilbert :=
  ⟨fun mode => φ mode / ((weight mode : ℂ) - Complex.I), by
    refine φ.2.mono' ?_
    intro mode
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (one_le_norm_real_sub_I (weight mode))⟩

theorem real_sub_I_ne_zero (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
  intro h
  have := one_le_norm_real_sub_I x
  rw [h, norm_zero] at this
  norm_num at this

theorem complex_shift_I_inverse_mem_domain (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) :
    complexShiftIInverse weight φ ∈ complexWeightedDiracDomain weight := by
  refine φ.2.mono' ?_
  intro mode
  change ‖(weight mode : ℂ) *
      (φ mode / ((weight mode : ℂ) - Complex.I))‖ ≤ ‖φ mode‖
  rw [norm_mul, norm_div]
  have hDenPos : 0 < ‖(weight mode : ℂ) - Complex.I‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_real_sub_I (weight mode))
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hDenPos).2
  calc
    ‖(weight mode : ℂ)‖ * ‖φ mode‖ ≤
        ‖(weight mode : ℂ) - Complex.I‖ * ‖φ mode‖ :=
      mul_le_mul_of_nonneg_right (norm_real_le_norm_real_sub_I (weight mode)) (norm_nonneg _)
    _ = ‖φ mode‖ * ‖(weight mode : ℂ) - Complex.I‖ := mul_comm _ _

noncomputable def complexShiftIInverseDomain (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) : complexWeightedDiracDomain weight :=
  ⟨complexShiftIInverse weight φ, complex_shift_I_inverse_mem_domain weight φ⟩

theorem complex_shift_I_inverse_norm_le (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) :
    ‖complexShiftIInverse weight φ‖ ≤ ‖φ‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  change ‖φ mode / ((weight mode : ℂ) - Complex.I)‖ ≤ ‖φ mode‖
  rw [norm_div]
  exact div_le_self (norm_nonneg _) (one_le_norm_real_sub_I (weight mode))

theorem real_diagonal_shift_I_cancel (x : ℝ) (a : ℂ) :
    (x : ℂ) * (a / ((x : ℂ) - Complex.I)) -
        Complex.I * (a / ((x : ℂ) - Complex.I)) = a := by
  calc
    _ = ((x : ℂ) - Complex.I) * (a / ((x : ℂ) - Complex.I)) := by ring
    _ = a := mul_div_cancel₀ a (real_sub_I_ne_zero x)

theorem real_diagonal_shift_I_div_cancel (x : ℝ) (a : ℂ) :
    ((x : ℂ) * a - Complex.I * a) / ((x : ℂ) - Complex.I) = a := by
  calc
    _ = (((x : ℂ) - Complex.I) * a) / ((x : ℂ) - Complex.I) := by ring
    _ = a := mul_div_cancel_left₀ a (real_sub_I_ne_zero x)

/-- The non-real shift `D-i` is surjective, with its inverse given mode by mode. -/
theorem complex_shift_I_surjective (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) :
    complexDiagonalL2Dirac weight (complexShiftIInverseDomain weight φ) -
        Complex.I • (complexShiftIInverseDomain weight φ).1 = φ := by
  ext mode
  simp only [complexDiagonalL2Dirac, complexShiftIInverseDomain,
    complexShiftIInverse, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
    ComplexProductModeHilbert]
  exact real_diagonal_shift_I_cancel (weight mode) (φ mode)

/-- The explicit resolvent is also a left inverse of `D-i`. -/
theorem complex_shift_I_inverse_left (weight : ProductDiracMode → ℝ)
    (ψ : complexWeightedDiracDomain weight) :
    complexShiftIInverse weight
      (complexDiagonalL2Dirac weight ψ - Complex.I • ψ.1) = ψ.1 := by
  ext mode
  change (((weight mode : ℂ) * ψ.1 mode - Complex.I * ψ.1 mode) /
      ((weight mode : ℂ) - Complex.I)) = ψ.1 mode
  exact real_diagonal_shift_I_div_cancel (weight mode) (ψ.1 mode)

theorem one_le_norm_real_add_I (x : ℝ) :
    1 ≤ ‖(x : ℂ) + Complex.I‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ) + Complex.I)

theorem norm_real_le_norm_real_add_I (x : ℝ) :
    ‖(x : ℂ)‖ ≤ ‖(x : ℂ) + Complex.I‖ := by
  simpa using Complex.abs_re_le_norm ((x : ℂ) + Complex.I)

theorem real_add_I_ne_zero (x : ℝ) : (x : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := one_le_norm_real_add_I x
  rw [h, norm_zero] at this
  norm_num at this

/-- Explicit candidate for `(D+i)⁻¹`. -/
noncomputable def complexShiftNegIInverse (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) : ComplexProductModeHilbert :=
  ⟨fun mode => φ mode / ((weight mode : ℂ) + Complex.I), by
    refine φ.2.mono' ?_
    intro mode
    change ‖φ mode / ((weight mode : ℂ) + Complex.I)‖ ≤ ‖φ mode‖
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (one_le_norm_real_add_I (weight mode))⟩

theorem complex_shift_neg_I_inverse_mem_domain (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) :
    complexShiftNegIInverse weight φ ∈ complexWeightedDiracDomain weight := by
  refine φ.2.mono' ?_
  intro mode
  change ‖(weight mode : ℂ) *
      (φ mode / ((weight mode : ℂ) + Complex.I))‖ ≤ ‖φ mode‖
  rw [norm_mul, norm_div, ← mul_div_assoc]
  have hDenPos : 0 < ‖(weight mode : ℂ) + Complex.I‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_real_add_I (weight mode))
  apply (div_le_iff₀ hDenPos).2
  calc
    ‖(weight mode : ℂ)‖ * ‖φ mode‖ ≤
        ‖(weight mode : ℂ) + Complex.I‖ * ‖φ mode‖ :=
      mul_le_mul_of_nonneg_right (norm_real_le_norm_real_add_I (weight mode)) (norm_nonneg _)
    _ = ‖φ mode‖ * ‖(weight mode : ℂ) + Complex.I‖ := mul_comm _ _

noncomputable def complexShiftNegIInverseDomain (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) : complexWeightedDiracDomain weight :=
  ⟨complexShiftNegIInverse weight φ, complex_shift_neg_I_inverse_mem_domain weight φ⟩

theorem real_diagonal_shift_neg_I_cancel (x : ℝ) (a : ℂ) :
    (x : ℂ) * (a / ((x : ℂ) + Complex.I)) +
        Complex.I * (a / ((x : ℂ) + Complex.I)) = a := by
  calc
    _ = ((x : ℂ) + Complex.I) * (a / ((x : ℂ) + Complex.I)) := by ring
    _ = a := mul_div_cancel₀ a (real_add_I_ne_zero x)

/-- The conjugate non-real shift `D+i` is also surjective. -/
theorem complex_shift_neg_I_surjective (weight : ProductDiracMode → ℝ)
    (φ : ComplexProductModeHilbert) :
    complexDiagonalL2Dirac weight (complexShiftNegIInverseDomain weight φ) +
        Complex.I • (complexShiftNegIInverseDomain weight φ).1 = φ := by
  ext mode
  change (weight mode : ℂ) * (φ mode / ((weight mode : ℂ) + Complex.I)) +
      Complex.I * (φ mode / ((weight mode : ℂ) + Complex.I)) = φ mode
  exact real_diagonal_shift_neg_I_cancel (weight mode) (φ mode)

/-- Concrete von Neumann resolvent certificate for the maximal diagonal operator. -/
structure DiagonalSelfAdjointResolventCertificate (weight : ProductDiracMode → ℝ) : Prop where
  domainDense : Dense (complexWeightedDiracDomain weight : Set ComplexProductModeHilbert)
  formallySymmetric : ∀ ψ φ : complexWeightedDiracDomain weight,
    inner ℂ (complexDiagonalL2Dirac weight ψ) φ.1 =
      inner ℂ ψ.1 (complexDiagonalL2Dirac weight φ)
  shiftMinusISurjective : ∀ φ : ComplexProductModeHilbert,
    ∃ ψ : complexWeightedDiracDomain weight,
      complexDiagonalL2Dirac weight ψ - Complex.I • ψ.1 = φ
  shiftPlusISurjective : ∀ φ : ComplexProductModeHilbert,
    ∃ ψ : complexWeightedDiracDomain weight,
      complexDiagonalL2Dirac weight ψ + Complex.I • ψ.1 = φ

theorem diagonal_self_adjoint_resolvent_certificate (weight : ProductDiracMode → ℝ) :
    DiagonalSelfAdjointResolventCertificate weight where
  domainDense := complex_weighted_dirac_domain_dense weight
  formallySymmetric := complex_diagonal_l2_formally_symmetric weight
  shiftMinusISurjective := fun φ =>
    ⟨complexShiftIInverseDomain weight φ, complex_shift_I_surjective weight φ⟩
  shiftPlusISurjective := fun φ =>
    ⟨complexShiftNegIInverseDomain weight φ, complex_shift_neg_I_surjective weight φ⟩

/-- Properness of a diagonal weight: bounded spectral windows contain finitely many modes. -/
def ProperDiagonalWeight (weight : ProductDiracMode → ℝ) : Prop :=
  ∀ R : ℝ, Set.Finite {mode | ‖(weight mode : ℂ)‖ ≤ R}

def productModeBoundingBox (N : ℕ) : Set ProductDiracMode :=
  {mode | mode.sphereLevel ≤ N ∧
    -(N : ℤ) ≤ mode.circleMode ∧ mode.circleMode ≤ (N : ℤ)}

/-- A bounded box contains only finitely many separated product modes. -/
theorem product_mode_bounding_box_finite (N : ℕ) :
    Set.Finite (productModeBoundingBox N) := by
  let encode : ProductDiracMode → ℕ × (ℤ × NormalRootChoice) :=
    fun mode => (mode.sphereLevel, mode.circleMode, mode.rootChoice)
  apply Set.Finite.of_finite_image (f := encode)
  · refine ((Set.finite_Iic N).prod
      ((Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod
        (Set.finite_univ : Set.Finite (Set.univ : Set NormalRootChoice)))).subset ?_
    rintro coordinates ⟨mode, hMode, rfl⟩
    exact ⟨hMode.1, ⟨⟨hMode.2.1, hMode.2.2⟩, Set.mem_univ _⟩⟩
  · apply Function.Injective.injOn
    intro first second hEncoded
    cases first
    cases second
    simp only [encode, Prod.mk.injEq] at hEncoded
    simp_all

/-- Quantitative coercivity: every bounded spectral window lies in a finite mode box. -/
def CoerciveDiagonalWeight (weight : ProductDiracMode → ℝ) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ,
    {mode | ‖(weight mode : ℂ)‖ ≤ R} ⊆ productModeBoundingBox N

theorem proper_diagonal_weight_of_coercive
    (weight : ProductDiracMode → ℝ) (hCoercive : CoerciveDiagonalWeight weight) :
    ProperDiagonalWeight weight := by
  intro R
  obtain ⟨N, hN⟩ := hCoercive R
  exact (product_mode_bounding_box_finite N).subset hN

/-- A diagonal multiplier vanishes at infinity when every nonzero superlevel set is finite. -/
def DiagonalMultiplierVanishesAtInfinity
    (multiplier : ProductDiracMode → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Set.Finite {mode | ε ≤ ‖multiplier mode‖}

def shiftIResolventMultiplier (weight : ProductDiracMode → ℝ)
    (mode : ProductDiracMode) : ℂ :=
  1 / ((weight mode : ℂ) - Complex.I)

theorem complex_shift_I_inverse_is_diagonal_multiplier
    (weight : ProductDiracMode → ℝ) (φ : ComplexProductModeHilbert)
    (mode : ProductDiracMode) :
    complexShiftIInverse weight φ mode =
      shiftIResolventMultiplier weight mode * φ mode := by
  change φ mode / ((weight mode : ℂ) - Complex.I) =
    (1 / ((weight mode : ℂ) - Complex.I)) * φ mode
  rw [one_div, div_eq_mul_inv]
  ring

/-- Proper eigenvalue growth forces the diagonal `(D-i)⁻¹` coefficients to vanish at infinity. -/
theorem shift_I_multiplier_vanishes_at_infinity
    (weight : ProductDiracMode → ℝ) (hProper : ProperDiagonalWeight weight) :
    DiagonalMultiplierVanishesAtInfinity (shiftIResolventMultiplier weight) := by
  intro ε hε
  refine (hProper (1 / ε)).subset ?_
  intro mode hMode
  change ε ≤ ‖1 / ((weight mode : ℂ) - Complex.I)‖ at hMode
  rw [norm_div, norm_one] at hMode
  have hDenPos : 0 < ‖(weight mode : ℂ) - Complex.I‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_norm_real_sub_I (weight mode))
  have hMul : ε * ‖(weight mode : ℂ) - Complex.I‖ ≤ 1 :=
    (le_div_iff₀ hDenPos).1 hMode
  have hDen : ‖(weight mode : ℂ) - Complex.I‖ ≤ 1 / ε := by
    apply (le_div_iff₀ hε).2
    simpa [mul_comm] using hMul
  exact (norm_real_le_norm_real_sub_I (weight mode)).trans hDen

/-- Spectral-growth form of the compact-resolvent obligation for a diagonal operator. -/
structure DiagonalCompactResolventDecayCertificate
    (weight : ProductDiracMode → ℝ) : Prop where
  selfAdjoint : DiagonalSelfAdjointResolventCertificate weight
  properWeight : ProperDiagonalWeight weight
  resolventCoefficientsVanish :
    DiagonalMultiplierVanishesAtInfinity (shiftIResolventMultiplier weight)

theorem diagonal_compact_resolvent_decay_certificate
    (weight : ProductDiracMode → ℝ) (hProper : ProperDiagonalWeight weight) :
    DiagonalCompactResolventDecayCertificate weight where
  selfAdjoint := diagonal_self_adjoint_resolvent_certificate weight
  properWeight := hProper
  resolventCoefficientsVanish := shift_I_multiplier_vanishes_at_infinity weight hProper

end

end P0EFTJanusInfiniteL2DiracDomain
end JanusFormal
