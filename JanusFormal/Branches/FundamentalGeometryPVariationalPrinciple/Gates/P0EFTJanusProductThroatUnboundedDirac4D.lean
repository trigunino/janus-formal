import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatUnboundedDiracSquared4D

/-!
# First-order self-adjoint product-throat Dirac operator

The signed positive square root of the product Dirac-square spectrum defines a
maximal first-order diagonal operator.  It is genuinely self-adjoint, and the
domain on which it can be applied twice is exactly the maximal domain of the
previous Dirac-square operator.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatUnboundedDirac4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open scoped ENNReal lp LinearPMap

/-- PT-signed first-order product eigenvalue. -/
def productThroatDiracEigenvalue
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Real :=
  fold.spectralSign *
    Real.sqrt (productThroatDiracSquaredEigenvalue data fold twist mode)

theorem productThroatDiracEigenvalue_sq
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracEigenvalue data fold twist mode ^ 2 =
      productThroatDiracSquaredEigenvalue data fold twist mode := by
  unfold productThroatDiracEigenvalue
  rw [mul_pow, Real.sq_sqrt
    (productThroatDiracSquaredEigenvalue_nonnegative data fold twist mode)]
  cases fold <;> norm_num

theorem productThroatDiracSquaredEigenvalue_coe_eq_mul
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) =
      (productThroatDiracEigenvalue data fold twist mode : Complex) *
        (productThroatDiracEigenvalue data fold twist mode : Complex) := by
  norm_cast
  simpa [pow_two] using
    (productThroatDiracEigenvalue_sq data fold twist mode).symm

/-- Maximal first-order weighted domain. -/
def productThroatDiracDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Submodule Complex (ProductThroatHeatHilbert data) where
  carrier := {state | ∃ image : ProductThroatHeatHilbert data, ∀ mode,
    image mode = (productThroatDiracEigenvalue data fold twist mode : Complex) *
      state mode}
  zero_mem' := ⟨0, by intro mode; simp⟩
  add_mem' := by
    rintro first second ⟨firstImage, hFirst⟩ ⟨secondImage, hSecond⟩
    refine ⟨firstImage + secondImage, ?_⟩
    intro mode
    change firstImage mode + secondImage mode =
      (productThroatDiracEigenvalue data fold twist mode : Complex) *
        (first mode + second mode)
    rw [hFirst mode, hSecond mode]
    ring
  smul_mem' := by
    intro scalar state
    rintro ⟨image, hImage⟩
    refine ⟨scalar • image, ?_⟩
    intro mode
    change scalar * image mode =
      (productThroatDiracEigenvalue data fold twist mode : Complex) *
        (scalar * state mode)
    rw [hImage mode]
    ring

def productThroatDiracImage
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : productThroatDiracDomain data fold twist) :
    ProductThroatHeatHilbert data :=
  state.property.choose

@[simp]
theorem productThroatDiracImage_apply
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : productThroatDiracDomain data fold twist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracImage data fold twist state mode =
      (productThroatDiracEigenvalue data fold twist mode : Complex) *
        state.1 mode :=
  state.property.choose_spec mode

/-- Genuine first-order maximal unbounded product Dirac operator. -/
def productThroatUnboundedDirac
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatHilbert data →ₗ.[Complex] ProductThroatHeatHilbert data where
  domain := productThroatDiracDomain data fold twist
  toFun :=
    { toFun := productThroatDiracImage data fold twist
      map_add' := by
        intro first second
        ext mode
        simp [productThroatDiracImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [productThroatDiracImage_apply]
        ring }

@[simp]
theorem productThroatUnboundedDirac_apply
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : (productThroatUnboundedDirac data fold twist).domain)
    (mode : ProductThroatHeatMode data) :
    productThroatUnboundedDirac data fold twist state mode =
      (productThroatDiracEigenvalue data fold twist mode : Complex) *
        state.1 mode :=
  productThroatDiracImage_apply data fold twist state mode

theorem productThroatHeatBasis_mem_diracDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatBasis data mode ∈ productThroatDiracDomain data fold twist := by
  refine ⟨(productThroatDiracEigenvalue data fold twist mode : Complex) •
    productThroatHeatBasis data mode, ?_⟩
  intro other
  change (productThroatDiracEigenvalue data fold twist mode : Complex) *
      (productThroatHeatBasis data mode other) =
    (productThroatDiracEigenvalue data fold twist other : Complex) *
      (productThroatHeatBasis data mode other)
  by_cases hOther : other = mode
  · subst other
    rfl
  · rw [productThroatHeatBasis_eq_single, lp.single_apply]
    simp [hOther]

theorem productThroatDiracDomain_dense
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Dense (productThroatDiracDomain data fold twist :
      Set (ProductThroatHeatHilbert data)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule Complex (ProductThroatHeatHilbert data)) =
        (Submodule.span Complex
          (Set.range (productThroatHeatBasis data))).topologicalClosure :=
      (HilbertBasis.dense_span (productThroatHeatBasis data)).symm
    _ ≤ (productThroatDiracDomain data fold twist).topologicalClosure :=
      Submodule.topologicalClosure_mono (Submodule.span_le.mpr (by
        rintro state ⟨mode, rfl⟩
        exact productThroatHeatBasis_mem_diracDomain data fold twist mode))

theorem productThroatUnboundedDirac_on_basis
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatUnboundedDirac data fold twist
        ⟨productThroatHeatBasis data mode,
          productThroatHeatBasis_mem_diracDomain data fold twist mode⟩ =
      (productThroatDiracEigenvalue data fold twist mode : Complex) •
        productThroatHeatBasis data mode := by
  ext other
  rw [productThroatUnboundedDirac_apply]
  change (productThroatDiracEigenvalue data fold twist other : Complex) *
      (productThroatHeatBasis data mode other) =
    (productThroatDiracEigenvalue data fold twist mode : Complex) *
      (productThroatHeatBasis data mode other)
  by_cases hOther : other = mode
  · subst other
    rfl
  · rw [productThroatHeatBasis_eq_single, lp.single_apply]
    simp [hOther]

theorem productThroatUnboundedDirac_isFormalAdjoint_self
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    (productThroatUnboundedDirac data fold twist).IsFormalAdjoint
      (productThroatUnboundedDirac data fold twist) := by
  intro first second
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  simp [productThroatDiracEigenvalue]
  ring

/-- Maximality of the real diagonal domain proves self-adjointness. -/
theorem productThroatUnboundedDirac_isSelfAdjoint
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    IsSelfAdjoint (productThroatUnboundedDirac data fold twist) := by
  let operator := productThroatUnboundedDirac data fold twist
  have hDense : Dense (operator.domain : Set (ProductThroatHeatHilbert data)) :=
    productThroatDiracDomain_dense data fold twist
  have hSymmetric : operator.IsFormalAdjoint operator :=
    productThroatUnboundedDirac_isFormalAdjoint_self data fold twist
  have hOperatorLeAdjoint : operator ≤ operator.adjoint :=
    hSymmetric.le_adjoint hDense
  have hAdjointDomain : operator.adjoint.domain ≤ operator.domain := by
    intro state hState
    let adjointState : operator.adjoint.domain := ⟨state, hState⟩
    let image : ProductThroatHeatHilbert data := operator.adjoint adjointState
    refine ⟨image, ?_⟩
    intro mode
    let basisState : operator.domain :=
      ⟨productThroatHeatBasis data mode,
        productThroatHeatBasis_mem_diracDomain data fold twist mode⟩
    have hInner := (LinearPMap.adjoint_isFormalAdjoint hDense).symm
      basisState adjointState
    change inner Complex (operator basisState)
        (adjointState : ProductThroatHeatHilbert data) =
      inner Complex (basisState : ProductThroatHeatHilbert data) image at hInner
    rw [show operator basisState =
        (productThroatDiracEigenvalue data fold twist mode : Complex) •
          productThroatHeatBasis data mode by
      exact productThroatUnboundedDirac_on_basis data fold twist mode,
      inner_smul_left,
      P0EFTJanusProductThroatUnboundedDiracSquared4D.productThroatHeatBasis_inner_left,
      P0EFTJanusProductThroatUnboundedDiracSquared4D.productThroatHeatBasis_inner_left]
      at hInner
    simpa [productThroatDiracEigenvalue] using hInner.symm
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt (le_antisymm hAdjointDomain hOperatorLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hOperatorLeAdjoint.2 hState.symm).symm

/-- First Dirac image of a state in the maximal square domain. -/
def productThroatDiracFirstImageOfSquared
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : productThroatDiracSquaredDomain data fold twist) :
    ProductThroatHeatHilbert data := by
  let first : ProductThroatHeatMode data → Complex := fun mode =>
    (productThroatDiracEigenvalue data fold twist mode : Complex) * state.1 mode
  have hBoundMem : Memℓp
      (fun mode : ProductThroatHeatMode data => ‖state.1 mode‖ +
        ‖productThroatDiracSquaredImage data fold twist state mode‖) 2 :=
    (lp.memℓp state.1).norm.add
      (lp.memℓp (productThroatDiracSquaredImage data fold twist state)).norm
  have hFirstMem : Memℓp first 2 := hBoundMem.mono' (fun mode => by
    let energy := productThroatDiracSquaredEigenvalue data fold twist mode
    have hEnergy : 0 ≤ energy :=
      productThroatDiracSquaredEigenvalue_nonnegative data fold twist mode
    have hAbs : |productThroatDiracEigenvalue data fold twist mode| ≤ 1 + energy := by
      have hSqrt : Real.sqrt energy ^ 2 = energy := Real.sq_sqrt hEnergy
      have hSignAbs : |fold.spectralSign| = 1 := by cases fold <;> norm_num
      rw [productThroatDiracEigenvalue, abs_mul, hSignAbs, one_mul,
        abs_of_nonneg (Real.sqrt_nonneg energy)]
      nlinarith [sq_nonneg (Real.sqrt energy - (1 / 2 : Real))]
    have hMul := mul_le_mul_of_nonneg_right hAbs (norm_nonneg (state.1 mode))
    have hEigenNorm :
        ‖(productThroatDiracEigenvalue data fold twist mode : Complex)‖ =
          |productThroatDiracEigenvalue data fold twist mode| := by
      simp [Real.norm_eq_abs]
    have hSquaredImageNorm :
        ‖productThroatDiracSquaredImage data fold twist state mode‖ =
          energy * ‖state.1 mode‖ := by
      rw [productThroatDiracSquaredImage_apply, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hEnergy]
    change ‖(productThroatDiracEigenvalue data fold twist mode : Complex) *
      state.1 mode‖ ≤ ‖(‖state.1 mode‖ +
        ‖productThroatDiracSquaredImage data fold twist state mode‖ : Real)‖
    rw [norm_mul, hEigenNorm]
    calc
      _ ≤ (1 + energy) * ‖state.1 mode‖ := hMul
      _ = ‖state.1 mode‖ + energy * ‖state.1 mode‖ := by ring
      _ = ‖state.1 mode‖ +
          ‖productThroatDiracSquaredImage data fold twist state mode‖ := by
        rw [hSquaredImageNorm]
      _ = ‖(‖state.1 mode‖ +
          ‖productThroatDiracSquaredImage data fold twist state mode‖ : Real)‖ := by
        symm
        exact Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  exact ⟨first, hFirstMem⟩

@[simp]
theorem productThroatDiracFirstImageOfSquared_apply
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : productThroatDiracSquaredDomain data fold twist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracFirstImageOfSquared data fold twist state mode =
      (productThroatDiracEigenvalue data fold twist mode : Complex) * state.1 mode :=
  rfl

/-- Domain of the actual composition `D ∘ D`. -/
def productThroatDiracIteratedDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Set (ProductThroatHeatHilbert data) :=
  {state | ∃ hState : state ∈ productThroatDiracDomain data fold twist,
    productThroatDiracImage data fold twist ⟨state, hState⟩ ∈
      productThroatDiracDomain data fold twist}

theorem mem_productThroatDiracIteratedDomain_of_mem_squaredDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : productThroatDiracSquaredDomain data fold twist) :
    state.1 ∈ productThroatDiracIteratedDomain data fold twist := by
  let first := productThroatDiracFirstImageOfSquared data fold twist state
  have hFirst : state.1 ∈ productThroatDiracDomain data fold twist :=
    ⟨first, productThroatDiracFirstImageOfSquared_apply data fold twist state⟩
  refine ⟨hFirst, ?_⟩
  have hImageEq :
      productThroatDiracImage data fold twist ⟨state.1, hFirst⟩ = first := by
    ext mode
    rw [productThroatDiracImage_apply]
    exact (productThroatDiracFirstImageOfSquared_apply data fold twist state mode).symm
  rw [hImageEq]
  refine ⟨productThroatDiracSquaredImage data fold twist state, ?_⟩
  intro mode
  rw [productThroatDiracSquaredImage_apply,
    productThroatDiracFirstImageOfSquared_apply,
    productThroatDiracSquaredEigenvalue_coe_eq_mul]
  ring

theorem mem_squaredDomain_of_mem_productThroatDiracIteratedDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : ProductThroatHeatHilbert data)
    (hState : state ∈ productThroatDiracIteratedDomain data fold twist) :
    state ∈ productThroatDiracSquaredDomain data fold twist := by
  rcases hState with ⟨hFirst, hSecond⟩
  rcases hSecond with ⟨second, hSecond⟩
  refine ⟨second, ?_⟩
  intro mode
  rw [hSecond mode, productThroatDiracImage_apply,
    productThroatDiracSquaredEigenvalue_coe_eq_mul]
  ring

theorem productThroatDiracSquaredDomain_eq_iteratedDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    (productThroatDiracSquaredDomain data fold twist :
      Set (ProductThroatHeatHilbert data)) =
      productThroatDiracIteratedDomain data fold twist := by
  ext state
  constructor
  · intro hState
    exact mem_productThroatDiracIteratedDomain_of_mem_squaredDomain data fold twist
      ⟨state, hState⟩
  · exact mem_squaredDomain_of_mem_productThroatDiracIteratedDomain
      data fold twist state

end

end P0EFTJanusProductThroatUnboundedDirac4D
end JanusFormal
