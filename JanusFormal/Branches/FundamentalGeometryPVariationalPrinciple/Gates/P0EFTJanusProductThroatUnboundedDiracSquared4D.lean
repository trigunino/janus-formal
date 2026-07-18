import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D

/-!
# Self-adjoint unbounded Dirac square on the product-throat spectrum

On the same Hilbert space used by the nuclear heat operator, the sum of the
monopole-sphere squared eigenvalue and the circle squared eigenvalue defines a
maximal real diagonal operator.  Its domain is dense, its graph is closed and
maximality proves genuine self-adjointness.  The positive-time exponential of
its diagonal coefficient is exactly the previously constructed heat operator.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatUnboundedDiracSquared4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D
open scoped ENNReal lp LinearPMap

/-- Squared product Dirac coefficient. -/
def productThroatDiracSquaredEigenvalue
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Real :=
  sphereEigenvalueSquared data mode.1.1 +
    circleOperatorSquaredEigenvalue fold twist mode.2

theorem productThroatDiracSquaredEigenvalue_nonnegative
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    0 ≤ productThroatDiracSquaredEigenvalue data fold twist mode := by
  exact add_nonneg (sphere_eigenvalue_squared_positive data mode.1.1).le
    (by
      rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
      exact eigenvalueSq_nonnegative fold twist mode.2)

/-- Maximal domain of the product Dirac square. -/
def productThroatDiracSquaredDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Submodule Complex (ProductThroatHeatHilbert data) where
  carrier := {state | ∃ image : ProductThroatHeatHilbert data, ∀ mode,
    image mode = (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
      state mode}
  zero_mem' := ⟨0, by intro mode; simp⟩
  add_mem' := by
    rintro first second ⟨firstImage, hFirst⟩ ⟨secondImage, hSecond⟩
    refine ⟨firstImage + secondImage, ?_⟩
    intro mode
    change firstImage mode + secondImage mode =
      (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
        (first mode + second mode)
    rw [hFirst mode, hSecond mode]
    ring
  smul_mem' := by
    intro scalar state
    rintro ⟨image, hImage⟩
    refine ⟨scalar • image, ?_⟩
    intro mode
    change scalar * image mode =
      (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
        (scalar * state mode)
    rw [hImage mode]
    ring

def productThroatDiracSquaredImage
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : productThroatDiracSquaredDomain data fold twist) :
    ProductThroatHeatHilbert data :=
  state.property.choose

@[simp]
theorem productThroatDiracSquaredImage_apply
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : productThroatDiracSquaredDomain data fold twist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracSquaredImage data fold twist state mode =
      (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
        state.1 mode :=
  state.property.choose_spec mode

/-- Genuine maximal unbounded product Dirac-square operator. -/
def productThroatUnboundedDiracSquared
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatHilbert data →ₗ.[Complex] ProductThroatHeatHilbert data where
  domain := productThroatDiracSquaredDomain data fold twist
  toFun :=
    { toFun := productThroatDiracSquaredImage data fold twist
      map_add' := by
        intro first second
        ext mode
        simp [productThroatDiracSquaredImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [productThroatDiracSquaredImage_apply]
        ring }

@[simp]
theorem productThroatUnboundedDiracSquared_apply
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (state : (productThroatUnboundedDiracSquared data fold twist).domain)
    (mode : ProductThroatHeatMode data) :
    productThroatUnboundedDiracSquared data fold twist state mode =
      (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
        state.1 mode :=
  productThroatDiracSquaredImage_apply data fold twist state mode

theorem productThroatHeatBasis_mem_diracSquaredDomain
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatBasis data mode ∈
      productThroatDiracSquaredDomain data fold twist := by
  refine ⟨(productThroatDiracSquaredEigenvalue data fold twist mode : Complex) •
    productThroatHeatBasis data mode, ?_⟩
  intro other
  change (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
      (productThroatHeatBasis data mode other) =
    (productThroatDiracSquaredEigenvalue data fold twist other : Complex) *
      (productThroatHeatBasis data mode other)
  by_cases hOther : other = mode
  · subst other
    rfl
  · rw [productThroatHeatBasis_eq_single, lp.single_apply]
    simp [hOther]

theorem productThroatDiracSquaredDomain_dense
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    Dense (productThroatDiracSquaredDomain data fold twist :
      Set (ProductThroatHeatHilbert data)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule Complex (ProductThroatHeatHilbert data)) =
        (Submodule.span Complex
          (Set.range (productThroatHeatBasis data))).topologicalClosure :=
      (HilbertBasis.dense_span (productThroatHeatBasis data)).symm
    _ ≤ (productThroatDiracSquaredDomain data fold twist).topologicalClosure :=
      Submodule.topologicalClosure_mono (Submodule.span_le.mpr (by
        rintro state ⟨mode, rfl⟩
        exact productThroatHeatBasis_mem_diracSquaredDomain data fold twist mode))

theorem productThroatUnboundedDiracSquared_on_basis
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatUnboundedDiracSquared data fold twist
        ⟨productThroatHeatBasis data mode,
          productThroatHeatBasis_mem_diracSquaredDomain data fold twist mode⟩ =
      (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) •
        productThroatHeatBasis data mode := by
  ext other
  rw [productThroatUnboundedDiracSquared_apply]
  change (productThroatDiracSquaredEigenvalue data fold twist other : Complex) *
      (productThroatHeatBasis data mode other) =
    (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
      (productThroatHeatBasis data mode other)
  by_cases hOther : other = mode
  · subst other
    rfl
  · rw [productThroatHeatBasis_eq_single, lp.single_apply]
    simp [hOther]

theorem productThroatHeatBasis_inner_left
    (data : ProductThroatSpectralData) (mode : ProductThroatHeatMode data)
    (state : ProductThroatHeatHilbert data) :
    inner Complex (productThroatHeatBasis data mode) state = state mode := by
  rw [productThroatHeatBasis_eq_single, lp.inner_single_left]
  simp

theorem productThroatUnboundedDiracSquared_isFormalAdjoint_self
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    (productThroatUnboundedDiracSquared data fold twist).IsFormalAdjoint
      (productThroatUnboundedDiracSquared data fold twist) := by
  intro first second
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  simp [productThroatDiracSquaredEigenvalue]
  ring

theorem mem_productThroatUnboundedDiracSquared_graph_iff
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (point : ProductThroatHeatHilbert data × ProductThroatHeatHilbert data) :
    point ∈ (productThroatUnboundedDiracSquared data fold twist).graph ↔
      ∀ mode, point.2 mode =
        (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
          point.1 mode := by
  constructor
  · intro hPoint
    rw [LinearPMap.mem_graph_iff] at hPoint
    rcases hPoint with ⟨state, hState, hImage⟩
    intro mode
    calc
      point.2 mode = productThroatUnboundedDiracSquared data fold twist state mode :=
        congrArg (fun image : ProductThroatHeatHilbert data => image mode) hImage.symm
      _ = _ := by rw [productThroatUnboundedDiracSquared_apply, hState]
  · intro hPoint
    have hDomain : point.1 ∈ productThroatDiracSquaredDomain data fold twist :=
      ⟨point.2, hPoint⟩
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨point.1, hDomain⟩, rfl, ?_⟩
    ext mode
    rw [productThroatUnboundedDiracSquared_apply]
    exact (hPoint mode).symm

theorem productThroatUnboundedDiracSquared_isClosed
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    (productThroatUnboundedDiracSquared data fold twist).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hGraph :
      ((productThroatUnboundedDiracSquared data fold twist).graph :
        Set (ProductThroatHeatHilbert data × ProductThroatHeatHilbert data)) =
      ⋂ mode : ProductThroatHeatMode data, {point | point.2 mode =
        (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) *
          point.1 mode} := by
    ext point
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_productThroatUnboundedDiracSquared_graph_iff data fold twist point
  rw [hGraph]
  apply isClosed_iInter
  intro mode
  exact isClosed_eq
    ((lp.evalCLM Complex (fun _ : ProductThroatHeatMode data => Complex) 2 mode)
      |>.continuous.comp continuous_snd)
    (continuous_const.mul
      ((lp.evalCLM Complex (fun _ : ProductThroatHeatMode data => Complex) 2 mode)
        |>.continuous.comp continuous_fst))

/-- Maximality of the real weighted domain proves genuine self-adjointness. -/
theorem productThroatUnboundedDiracSquared_isSelfAdjoint
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    IsSelfAdjoint (productThroatUnboundedDiracSquared data fold twist) := by
  let operator := productThroatUnboundedDiracSquared data fold twist
  have hDense : Dense (operator.domain : Set (ProductThroatHeatHilbert data)) :=
    productThroatDiracSquaredDomain_dense data fold twist
  have hSymmetric : operator.IsFormalAdjoint operator :=
    productThroatUnboundedDiracSquared_isFormalAdjoint_self data fold twist
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
        productThroatHeatBasis_mem_diracSquaredDomain data fold twist mode⟩
    have hInner := (LinearPMap.adjoint_isFormalAdjoint hDense).symm
      basisState adjointState
    change inner Complex (operator basisState)
        (adjointState : ProductThroatHeatHilbert data) =
      inner Complex (basisState : ProductThroatHeatHilbert data) image at hInner
    rw [show operator basisState =
        (productThroatDiracSquaredEigenvalue data fold twist mode : Complex) •
          productThroatHeatBasis data mode by
      exact productThroatUnboundedDiracSquared_on_basis data fold twist mode,
      inner_smul_left, productThroatHeatBasis_inner_left,
      productThroatHeatBasis_inner_left] at hInner
    simpa using hInner.symm
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt (le_antisymm hAdjointDomain hOperatorLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hOperatorLeAdjoint.2 hState.symm).symm

/-- The exponential of the unbounded diagonal coefficient is exactly the
bounded product heat multiplier. -/
theorem productThroatHeatWeight_eq_exp_diracSquared
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatWeight data time fold twist mode =
      Real.exp (-time.1 *
        productThroatDiracSquaredEigenvalue data fold twist mode) := by
  unfold productThroatHeatWeight sphereModeHeatWeight
    circleOperatorHeatWeight productThroatDiracSquaredEigenvalue
  rw [← Real.exp_add]
  congr 1
  ring

end

end P0EFTJanusProductThroatUnboundedDiracSquared4D
end JanusFormal
