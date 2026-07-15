import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleDiracHeatTraceCancellation
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Closed unbounded circle Fourier--Dirac operator

This gate upgrades the algebraic Fourier multiplier from
`P0EFTJanusCircleDiracHeatTraceCancellation` to a genuine partially defined
operator on `ℓ²(ℤ, ℂ)`.  Its maximal diagonal domain consists exactly of
states for which multiplication by the real eigenvalue sequence is again in
`ℓ²`.  The finite Fourier span lies in this domain and is dense.  The operator
is symmetric, its graph is closed, and the maximal-domain diagonal operator
is self-adjoint.  Elementary Fourier vectors also prove that it is not bounded
by any uniform operator norm on its domain.

The result concerns the one-dimensional diagonal circle model only.  It does
not construct the full Janus Dirac operator, a local heat-kernel coefficient,
a determinant line, an anomaly density, or a normalization law.
-/

namespace JanusFormal
namespace P0EFTJanusCircleUnboundedDiracDomain

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open scoped ComplexConjugate LinearPMap

/-- Complex Hilbert space of square-summable integer Fourier coefficients. -/
abbrev CircleHilbert := lp (fun _ : ℤ => ℂ) 2

/-- The real circle eigenvalue, embedded into the complex scalar field. -/
def complexDiracEigenvalue
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) : ℂ :=
  (diracEigenvalue fold twist mode : ℂ)

/-- Maximal weighted domain: diagonal multiplication must again define an
`ℓ²` vector. -/
def circleDiracDomain
    (fold : Fold) (twist : CircleTwist) : Submodule ℂ CircleHilbert where
  carrier := {state | ∃ image : CircleHilbert, ∀ mode,
    image mode = complexDiracEigenvalue fold twist mode * state mode}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro mode
    simp
  add_mem' := by
    rintro first second ⟨firstImage, hFirst⟩ ⟨secondImage, hSecond⟩
    refine ⟨firstImage + secondImage, ?_⟩
    intro mode
    change firstImage mode + secondImage mode =
      complexDiracEigenvalue fold twist mode * (first mode + second mode)
    rw [hFirst mode, hSecond mode]
    ring
  smul_mem' := by
    intro scalar state
    rintro ⟨image, hImage⟩
    refine ⟨scalar • image, ?_⟩
    intro mode
    change scalar * image mode =
      complexDiracEigenvalue fold twist mode * (scalar * state mode)
    rw [hImage mode]
    ring

/-- The uniquely determined weighted image selected from domain membership. -/
def circleDiracImage
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracDomain fold twist) : CircleHilbert :=
  state.property.choose

@[simp]
theorem circleDiracImage_apply
    (fold : Fold) (twist : CircleTwist)
    (state : circleDiracDomain fold twist) (mode : ℤ) :
    circleDiracImage fold twist state mode =
      complexDiracEigenvalue fold twist mode * state.1 mode :=
  state.property.choose_spec mode

/-- Maximal diagonal circle Dirac operator as a `LinearPMap`. -/
def circleUnboundedDirac
    (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →ₗ.[ℂ] CircleHilbert where
  domain := circleDiracDomain fold twist
  toFun :=
    { toFun := circleDiracImage fold twist
      map_add' := by
        intro first second
        ext mode
        simp [circleDiracImage_apply]
        ring
      map_smul' := by
        intro scalar state
        ext mode
        simp [circleDiracImage_apply]
        ring }

@[simp]
theorem circleUnboundedDirac_apply
    (fold : Fold) (twist : CircleTwist)
    (state : (circleUnboundedDirac fold twist).domain) (mode : ℤ) :
    circleUnboundedDirac fold twist state mode =
      complexDiracEigenvalue fold twist mode * state.1 mode :=
  circleDiracImage_apply fold twist state mode

/-- Canonical Hilbert basis of integer Fourier modes. -/
def circleFourierBasis : HilbertBasis ℤ ℂ CircleHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ CircleHilbert)

@[simp]
theorem circleFourierBasis_eq_single (mode : ℤ) :
    circleFourierBasis mode = lp.single 2 mode (1 : ℂ) :=
  by
    rw [← HilbertBasis.repr_symm_single circleFourierBasis mode]
    change (circleFourierBasis.repr).symm
      (lp.single 2 mode (1 : ℂ)) = lp.single 2 mode (1 : ℂ)
    rw [show circleFourierBasis.repr =
        LinearIsometryEquiv.refl ℂ CircleHilbert by rfl]
    simpa only [LinearIsometryEquiv.coe_refl, id_eq] using
      (LinearIsometryEquiv.refl ℂ CircleHilbert).symm_apply_apply
        (lp.single 2 mode (1 : ℂ))

theorem circleFourierBasis_mem_domain
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleFourierBasis mode ∈ circleDiracDomain fold twist := by
  refine ⟨complexDiracEigenvalue fold twist mode • circleFourierBasis mode, ?_⟩
  intro other
  by_cases hOther : other = mode
  · subst other
    simp [circleFourierBasis_eq_single]
  · simp [circleFourierBasis_eq_single, lp.single_apply, hOther]

/-- The maximal diagonal domain is dense because it contains the finite
Fourier span. -/
theorem circleDiracDomain_dense
    (fold : Fold) (twist : CircleTwist) :
    Dense (circleDiracDomain fold twist : Set CircleHilbert) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  calc
    (⊤ : Submodule ℂ CircleHilbert) =
        (Submodule.span ℂ (Set.range circleFourierBasis)).topologicalClosure :=
      (HilbertBasis.dense_span circleFourierBasis).symm
    _ ≤ (circleDiracDomain fold twist).topologicalClosure :=
      Submodule.topologicalClosure_mono (Submodule.span_le.mpr (by
        rintro state ⟨mode, rfl⟩
        exact circleFourierBasis_mem_domain fold twist mode))

theorem circleFourierBasis_norm (mode : ℤ) :
    ‖circleFourierBasis mode‖ = 1 := by
  exact (HilbertBasis.orthonormal circleFourierBasis).1 mode

theorem circleUnboundedDirac_on_basis
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleUnboundedDirac fold twist
        ⟨circleFourierBasis mode,
          circleFourierBasis_mem_domain fold twist mode⟩ =
      complexDiracEigenvalue fold twist mode • circleFourierBasis mode := by
  ext other
  by_cases hOther : other = mode
  · subst other
    simp [circleFourierBasis_eq_single]
  · simp [circleFourierBasis_eq_single, lp.single_apply, hOther]

theorem circleFourierBasis_inner_left
    (mode : ℤ) (state : CircleHilbert) :
    inner ℂ (circleFourierBasis mode) state = state mode := by
  rw [circleFourierBasis_eq_single, lp.inner_single_left]
  simp

/-- Real diagonal multiplication is symmetric on the weighted domain. -/
theorem circleUnboundedDirac_isFormalAdjoint_self
    (fold : Fold) (twist : CircleTwist) :
    (circleUnboundedDirac fold twist).IsFormalAdjoint
      (circleUnboundedDirac fold twist) := by
  intro first second
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  simp [complexDiracEigenvalue]
  ring

/-- Coordinate characterization of the graph. -/
theorem mem_circleUnboundedDirac_graph_iff
    (fold : Fold) (twist : CircleTwist)
    (point : CircleHilbert × CircleHilbert) :
    point ∈ (circleUnboundedDirac fold twist).graph ↔
      ∀ mode, point.2 mode =
        complexDiracEigenvalue fold twist mode * point.1 mode := by
  constructor
  · intro hPoint
    rw [LinearPMap.mem_graph_iff] at hPoint
    rcases hPoint with ⟨state, hState, hImage⟩
    intro mode
    calc
      point.2 mode = circleUnboundedDirac fold twist state mode := by
        exact congrArg (fun image : CircleHilbert => image mode) hImage.symm
      _ = complexDiracEigenvalue fold twist mode * state.1 mode := by
        rw [circleUnboundedDirac_apply]
      _ = complexDiracEigenvalue fold twist mode * point.1 mode := by
        rw [hState]
  · intro hPoint
    have hDomain : point.1 ∈ circleDiracDomain fold twist :=
      ⟨point.2, hPoint⟩
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨point.1, hDomain⟩, rfl, ?_⟩
    ext mode
    rw [circleUnboundedDirac_apply]
    exact (hPoint mode).symm

/-- The maximal diagonal graph is the intersection of closed coordinate
relations, hence is closed. -/
theorem circleUnboundedDirac_isClosed
    (fold : Fold) (twist : CircleTwist) :
    (circleUnboundedDirac fold twist).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hGraph :
      ((circleUnboundedDirac fold twist).graph :
          Set (CircleHilbert × CircleHilbert)) =
        ⋂ mode : ℤ, {point | point.2 mode =
          complexDiracEigenvalue fold twist mode * point.1 mode} := by
    ext point
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_circleUnboundedDirac_graph_iff fold twist point
  rw [hGraph]
  apply isClosed_iInter
  intro mode
  exact isClosed_eq
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode).continuous.comp continuous_snd)
    (continuous_const.mul
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode).continuous.comp continuous_fst))

/-- No finite constant bounds the operator on unit vectors in its domain. -/
theorem circleUnboundedDirac_not_uniformly_bounded
    (fold : Fold) (twist : CircleTwist) (bound : ℝ) :
    ∃ state : (circleUnboundedDirac fold twist).domain,
      ‖(state : CircleHilbert)‖ = 1 ∧
        bound < ‖circleUnboundedDirac fold twist state‖ := by
  obtain ⟨mode, hMode⟩ := exists_int_gt (max bound 0)
  let state : (circleUnboundedDirac fold twist).domain :=
    ⟨circleFourierBasis mode,
      circleFourierBasis_mem_domain fold twist mode⟩
  refine ⟨state, circleFourierBasis_norm mode, ?_⟩
  have hBoundMode : bound < (mode : ℝ) :=
    lt_of_le_of_lt (le_max_left bound 0) hMode
  have hModePositive : 0 < (mode : ℝ) :=
    lt_of_le_of_lt (le_max_right bound 0) hMode
  have hBoundEigen : bound < baseEigenvalue twist mode := by
    unfold baseEigenvalue
    linarith [twist.nonnegative]
  have hEigenPositive : 0 < baseEigenvalue twist mode := by
    unfold baseEigenvalue
    linarith [twist.nonnegative]
  change bound < ‖circleUnboundedDirac fold twist state‖
  rw [show circleUnboundedDirac fold twist state =
      complexDiracEigenvalue fold twist mode • circleFourierBasis mode by
    exact circleUnboundedDirac_on_basis fold twist mode]
  rw [norm_smul, circleFourierBasis_norm, mul_one]
  cases fold <;>
    simpa [complexDiracEigenvalue, diracEigenvalue, abs_of_pos hEigenPositive]
      using hBoundEigen

/-- Maximality of the weighted domain upgrades symmetry to self-adjointness. -/
theorem circleUnboundedDirac_isSelfAdjoint
    (fold : Fold) (twist : CircleTwist) :
    IsSelfAdjoint (circleUnboundedDirac fold twist) := by
  let operator := circleUnboundedDirac fold twist
  have hDense : Dense (operator.domain : Set CircleHilbert) :=
    circleDiracDomain_dense fold twist
  have hSymmetric : operator.IsFormalAdjoint operator :=
    circleUnboundedDirac_isFormalAdjoint_self fold twist
  have hOperatorLeAdjoint : operator ≤ operator.adjoint :=
    hSymmetric.le_adjoint hDense
  have hAdjointDomain : operator.adjoint.domain ≤ operator.domain := by
    intro state hState
    let adjointState : operator.adjoint.domain := ⟨state, hState⟩
    let image : CircleHilbert := operator.adjoint adjointState
    refine ⟨image, ?_⟩
    intro mode
    let basisState : operator.domain :=
      ⟨circleFourierBasis mode,
        circleFourierBasis_mem_domain fold twist mode⟩
    have hInner := (LinearPMap.adjoint_isFormalAdjoint hDense).symm
      basisState adjointState
    change inner ℂ (operator basisState) (adjointState : CircleHilbert) =
      inner ℂ (basisState : CircleHilbert) image at hInner
    rw [show operator basisState =
        complexDiracEigenvalue fold twist mode • circleFourierBasis mode by
      exact circleUnboundedDirac_on_basis fold twist mode,
      inner_smul_left, circleFourierBasis_inner_left,
      circleFourierBasis_inner_left] at hInner
    simpa [complexDiracEigenvalue] using hInner.symm
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt
    (le_antisymm hAdjointDomain hOperatorLeAdjoint.1)
  intro adjointState operatorState hState
  exact (hOperatorLeAdjoint.2 hState.symm).symm

end

end P0EFTJanusCircleUnboundedDiracDomain
end JanusFormal
