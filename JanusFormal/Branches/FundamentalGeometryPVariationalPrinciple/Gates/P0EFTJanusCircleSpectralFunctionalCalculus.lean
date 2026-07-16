import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatSemigroupOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Pure-point spectral functional calculus for the circle Dirac operator

This gate constructs, independently of the existing heat semigroup, the
contractive bounded functional calculus associated with the Fourier
diagonalization of the self-adjoint circle Dirac operator.  A bounded scalar
function is evaluated on the real Dirac eigenvalues and then extended to the
whole circle Hilbert space as a bounded Fourier multiplier.  The construction
preserves the unit, pointwise multiplication/operator composition, and complex
conjugation/Hilbert adjoint.

Applying this generic construction to `x ↦ exp (-t * x²)` gives exactly the
previously constructed circle heat semigroup.  Thus the equality
`exp (-t D²) = circleHeatSemigroup t` is proved for the normalized pure-point
circle operator.

The scope is deliberately precise: Mathlib currently supplies no general
unbounded Borel functional calculus for `LinearPMap`.  This is the concrete
bounded pure-point functional calculus determined by the proved Fourier
eigenbasis, not a global Janus spectral theorem or a general Borel-calculus
API for arbitrary self-adjoint unbounded operators.
-/

namespace JanusFormal
namespace P0EFTJanusCircleSpectralFunctionalCalculus

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open scoped ComplexConjugate ENNReal lp

/-- The unit ball of bounded complex functions on the real spectrum.  No
measurability hypothesis is needed for the discrete pure-point calculus. -/
structure CircleContractiveSpectralFunction where
  toFun : ℝ → ℂ
  norm_le_one : ∀ x, ‖toFun x‖ ≤ 1

instance : CoeFun CircleContractiveSpectralFunction (fun _ => ℝ → ℂ) :=
  ⟨CircleContractiveSpectralFunction.toFun⟩

/-- Constant-one spectral function. -/
def circleSpectralOne : CircleContractiveSpectralFunction where
  toFun := fun _ => 1
  norm_le_one := by simp

/-- Pointwise product stays in the contractive unit ball. -/
def circleSpectralMul
    (first second : CircleContractiveSpectralFunction) :
    CircleContractiveSpectralFunction where
  toFun := fun x => first x * second x
  norm_le_one := by
    intro x
    exact (norm_mul_le (first x) (second x)).trans
      (mul_le_one₀ (first.norm_le_one x) (norm_nonneg _) (second.norm_le_one x))

/-- Pointwise complex conjugation is the involution of the spectral algebra. -/
def circleSpectralStar
    (function : CircleContractiveSpectralFunction) :
    CircleContractiveSpectralFunction where
  toFun := fun x => star (function x)
  norm_le_one := by
    intro x
    simpa using function.norm_le_one x

/-- Coordinatewise multiplication by a contractive function of an arbitrary
real pure-point spectrum. -/
def circlePurePointFunctionalCalculusLinearMap
    (spectrum : ℤ → ℝ) (function : CircleContractiveSpectralFunction) :
    CircleHilbert →ₗ[ℂ] CircleHilbert where
  toFun state := ⟨fun mode => function (spectrum mode) * state mode, by
    refine state.2.mono' ?_
    intro mode
    simpa using mul_le_mul_of_nonneg_right
      (function.norm_le_one (spectrum mode)) (norm_nonneg (state mode))⟩
  map_add' := by
    intro first second
    ext mode
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext mode
    simp [mul_left_comm]

/-- Bounded pure-point spectral calculus on the Fourier Hilbert space. -/
def circlePurePointFunctionalCalculus
    (spectrum : ℤ → ℝ) (function : CircleContractiveSpectralFunction) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (circlePurePointFunctionalCalculusLinearMap spectrum function).mkContinuous 1 (by
    intro state
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ℝ≥0∞)) (by norm_num)
    intro mode
    change ‖function (spectrum mode) * state mode‖ ≤ ‖state mode‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg (state mode))
      (function.norm_le_one (spectrum mode)))

@[simp]
theorem circlePurePointFunctionalCalculus_apply
    (spectrum : ℤ → ℝ) (function : CircleContractiveSpectralFunction)
    (state : CircleHilbert) (mode : ℤ) :
    circlePurePointFunctionalCalculus spectrum function state mode =
      function (spectrum mode) * state mode :=
  rfl

/-- The pure-point calculus sends the constant function one to the identity. -/
theorem circlePurePointFunctionalCalculus_one (spectrum : ℤ → ℝ) :
    circlePurePointFunctionalCalculus spectrum circleSpectralOne =
      ContinuousLinearMap.id ℂ CircleHilbert := by
  ext state mode
  simp [circlePurePointFunctionalCalculus_apply, circleSpectralOne]

/-- Pointwise multiplication becomes composition of bounded operators. -/
theorem circlePurePointFunctionalCalculus_mul
    (spectrum : ℤ → ℝ)
    (first second : CircleContractiveSpectralFunction) :
    circlePurePointFunctionalCalculus spectrum
        (circleSpectralMul first second) =
      (circlePurePointFunctionalCalculus spectrum first).comp
        (circlePurePointFunctionalCalculus spectrum second) := by
  ext state mode
  simp [circlePurePointFunctionalCalculus_apply, circleSpectralMul, mul_assoc]

/-- Complex conjugation of the scalar function becomes the Hilbert adjoint. -/
theorem circlePurePointFunctionalCalculus_star
    (spectrum : ℤ → ℝ)
    (function : CircleContractiveSpectralFunction) :
    circlePurePointFunctionalCalculus spectrum
        (circleSpectralStar function) =
      ContinuousLinearMap.adjoint
        (circlePurePointFunctionalCalculus spectrum function) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro first second
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro mode
  simp [circlePurePointFunctionalCalculus_apply, circleSpectralStar,
    mul_comm, mul_left_comm, mul_assoc]

/-- Functional calculus associated with the actual real circle Dirac
eigenvalues. -/
def circleDiracFunctionalCalculus
    (fold : Fold) (twist : CircleTwist)
    (function : CircleContractiveSpectralFunction) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  circlePurePointFunctionalCalculus
    (diracEigenvalue fold twist) function

@[simp]
theorem circleDiracFunctionalCalculus_apply
    (fold : Fold) (twist : CircleTwist)
    (function : CircleContractiveSpectralFunction)
    (state : CircleHilbert) (mode : ℤ) :
    circleDiracFunctionalCalculus fold twist function state mode =
      function (diracEigenvalue fold twist mode) * state mode :=
  rfl

/-- Exact diagonal action on the Fourier eigenbasis of the genuine unbounded
Dirac operator. -/
theorem circleDiracFunctionalCalculus_on_basis
    (fold : Fold) (twist : CircleTwist)
    (function : CircleContractiveSpectralFunction) (mode : ℤ) :
    circleDiracFunctionalCalculus fold twist function
        (circleFourierBasis mode) =
      function (diracEigenvalue fold twist mode) •
        circleFourierBasis mode := by
  ext other
  rw [circleDiracFunctionalCalculus_apply]
  by_cases hOther : other = mode
  · subst other
    simp [circleFourierBasis_eq_single]
  · simp [circleFourierBasis_eq_single, lp.single_apply, hOther]

/-- The contractive scalar function `x ↦ exp (-t x²)`. -/
def circleExpNegSquareSpectralFunction
    (time : HeatSemigroupTime) : CircleContractiveSpectralFunction where
  toFun := fun x => (Real.exp (-time.1 * x ^ 2) : ℂ)
  norm_le_one := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.2) (sq_nonneg x)

/-- Independent pure-point construction of `exp (-t D²)`. -/
def circleDiracExpNegSquare
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  circleDiracFunctionalCalculus fold twist
    (circleExpNegSquareSpectralFunction time)

@[simp]
theorem circleDiracExpNegSquare_apply
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleDiracExpNegSquare time fold twist state mode =
      (Real.exp
        (-time.1 * (diracEigenvalue fold twist mode) ^ 2) : ℂ) *
        state mode :=
  rfl

/-- The independently constructed bounded pure-point functional-calculus
exponential is exactly the existing circle heat semigroup. -/
theorem circleDiracExpNegSquare_eq_circleHeatSemigroup
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist) :
    circleDiracExpNegSquare time fold twist =
      circleHeatSemigroup time fold twist := by
  ext state mode
  rw [circleDiracExpNegSquare_apply, circleHeatSemigroup_apply]
  rw [circleHeatMultiplier,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  rfl

end

end P0EFTJanusCircleSpectralFunctionalCalculus
end JanusFormal
