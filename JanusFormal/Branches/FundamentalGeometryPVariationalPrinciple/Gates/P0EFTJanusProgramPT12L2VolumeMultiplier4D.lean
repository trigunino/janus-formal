import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Bounded real volume multipliers on L2, including their exact inverse. -/
namespace JanusFormal.P0EFTJanusProgramPT12L2VolumeMultiplier4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace BoundedContinuousFunction
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X)

def l2VolumeMultiplier (weight : X →ᵇ Real) : Lp Real 2 μ →L[Real] Lp Real 2 μ :=
  (ContinuousLinearMap.mul Real Real).holderL μ ∞ 2 2
    ((weight.memLp_top (μ := μ)).toLp weight)

theorem l2VolumeMultiplier_ae (weight : X →ᵇ Real) (field : Lp Real 2 μ) :
    l2VolumeMultiplier μ weight field =ᵐ[μ] fun point => weight point * field point := by
  filter_upwards [(ContinuousLinearMap.mul Real Real).coeFn_holder (r := 2)
    ((weight.memLp_top (μ := μ)).toLp weight) field, (weight.memLp_top (μ := μ)).coeFn_toLp] with point hMul hWeight
  exact hMul.trans (congrArg (fun value : Real => value * field point) hWeight)

theorem l2VolumeMultiplier_inverse (weight inverse : X →ᵇ Real)
    (hInverse : ∀ point, weight point * inverse point = 1) (field : Lp Real 2 μ) :
    l2VolumeMultiplier μ weight (l2VolumeMultiplier μ inverse field) = field := by
  apply Lp.ext
  filter_upwards [l2VolumeMultiplier_ae μ weight (l2VolumeMultiplier μ inverse field),
    l2VolumeMultiplier_ae μ inverse field] with point hOuter hInner
  rw [hOuter, hInner, ← mul_assoc, hInverse, one_mul]

def l2VolumeEquiv (weight inverse : X →ᵇ Real)
    (hInverse : ∀ point, weight point * inverse point = 1) :
    Lp Real 2 μ ≃L[Real] Lp Real 2 μ where
  toLinearMap := (l2VolumeMultiplier μ weight).toLinearMap
  invFun := l2VolumeMultiplier μ inverse
  left_inv := l2VolumeMultiplier_inverse μ inverse weight (fun point => by rw [mul_comm, hInverse])
  right_inv := l2VolumeMultiplier_inverse μ weight inverse hInverse
  continuous_toFun := (l2VolumeMultiplier μ weight).continuous
  continuous_invFun := (l2VolumeMultiplier μ inverse).continuous

theorem l2VolumeMultiplier_symmetric (weight : X →ᵇ Real) (first second : Lp Real 2 μ) :
    inner Real (l2VolumeMultiplier μ weight first) second =
      inner Real first (l2VolumeMultiplier μ weight second) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2VolumeMultiplier_ae μ weight first,
    l2VolumeMultiplier_ae μ weight second] with point hFirst hSecond
  simp only [hFirst, hSecond, RCLike.inner_apply, conj_trivial]
  ring

end
end JanusFormal.P0EFTJanusProgramPT12L2VolumeMultiplier4D
