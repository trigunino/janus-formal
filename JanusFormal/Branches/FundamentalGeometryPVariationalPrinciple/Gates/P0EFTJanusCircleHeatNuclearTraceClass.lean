import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatGeneratorDomain

/-!
# Nuclear trace-class certificate for the circle heat operator

At every positive time, the explicit circle heat operator is the operator-norm
sum of rank-one Fourier projections weighted by the heat eigenvalues.  The sum
of the component operator norms is finite, giving a concrete nuclear (hence
trace-class in the standard Hilbert-space sense) certificate even though this
Mathlib version has no general trace-class operator API.  Its nuclear trace is
the already constructed diagonal spectral heat trace.

The theorem is scoped to the normalized circle model.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatNuclearTraceClass

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open scoped ENNReal lp

/-- Rank-one Fourier summand of the positive-time heat operator. -/
def circleHeatRankOne
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode).smulRight
    ((circleOperatorHeatWeight time fold twist mode : ℂ) •
      circleFourierBasis mode)

@[simp]
theorem circleHeatRankOne_apply
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ)
    (state : CircleHilbert) :
    circleHeatRankOne time fold twist mode state =
      state mode •
        ((circleOperatorHeatWeight time fold twist mode : ℂ) •
          circleFourierBasis mode) := by
  rfl

theorem circleEvalCLM_opNorm_le_one (mode : ℤ) :
    ‖lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 mode‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro state
  change ‖state mode‖ ≤ 1 * ‖state‖
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    state mode

theorem circleOperatorHeatWeight_nonnegative
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    0 ≤ circleOperatorHeatWeight time fold twist mode := by
  unfold circleOperatorHeatWeight
  exact Real.exp_pos _ |>.le

theorem circleHeatRankOne_opNorm_le
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    ‖circleHeatRankOne time fold twist mode‖ ≤
      circleOperatorHeatWeight time fold twist mode := by
  rw [circleHeatRankOne, ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, circleFourierBasis_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg (circleOperatorHeatWeight_nonnegative time fold twist mode)]
  exact mul_le_of_le_one_left
    (circleOperatorHeatWeight_nonnegative time fold twist mode)
    (circleEvalCLM_opNorm_le_one mode)

theorem circleHeatRankOne_norm_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : ℤ => ‖circleHeatRankOne time fold twist mode‖) :=
  (circleOperatorHeatWeight_summable time fold twist).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (circleHeatRankOne_opNorm_le time fold twist)

theorem circleHeatRankOne_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (circleHeatRankOne time fold twist) :=
  Summable.of_norm (circleHeatRankOne_norm_summable time fold twist)

/-- Operator-norm sum of the rank-one heat expansion. -/
def circleHeatNuclearSum
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  ∑' mode : ℤ, circleHeatRankOne time fold twist mode

theorem circleHeatRankOne_on_basis
    (time : HeatTime) (fold : Fold) (twist : CircleTwist)
    (mode other : ℤ) :
    circleHeatRankOne time fold twist mode (circleFourierBasis other) =
      if mode = other then
        (circleOperatorHeatWeight time fold twist other : ℂ) •
          circleFourierBasis other
      else 0 := by
  by_cases hMode : mode = other
  · subst mode
    simp [circleHeatRankOne_apply, circleFourierBasis_eq_single]
  · simp [circleHeatRankOne_apply, circleFourierBasis_eq_single,
      lp.single_apply, hMode]

theorem circleHeatNuclearSum_on_basis
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    circleHeatNuclearSum time fold twist (circleFourierBasis mode) =
      (circleOperatorHeatWeight time fold twist mode : ℂ) •
        circleFourierBasis mode := by
  rw [circleHeatNuclearSum]
  rw [show
      (∑' other : ℤ, circleHeatRankOne time fold twist other)
          (circleFourierBasis mode) =
        ∑' other : ℤ,
          circleHeatRankOne time fold twist other
            (circleFourierBasis mode) by
    simpa only [ContinuousLinearMap.apply_apply] using
      (ContinuousLinearMap.apply ℂ CircleHilbert
        (circleFourierBasis mode)).map_tsum
        (circleHeatRankOne_summable time fold twist)]
  rw [tsum_eq_single mode]
  · simp
  · intro other hOther
    simp [hOther]

/-- The nuclear series is exactly the previously constructed heat semigroup. -/
theorem circleHeatNuclearSum_eq_semigroup
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearSum time fold twist =
      circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist := by
  have hDense : Dense
      (Submodule.span ℂ (Set.range circleFourierBasis) : Set CircleHilbert) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact HilbertBasis.dense_span circleFourierBasis
  apply ContinuousLinearMap.ext_on (s := Set.range circleFourierBasis) hDense
  rintro _ ⟨mode, rfl⟩
  rw [circleHeatNuclearSum_on_basis, circleHeatSemigroup_on_basis]
  congr 1

/-- Explicit nuclear certificate used in lieu of a missing general Mathlib
trace-class structure. -/
structure CircleHeatNuclearCertificate
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) where
  components : ℤ → (CircleHilbert →L[ℂ] CircleHilbert)
  components_eq : components = circleHeatRankOne time fold twist
  summable_norm : Summable (fun mode => ‖components mode‖)
  operator_eq_tsum :
    circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist =
      ∑' mode, components mode

def circleHeatNuclearCertificate
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    CircleHeatNuclearCertificate time fold twist where
  components := circleHeatRankOne time fold twist
  components_eq := rfl
  summable_norm := circleHeatRankOne_norm_summable time fold twist
  operator_eq_tsum := (circleHeatNuclearSum_eq_semigroup time fold twist).symm

/-- Nuclear trace of the explicit rank-one decomposition. -/
def circleHeatNuclearTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : ℝ :=
  ∑' mode : ℤ, circleOperatorHeatWeight time fold twist mode

theorem circleHeatNuclearTrace_eq_operatorEvenHeatTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTrace time fold twist =
      circleOperatorEvenHeatTrace time fold twist := by
  unfold circleHeatNuclearTrace circleOperatorEvenHeatTrace
  apply tsum_congr
  intro mode
  exact (circleSpectralHeatMode_diagonal time fold twist mode).symm

/-- The explicit nuclear traces of the PT-related circle sectors agree. -/
theorem circleHeatNuclearTrace_pt_eq_positive
    (time : HeatTime) (twist : CircleTwist) :
    circleHeatNuclearTrace time .pt twist =
      circleHeatNuclearTrace time .positive twist := by
  rw [circleHeatNuclearTrace_eq_operatorEvenHeatTrace,
    circleHeatNuclearTrace_eq_operatorEvenHeatTrace,
    circleOperatorEvenHeatTrace_eq_evenHeatTrace,
    circleOperatorEvenHeatTrace_eq_evenHeatTrace,
    evenHeatTrace_pt_eq_positive]

/-- The sum of rank-one operator norms is bounded by the positive spectral
trace, the concrete trace-class estimate. -/
theorem circleHeatNuclearNormSum_le_trace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    (∑' mode : ℤ, ‖circleHeatRankOne time fold twist mode‖) ≤
      circleHeatNuclearTrace time fold twist := by
  unfold circleHeatNuclearTrace
  exact Summable.tsum_le_tsum
    (fun mode => circleHeatRankOne_opNorm_le time fold twist mode)
    (circleHeatRankOne_norm_summable time fold twist)
    (circleOperatorHeatWeight_summable time fold twist)

end

end P0EFTJanusCircleHeatNuclearTraceClass
end JanusFormal
