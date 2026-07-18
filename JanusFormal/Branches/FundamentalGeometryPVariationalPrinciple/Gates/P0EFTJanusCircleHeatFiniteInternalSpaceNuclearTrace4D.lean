import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatFiniteMultiplicityNuclearTrace4D

/-!
# Nuclear circle heat operator on a genuine finite internal space

For a finite internal index type, the Hilbert space is the finite product of
circle Hilbert spaces.  Its heat operator acts diagonally.  The concrete
nuclear expansion is indexed by an internal component and a Fourier mode;
each summand factors through one rank-one circle component.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatFiniteInternalSpaceNuclearTrace4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatNuclearTraceClass
open scoped ENNReal lp

variable {Internal : Type} [Fintype Internal] [DecidableEq Internal]

/-- Genuine finite product of circle Hilbert spaces. -/
abbrev CircleFiniteInternalHilbert (Internal : Type) :=
  Internal → CircleHilbert

/-- Diagonal circle heat operator on every internal component. -/
def circleFiniteInternalHeat
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    CircleFiniteInternalHilbert Internal →L[Complex]
      CircleFiniteInternalHilbert Internal :=
  ContinuousLinearMap.piMap fun _ : Internal =>
    circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist

@[simp]
theorem circleFiniteInternalHeat_apply
    (time : HeatTime) (fold : Fold) (twist : CircleTwist)
    (state : CircleFiniteInternalHilbert Internal) (component : Internal) :
    circleFiniteInternalHeat time fold twist state component =
      circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist
        (state component) := by
  rfl

/-- Rank-one component supported on one internal coordinate and one Fourier
mode. -/
def circleFiniteInternalHeatRankOne
    (time : HeatTime) (fold : Fold) (twist : CircleTwist)
    (index : Internal × Int) :
    CircleFiniteInternalHilbert Internal →L[Complex]
      CircleFiniteInternalHilbert Internal :=
  (ContinuousLinearMap.single Complex
      (fun _ : Internal => CircleHilbert) index.1).comp
    ((circleHeatRankOne time fold twist index.2).comp
      (ContinuousLinearMap.proj index.1))

theorem circleFiniteInternalHeatRankOne_opNorm_le
    (time : HeatTime) (fold : Fold) (twist : CircleTwist)
    (index : Internal × Int) :
    ‖circleFiniteInternalHeatRankOne time fold twist index‖ ≤
      ‖circleHeatRankOne time fold twist index.2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro state
  simp only [circleFiniteInternalHeatRankOne,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
    ContinuousLinearMap.proj_apply, Pi.norm_single]
  exact (circleHeatRankOne time fold twist index.2).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm state index.1)
      (norm_nonneg _))

theorem circleFiniteInternalHeatRankOne_norm_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (fun index : Internal × Int =>
      ‖circleFiniteInternalHeatRankOne time fold twist index‖) := by
  apply (summable_prod_of_nonneg fun _ => norm_nonneg _).2
  constructor
  · intro component
    exact (circleHeatRankOne_norm_summable time fold twist).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun mode => circleFiniteInternalHeatRankOne_opNorm_le time fold twist
        (component, mode))
  · exact Summable.of_finite

theorem circleFiniteInternalHeatRankOne_summable
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    Summable (circleFiniteInternalHeatRankOne
      (Internal := Internal) time fold twist) :=
  Summable.of_norm (circleFiniteInternalHeatRankOne_norm_summable time fold twist)

private theorem circleFiniteInternalHeatRankOne_component_tsum_eq
    (time : HeatTime) (fold : Fold) (twist : CircleTwist)
    (component : Internal) :
    (∑' mode : Int,
      circleFiniteInternalHeatRankOne time fold twist (component, mode)) =
      (ContinuousLinearMap.single Complex
        (fun _ : Internal => CircleHilbert) component).comp
        ((circleHeatSemigroup (heatTimeToSemigroupTime time) fold twist).comp
          (ContinuousLinearMap.proj component)) := by
  have hSummable :=
    (circleFiniteInternalHeatRankOne_summable time fold twist).prod_factor component
  apply ContinuousLinearMap.ext
  intro state
  funext target
  rw [show
      (∑' mode : Int,
        circleFiniteInternalHeatRankOne time fold twist (component, mode)) state
          target =
        ∑' mode : Int,
          (circleFiniteInternalHeatRankOne time fold twist
            (component, mode) state) target by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply] using
      ((ContinuousLinearMap.proj target).comp
        (ContinuousLinearMap.apply Complex
          (CircleFiniteInternalHilbert Internal) state)).map_tsum hSummable]
  by_cases hTarget : target = component
  · subst target
    simp only [circleFiniteInternalHeatRankOne,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same]
    have hApply := (ContinuousLinearMap.apply Complex CircleHilbert
      (state component)).map_tsum
        (circleHeatRankOne_summable time fold twist)
    have hApply' :
        (∑' mode : Int, circleHeatRankOne time fold twist mode)
            (state component) =
          ∑' mode : Int,
            circleHeatRankOne time fold twist mode (state component) := by
      simpa only [ContinuousLinearMap.apply_apply] using hApply
    rw [← hApply']
    change circleHeatNuclearSum time fold twist (state component) = _
    rw [circleHeatNuclearSum_eq_semigroup]
  · simp [circleFiniteInternalHeatRankOne, hTarget]

/-- The genuine finite-internal nuclear expansion sums to the diagonal heat
operator. -/
theorem circleFiniteInternalHeatRankOne_tsum_eq
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    (∑' index : Internal × Int,
      circleFiniteInternalHeatRankOne time fold twist index) =
      circleFiniteInternalHeat time fold twist := by
  rw [(circleFiniteInternalHeatRankOne_summable time fold twist).tsum_prod]
  rw [tsum_fintype]
  simp_rw [circleFiniteInternalHeatRankOne_component_tsum_eq]
  apply ContinuousLinearMap.ext
  intro state
  funext component
  simp [circleFiniteInternalHeat, Finset.sum_apply]

/-- The nuclear trace is the internal dimension times the circle trace. -/
def circleFiniteInternalNuclearTrace
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) : Real :=
  Fintype.card Internal * circleHeatNuclearTrace time fold twist

theorem circleFiniteInternalNuclearTrace_pt_eq_positive
    (time : HeatTime) (twist : CircleTwist) :
    circleFiniteInternalNuclearTrace (Internal := Internal) time .pt twist =
      circleFiniteInternalNuclearTrace (Internal := Internal) time .positive twist := by
  rw [circleFiniteInternalNuclearTrace, circleFiniteInternalNuclearTrace,
    circleHeatNuclearTrace_pt_eq_positive]

end

end P0EFTJanusCircleHeatFiniteInternalSpaceNuclearTrace4D
end JanusFormal
