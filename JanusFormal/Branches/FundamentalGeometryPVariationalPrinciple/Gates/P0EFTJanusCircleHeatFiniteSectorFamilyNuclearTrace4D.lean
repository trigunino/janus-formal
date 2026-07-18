import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatFiniteInternalSpaceNuclearTrace4D

/-!
# Nuclear heat expansion for a heterogeneous finite sector family

Each internal component may carry its own fold and circle twist.  The heat
operator is the corresponding block-diagonal finite product.  Its nuclear
expansion is the sum of the componentwise Fourier rank-one expansions, and
simultaneously flipping every fold preserves the total nuclear trace.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatFiniteSectorFamilyNuclearTrace4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatNuclearTraceClass
open P0EFTJanusCircleHeatFiniteInternalSpaceNuclearTrace4D
open scoped ENNReal lp

variable {Internal : Type} [Fintype Internal] [DecidableEq Internal]

/-- Fold and holonomy carried by one finite internal sector. -/
structure CircleFiniteSector where
  fold : Fold
  twist : CircleTwist

/-- PT flips the Fourier fold and leaves its twist fixed. -/
def foldPTFlip : Fold → Fold
  | .positive => .pt
  | .pt => .positive

@[simp] theorem foldPTFlip_positive : foldPTFlip .positive = .pt := rfl
@[simp] theorem foldPTFlip_pt : foldPTFlip .pt = .positive := rfl
@[simp] theorem foldPTFlip_involutive (fold : Fold) :
    foldPTFlip (foldPTFlip fold) = fold := by
  cases fold <;> rfl

def CircleFiniteSector.pt (sector : CircleFiniteSector) : CircleFiniteSector where
  fold := foldPTFlip sector.fold
  twist := sector.twist

/-- Block-diagonal heat operator with component-dependent fold and twist. -/
def circleFiniteSectorFamilyHeat
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    CircleFiniteInternalHilbert Internal →L[Complex]
      CircleFiniteInternalHilbert Internal :=
  ContinuousLinearMap.piMap fun component : Internal =>
    circleHeatSemigroup (heatTimeToSemigroupTime time)
      (sector component).fold (sector component).twist

@[simp]
theorem circleFiniteSectorFamilyHeat_apply
    (time : HeatTime) (sector : Internal → CircleFiniteSector)
    (state : CircleFiniteInternalHilbert Internal) (component : Internal) :
    circleFiniteSectorFamilyHeat time sector state component =
      circleHeatSemigroup (heatTimeToSemigroupTime time)
        (sector component).fold (sector component).twist (state component) := by
  rfl

/-- Rank-one Fourier component of one heterogeneous internal sector. -/
def circleFiniteSectorFamilyHeatRankOne
    (time : HeatTime) (sector : Internal → CircleFiniteSector)
    (index : Internal × Int) :
    CircleFiniteInternalHilbert Internal →L[Complex]
      CircleFiniteInternalHilbert Internal :=
  (ContinuousLinearMap.single Complex
      (fun _ : Internal => CircleHilbert) index.1).comp
    ((circleHeatRankOne time (sector index.1).fold
        (sector index.1).twist index.2).comp
      (ContinuousLinearMap.proj index.1))

theorem circleFiniteSectorFamilyHeatRankOne_opNorm_le
    (time : HeatTime) (sector : Internal → CircleFiniteSector)
    (index : Internal × Int) :
    ‖circleFiniteSectorFamilyHeatRankOne time sector index‖ ≤
      ‖circleHeatRankOne time (sector index.1).fold
        (sector index.1).twist index.2‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro state
  simp only [circleFiniteSectorFamilyHeatRankOne,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
    ContinuousLinearMap.proj_apply, Pi.norm_single]
  exact (circleHeatRankOne time (sector index.1).fold
      (sector index.1).twist index.2).le_opNorm _ |>.trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm state index.1)
      (norm_nonneg _))

theorem circleFiniteSectorFamilyHeatRankOne_norm_summable
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    Summable (fun index : Internal × Int =>
      ‖circleFiniteSectorFamilyHeatRankOne time sector index‖) := by
  apply (summable_prod_of_nonneg fun _ => norm_nonneg _).2
  constructor
  · intro component
    exact (circleHeatRankOne_norm_summable time (sector component).fold
      (sector component).twist).of_nonneg_of_le
        (fun _ => norm_nonneg _)
        (fun mode => circleFiniteSectorFamilyHeatRankOne_opNorm_le time sector
          (component, mode))
  · exact Summable.of_finite

theorem circleFiniteSectorFamilyHeatRankOne_summable
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    Summable (circleFiniteSectorFamilyHeatRankOne time sector) :=
  Summable.of_norm
    (circleFiniteSectorFamilyHeatRankOne_norm_summable time sector)

private theorem circleFiniteSectorFamilyHeatRankOne_component_tsum_eq
    (time : HeatTime) (sector : Internal → CircleFiniteSector)
    (component : Internal) :
    (∑' mode : Int,
      circleFiniteSectorFamilyHeatRankOne time sector (component, mode)) =
      (ContinuousLinearMap.single Complex
        (fun _ : Internal => CircleHilbert) component).comp
        ((circleHeatSemigroup (heatTimeToSemigroupTime time)
          (sector component).fold (sector component).twist).comp
          (ContinuousLinearMap.proj component)) := by
  have hSummable :=
    (circleFiniteSectorFamilyHeatRankOne_summable time sector).prod_factor component
  apply ContinuousLinearMap.ext
  intro state
  funext target
  rw [show
      (∑' mode : Int,
        circleFiniteSectorFamilyHeatRankOne time sector (component, mode)) state
          target =
        ∑' mode : Int,
          (circleFiniteSectorFamilyHeatRankOne time sector
            (component, mode) state) target by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.proj_apply] using
      ((ContinuousLinearMap.proj target).comp
        (ContinuousLinearMap.apply Complex
          (CircleFiniteInternalHilbert Internal) state)).map_tsum hSummable]
  by_cases hTarget : target = component
  · subst target
    simp only [circleFiniteSectorFamilyHeatRankOne,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same]
    have hApply := (ContinuousLinearMap.apply Complex CircleHilbert
      (state component)).map_tsum
        (circleHeatRankOne_summable time (sector component).fold
          (sector component).twist)
    have hApply' :
        (∑' mode : Int, circleHeatRankOne time (sector component).fold
          (sector component).twist mode) (state component) =
          ∑' mode : Int, circleHeatRankOne time (sector component).fold
            (sector component).twist mode (state component) := by
      simpa only [ContinuousLinearMap.apply_apply] using hApply
    rw [← hApply']
    change circleHeatNuclearSum time (sector component).fold
      (sector component).twist (state component) = _
    rw [circleHeatNuclearSum_eq_semigroup]
  · simp [circleFiniteSectorFamilyHeatRankOne, hTarget]

/-- The heterogeneous rank-one expansion sums to the full block-diagonal
operator. -/
theorem circleFiniteSectorFamilyHeatRankOne_tsum_eq
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    (∑' index : Internal × Int,
      circleFiniteSectorFamilyHeatRankOne time sector index) =
      circleFiniteSectorFamilyHeat time sector := by
  rw [(circleFiniteSectorFamilyHeatRankOne_summable time sector).tsum_prod,
    tsum_fintype]
  simp_rw [circleFiniteSectorFamilyHeatRankOne_component_tsum_eq]
  apply ContinuousLinearMap.ext
  intro state
  funext component
  simp [circleFiniteSectorFamilyHeat, Finset.sum_apply]

/-- Total nuclear trace of the heterogeneous finite family. -/
def circleFiniteSectorFamilyNuclearTrace
    (time : HeatTime) (sector : Internal → CircleFiniteSector) : Real :=
  ∑ component : Internal,
    circleHeatNuclearTrace time (sector component).fold (sector component).twist

theorem circleHeatNuclearTrace_ptFlip
    (time : HeatTime) (fold : Fold) (twist : CircleTwist) :
    circleHeatNuclearTrace time (foldPTFlip fold) twist =
      circleHeatNuclearTrace time fold twist := by
  cases fold
  · exact circleHeatNuclearTrace_pt_eq_positive time twist
  · exact (circleHeatNuclearTrace_pt_eq_positive time twist).symm

/-- Simultaneous PT of every finite internal sector preserves the total
nuclear trace. -/
theorem circleFiniteSectorFamilyNuclearTrace_pt_eq
    (time : HeatTime) (sector : Internal → CircleFiniteSector) :
    circleFiniteSectorFamilyNuclearTrace time (fun i => (sector i).pt) =
      circleFiniteSectorFamilyNuclearTrace time sector := by
  unfold circleFiniteSectorFamilyNuclearTrace CircleFiniteSector.pt
  apply Finset.sum_congr rfl
  intro component _
  exact circleHeatNuclearTrace_ptFlip time (sector component).fold
    (sector component).twist

end

end P0EFTJanusCircleHeatFiniteSectorFamilyNuclearTrace4D
end JanusFormal
