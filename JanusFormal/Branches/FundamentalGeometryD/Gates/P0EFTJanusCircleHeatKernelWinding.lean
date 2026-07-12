import Mathlib

namespace JanusFormal
namespace P0EFTJanusCircleHeatKernelWinding

set_option autoImplicit false

def quarterWindingWeight (winding : ℕ) : ℤ :=
  match winding % 4 with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | _ => 0

def antiperiodicWindingWeight (winding : ℕ) : ℤ :=
  if winding % 2 = 0 then 1 else -1

@[simp] theorem quarter_weight_zero : quarterWindingWeight 0 = 1 := by
  norm_num [quarterWindingWeight]
@[simp] theorem quarter_weight_one : quarterWindingWeight 1 = 0 := by
  norm_num [quarterWindingWeight]
@[simp] theorem quarter_weight_two : quarterWindingWeight 2 = -1 := by
  norm_num [quarterWindingWeight]
@[simp] theorem quarter_weight_three : quarterWindingWeight 3 = 0 := by
  norm_num [quarterWindingWeight]
@[simp] theorem quarter_weight_four : quarterWindingWeight 4 = 1 := by
  norm_num [quarterWindingWeight]
@[simp] theorem antiperiodic_weight_zero :
    antiperiodicWindingWeight 0 = 1 := by
  norm_num [antiperiodicWindingWeight]
@[simp] theorem antiperiodic_weight_one :
    antiperiodicWindingWeight 1 = -1 := by
  norm_num [antiperiodicWindingWeight]

theorem quarter_first_positive_winding_vanishes :
    quarterWindingWeight 1 = 0 := quarter_weight_one

theorem quarter_first_nonzero_positive_winding_is_two :
    quarterWindingWeight 2 ≠ 0 /\
      ∀ winding : ℕ,
        0 < winding → winding < 2 → quarterWindingWeight winding = 0 := by
  constructor
  · norm_num
  · intro winding hPositive hBelow
    have hOne : winding = 1 := by omega
    subst winding
    exact quarter_weight_one

noncomputable def windingExponent
    (circumference heatTime : ℝ) (winding : ℕ) : ℝ :=
  circumference ^ 2 * (winding : ℝ) ^ 2 / (4 * heatTime)

noncomputable def weightedWindingTerm
    (weight : ℤ) (circumference heatTime : ℝ) (winding : ℕ) : ℝ :=
  (weight : ℝ) * Real.exp (-windingExponent circumference heatTime winding)

theorem antiperiodic_first_winding_term
    (circumference heatTime : ℝ) :
    weightedWindingTerm (antiperiodicWindingWeight 1)
        circumference heatTime 1 =
      -Real.exp (-(circumference ^ 2 / (4 * heatTime))) := by
  simp [weightedWindingTerm, windingExponent]

theorem quarter_first_winding_term_vanishes
    (circumference heatTime : ℝ) :
    weightedWindingTerm (quarterWindingWeight 1)
        circumference heatTime 1 = 0 := by
  simp [weightedWindingTerm]

theorem quarter_second_winding_term
    (circumference heatTime : ℝ)
    (hHeatTime : heatTime ≠ 0) :
    weightedWindingTerm (quarterWindingWeight 2)
        circumference heatTime 2 =
      -Real.exp (-(circumference ^ 2 / heatTime)) := by
  have hExponent :
      windingExponent circumference heatTime 2 =
        circumference ^ 2 / heatTime := by
    unfold windingExponent
    field_simp [hHeatTime]
    ring
  simp [weightedWindingTerm, hExponent]

theorem quarter_leading_exponent_is_four_times_antiperiodic
    (circumference heatTime : ℝ) :
    windingExponent circumference heatTime 2 =
      4 * windingExponent circumference heatTime 1 := by
  unfold windingExponent
  ring

noncomputable def localCircleHeatTerm
    (circumference heatTime piConstant : ℝ) : ℝ :=
  circumference / Real.sqrt (4 * piConstant * heatTime)

theorem same_geometry_same_local_circle_heat_term
    (firstCircumference secondCircumference
      firstHeatTime secondHeatTime piConstant : ℝ)
    (hCircumference : firstCircumference = secondCircumference)
    (hHeatTime : firstHeatTime = secondHeatTime) :
    localCircleHeatTerm firstCircumference firstHeatTime piConstant =
      localCircleHeatTerm secondCircumference secondHeatTime piConstant := by
  rw [hCircumference, hHeatTime]

structure CircleHeatKernelDecomposition where
  circumference : ℝ
  heatTime : ℝ
  localTerm : ℝ
  nonlocalWindingSum : ℝ
  fullTrace : ℝ
  circumferencePositive : 0 < circumference
  heatTimePositive : 0 < heatTime
  decompositionLaw : fullTrace = localTerm + nonlocalWindingSum
  localTermIndependentOfHolonomy : Prop

structure QuarterHolonomyHeatKernelStatus where
  poissonResummationDerived : Prop
  localTermSeparated : Prop
  localCoefficientsHolonomyIndependent : Prop
  oddWindingCancellationProved : Prop
  leadingWindingTwoProved : Prop
  fullSphereProductHeatTraceDerived : Prop
  zetaEffectiveActionDerived : Prop

def quarterHolonomyHeatKernelClosed
    (s : QuarterHolonomyHeatKernelStatus) : Prop :=
  s.poissonResummationDerived /\
  s.localTermSeparated /\
  s.localCoefficientsHolonomyIndependent /\
  s.oddWindingCancellationProved /\
  s.leadingWindingTwoProved /\
  s.fullSphereProductHeatTraceDerived /\
  s.zetaEffectiveActionDerived

end P0EFTJanusCircleHeatKernelWinding
end JanusFormal
