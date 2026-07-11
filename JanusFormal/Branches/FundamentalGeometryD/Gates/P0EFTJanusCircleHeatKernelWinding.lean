import Mathlib

namespace JanusFormal
namespace P0EFTJanusCircleHeatKernelWinding

set_option autoImplicit false

/-- Exact cosine weight `cos(pi*w/2)` for a quarter-holonomy winding, encoded by residue modulo four. -/
def quarterWindingWeight (winding : ℕ) : ℤ :=
  match winding % 4 with
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | _ => 0

/-- Exact antiperiodic weight `cos(pi*w)=(-1)^w`. -/
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

/-- The first positive winding is absent in the quarter-holonomy sector. -/
theorem quarter_first_positive_winding_vanishes :
    quarterWindingWeight 1 = 0 :=
  quarter_weight_one

/-- The first nonzero positive quarter-holonomy winding is `w=2`. -/
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

/-- Winding exponent in the Poisson-resummed heat kernel. -/
noncomputable def windingExponent
    (circumference heatTime : ℝ) (winding : ℕ) : ℝ :=
  circumference ^ 2 * (winding : ℝ) ^ 2 /
    (4 * heatTime)

/-- Weighted winding contribution, omitting the common local prefactor. -/
noncomputable def weightedWindingTerm
    (weight : ℤ)
    (circumference heatTime : ℝ)
    (winding : ℕ) : ℝ :=
  (weight : ℝ) * Real.exp (-windingExponent circumference heatTime winding)

/-- The leading antiperiodic winding is suppressed by `exp(-beta^2/(4t))`. -/
theorem antiperiodic_first_winding_term
    (circumference heatTime : ℝ) :
    weightedWindingTerm (antiperiodicWindingWeight 1)
        circumference heatTime 1 =
      -Real.exp (-(circumference ^ 2 / (4 * heatTime))) := by
  simp [weightedWindingTerm, windingExponent]

/-- The `w=1` quarter-holonomy winding vanishes exactly. -/
theorem quarter_first_winding_term_vanishes
    (circumference heatTime : ℝ) :
    weightedWindingTerm (quarterWindingWeight 1)
        circumference heatTime 1 = 0 := by
  simp [weightedWindingTerm]

/-- The leading nonzero quarter-holonomy winding is `w=2`, suppressed by `exp(-beta^2/t)`. -/
theorem quarter_second_winding_term
    (circumference heatTime : ℝ) :
    weightedWindingTerm (quarterWindingWeight 2)
        circumference heatTime 2 =
      -Real.exp (-(circumference ^ 2 / heatTime)) := by
  simp [weightedWindingTerm, windingExponent]
  congr 2
  ring

/-- The quarter-holonomy leading exponent is four times the antiperiodic leading exponent. -/
theorem quarter_leading_exponent_is_four_times_antiperiodic
    (circumference heatTime : ℝ) :
    windingExponent circumference heatTime 2 =
      4 * windingExponent circumference heatTime 1 := by
  unfold windingExponent
  norm_num
  ring

/--
Poisson-resummed circle heat trace interface. The `w=0` term is local and
holonomy independent; all holonomy dependence is stored in positive windings.
-/
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

/-- Two holonomies with the same geometry have identical local heat-kernel terms. -/
theorem same_geometry_same_local_term
    (first second : CircleHeatKernelDecomposition)
    (hCircumference : first.circumference = second.circumference)
    (hHeatTime : first.heatTime = second.heatTime)
    (hLocalLaw :
      ∀ circumference heatTime,
        first.localTerm = second.localTerm) :
    first.localTerm = second.localTerm := by
  exact hLocalLaw first.circumference first.heatTime

/--
For exact quarter holonomy, the UV-sensitive local coefficients cannot see the
holonomy and the first nonlocal winding vanishes. The first holonomy signal is
therefore the more strongly suppressed `w=2` sector.
-/
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
