import JanusFormal.Foundations.ProgramMWellConditionedEmbedding
import Mathlib.Analysis.Real.Sqrt

/-!
# MF-MAN-004: external 1+1 Minkowski test target

Null coordinates `(u,v)` turn future causal order into the product order.
We fix the convention `ds² = -du dv`, hence diamond volume is
`Δu Δv / 2` and timelike proper time is `sqrt (Δu Δv)`.
This target is supplied externally; it is not derived from Program M.
-/

namespace JanusFormal.ProgramM

/-- A point in the external 1+1-dimensional Minkowski test target, represented
in future-oriented null coordinates. -/
abbrev MinkowskiTwoPoint := ℝ × ℝ

/-- A closed causal diamond with ordered endpoints. -/
structure MinkowskiTwoDiamond where
  lower : MinkowskiTwoPoint
  upper : MinkowskiTwoPoint
  ordered : lower ≤ upper

def minkowskiTwoContains (d : MinkowskiTwoDiamond) (x : MinkowskiTwoPoint) : Prop :=
  d.lower ≤ x ∧ x ≤ d.upper

/-- Spacetime volume in the fixed convention `dt dx = du dv / 2`. -/
noncomputable def minkowskiTwoVolume (d : MinkowskiTwoDiamond) : ℝ :=
  ((d.upper.1 - d.lower.1) * (d.upper.2 - d.lower.2)) / 2

/-- Future proper time; it is zero when the endpoints are not causally ordered. -/
noncomputable def minkowskiTwoProperTime
    (x y : MinkowskiTwoPoint) : ℝ :=
  if x ≤ y then Real.sqrt ((y.1 - x.1) * (y.2 - x.2)) else 0

theorem minkowskiTwoVolume_nonneg (d : MinkowskiTwoDiamond) :
    0 ≤ minkowskiTwoVolume d := by
  have hu : 0 ≤ d.upper.1 - d.lower.1 := sub_nonneg.mpr d.ordered.1
  have hv : 0 ≤ d.upper.2 - d.lower.2 := sub_nonneg.mpr d.ordered.2
  exact div_nonneg (mul_nonneg hu hv) (by norm_num)

theorem minkowskiTwoProperTime_nonneg (x y : MinkowskiTwoPoint) :
    0 ≤ minkowskiTwoProperTime x y := by
  by_cases hxy : x ≤ y
  · simp [minkowskiTwoProperTime, hxy, Real.sqrt_nonneg]
  · simp [minkowskiTwoProperTime, hxy]

theorem minkowskiTwoProperTime_zero_of_not_ordered
    (x y : MinkowskiTwoPoint) (hxy : ¬ x ≤ y) :
    minkowskiTwoProperTime x y = 0 := by
  simp [minkowskiTwoProperTime, hxy]

/-- In this normalization, twice the diamond volume equals squared proper time. -/
theorem minkowskiTwo_two_mul_volume_eq_properTime_sq
    (x y : MinkowskiTwoPoint) (hxy : x ≤ y) :
    2 * minkowskiTwoVolume ⟨x, y, hxy⟩ =
      minkowskiTwoProperTime x y ^ 2 := by
  have hu : 0 ≤ y.1 - x.1 := sub_nonneg.mpr hxy.1
  have hv : 0 ≤ y.2 - x.2 := sub_nonneg.mpr hxy.2
  have hp : 0 ≤ (y.1 - x.1) * (y.2 - x.2) := mul_nonneg hu hv
  rw [minkowskiTwoProperTime, if_pos hxy, Real.sq_sqrt hp]
  unfold minkowskiTwoVolume
  ring

/-- Concrete external target for exercising `MF-MAN-003`. -/
noncomputable def minkowskiTwoTarget :
    CausalVolumeTimeTarget MinkowskiTwoPoint MinkowskiTwoDiamond where
  identifier := "external-minkowski-1+1-null-target"
  identifier_nonempty := by decide
  contains := minkowskiTwoContains
  volume := minkowskiTwoVolume
  properTime := minkowskiTwoProperTime
  volume_nonneg := minkowskiTwoVolume_nonneg
  properTime_nonneg := minkowskiTwoProperTime_nonneg
  properTime_zero_of_not_ordered := minkowskiTwoProperTime_zero_of_not_ordered

end JanusFormal.ProgramM
