import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkHelmholtzReciprocity

/-!
# Static Schur data do not determine a normalized spectral response

The bulk inner product is fixed to the usual real scalar inner product, and
the spectral pencil is `A - z I`, hence `a - z`: the coefficient of `z` is one
for both examples.  The boundary variable and its coupling have the same
normalization.  This finite-dimensional algebraic witness distinguishes
two positive, genuinely coupled quadratic parents with identical static Schur
data.  It does not select a physical Janus parent or establish terminal `T08`.

The response is meaningful away from the pole `z = a`; all comparison points
below are proved to avoid that pole.  No equivalence under arbitrary changes
of spectral or field normalization is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusParentBulkSpectralResponseSeparation

set_option autoImplicit false

open P0EFTJanusCoupledSectorHelmholtzSelection
open P0EFTJanusParentBulkHelmholtzReciprocity

/-- Normal-sector Schur response with fixed unit spectral coefficient. -/
noncomputable def normalizedNormalSpectralResponse
    (parent : ParentBulkTwoSectorData) (z : ℝ) : ℝ :=
  parent.boundaryNormal -
    parent.bulkToNormal ^ 2 / (parent.bulkCoefficient - z)

theorem normalized_response_at_zero_is_static
    (parent : ParentBulkTwoSectorData) :
    normalizedNormalSpectralResponse parent 0 =
      reducedNormalCoefficient parent := by
  simp [normalizedNormalSpectralResponse, reducedNormalCoefficient]

/-- Unit bulk coefficient, with nonzero normal coupling. -/
noncomputable def unitBulkParent (k : ℝ) : ParentBulkTwoSectorData :=
  { bulkCoefficient := 1
    bulkToNormal := 1
    bulkToTrace := 0
    boundaryNormal := k + 1
    boundaryMixing := 0
    boundaryTrace := k
    bulkCoefficientNonzero := by norm_num }

/-- Distinct bulk coefficient with the same coupling and static target. -/
noncomputable def doubleBulkParent (k : ℝ) : ParentBulkTwoSectorData :=
  { bulkCoefficient := 2
    bulkToNormal := 1
    bulkToTrace := 0
    boundaryNormal := k + 1 / 2
    boundaryMixing := 0
    boundaryTrace := k
    bulkCoefficientNonzero := by norm_num }

theorem both_parents_genuinely_coupled (k : ℝ) :
    (unitBulkParent k).bulkToNormal ≠ 0 ∧
      (doubleBulkParent k).bulkToNormal ≠ 0 := by
  norm_num [unitBulkParent, doubleBulkParent]

theorem comparison_points_avoid_poles (k : ℝ) :
    (unitBulkParent k).bulkCoefficient - 0 ≠ 0 ∧
    (doubleBulkParent k).bulkCoefficient - 0 ≠ 0 ∧
    (unitBulkParent k).bulkCoefficient - (-1) ≠ 0 ∧
    (doubleBulkParent k).bulkCoefficient - (-1) ≠ 0 := by
  norm_num [unitBulkParent, doubleBulkParent]

theorem both_parents_have_same_static_schur_data (k : ℝ) :
    reducedPotential (unitBulkParent k) =
      reducedPotential (doubleBulkParent k) ∧
    reducedNormalCoefficient (unitBulkParent k) = k ∧
    reducedNormalCoefficient (doubleBulkParent k) = k := by
  constructor
  · ext <;>
      simp [reducedPotential, reducedNormalCoefficient,
        reducedMixingCoefficient, reducedTraceCoefficient,
        unitBulkParent, doubleBulkParent]
  · simp [reducedNormalCoefficient, unitBulkParent, doubleBulkParent]

/-- A regular negative spectral point already distinguishes the parents. -/
theorem normalized_responses_differ_at_negative_one (k : ℝ) :
    normalizedNormalSpectralResponse (unitBulkParent k) (-1) -
      normalizedNormalSpectralResponse (doubleBulkParent k) (-1) =
        1 / 3 := by
  norm_num [normalizedNormalSpectralResponse, unitBulkParent,
    doubleBulkParent]
  ring

theorem normalized_response_functions_distinct (k : ℝ) :
    normalizedNormalSpectralResponse (unitBulkParent k) ≠
      normalizedNormalSpectralResponse (doubleBulkParent k) := by
  intro hEqual
  have hAt := congrFun hEqual (-1)
  have hDifference := normalized_responses_differ_at_negative_one k
  rw [hAt, sub_self] at hDifference
  norm_num at hDifference

theorem unit_bulk_action_square_completion (k bulk normal trace : ℝ) :
    parentAction (unitBulkParent k) bulk normal trace =
      (bulk + normal) ^ 2 / 2 +
        k * normal ^ 2 / 2 + k * trace ^ 2 / 2 := by
  unfold parentAction unitBulkParent
  ring

theorem double_bulk_action_square_completion (k bulk normal trace : ℝ) :
    parentAction (doubleBulkParent k) bulk normal trace =
      (bulk + normal / 2) ^ 2 +
        k * normal ^ 2 / 2 + k * trace ^ 2 / 2 := by
  unfold parentAction doubleBulkParent
  ring

private theorem positive_square_sum
    (k c x normal trace : ℝ) (hk : 0 < k) (hc : 0 < c)
    (hNonzero : x ≠ 0 ∨ normal ≠ 0 ∨ trace ≠ 0) :
    0 < c * x ^ 2 + k * normal ^ 2 / 2 + k * trace ^ 2 / 2 := by
  have hx := sq_nonneg x
  have hn := sq_nonneg normal
  have ht := sq_nonneg trace
  have hcx : 0 ≤ c * x ^ 2 := mul_nonneg (le_of_lt hc) hx
  have hkn : 0 ≤ k * normal ^ 2 := mul_nonneg (le_of_lt hk) hn
  have hkt : 0 ≤ k * trace ^ 2 := mul_nonneg (le_of_lt hk) ht
  rcases hNonzero with h | h | h
  · have hPos := mul_pos hc (sq_pos_of_ne_zero h)
    linarith
  · have hPos := mul_pos hk (sq_pos_of_ne_zero h)
    linarith
  · have hPos := mul_pos hk (sq_pos_of_ne_zero h)
    linarith

/-- Both full quadratic actions are positive away from the zero field when
the common reduced coefficient is positive. -/
theorem both_parent_actions_positive
    (k bulk normal trace : ℝ) (hk : 0 < k)
    (hNonzero : bulk ≠ 0 ∨ normal ≠ 0 ∨ trace ≠ 0) :
    0 < parentAction (unitBulkParent k) bulk normal trace ∧
      0 < parentAction (doubleBulkParent k) bulk normal trace := by
  have hUnit : bulk + normal ≠ 0 ∨ normal ≠ 0 ∨ trace ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    rcases hNonzero with hb | hn | ht
    · exact hb (by linarith [h.1, h.2.1])
    · exact hn h.2.1
    · exact ht h.2.2
  have hDouble : bulk + normal / 2 ≠ 0 ∨ normal ≠ 0 ∨ trace ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    rcases hNonzero with hb | hn | ht
    · exact hb (by linarith [h.1, h.2.1])
    · exact hn h.2.1
    · exact ht h.2.2
  rw [unit_bulk_action_square_completion, double_bulk_action_square_completion]
  constructor
  · convert positive_square_sum k (1 / 2) (bulk + normal) normal trace
      hk (by norm_num) hUnit using 1
    ring
  · simpa using positive_square_sum k 1 (bulk + normal / 2) normal trace
      hk (by norm_num) hDouble

/-- Static equality does not identify the normalized response, even for
nonzero couplings and positive parent actions. -/
theorem positive_coupled_static_data_do_not_select_spectral_response
    (k : ℝ) (hk : 0 < k) :
    reducedPotential (unitBulkParent k) =
        reducedPotential (doubleBulkParent k) ∧
    (unitBulkParent k).bulkToNormal ≠ 0 ∧
    (doubleBulkParent k).bulkToNormal ≠ 0 ∧
    normalizedNormalSpectralResponse (unitBulkParent k) ≠
        normalizedNormalSpectralResponse (doubleBulkParent k) ∧
    ∀ bulk normal trace : ℝ,
      bulk ≠ 0 ∨ normal ≠ 0 ∨ trace ≠ 0 →
        0 < parentAction (unitBulkParent k) bulk normal trace ∧
        0 < parentAction (doubleBulkParent k) bulk normal trace := by
  exact ⟨(both_parents_have_same_static_schur_data k).1,
    (both_parents_genuinely_coupled k).1,
    (both_parents_genuinely_coupled k).2,
    normalized_response_functions_distinct k,
    fun bulk normal trace h => both_parent_actions_positive k bulk normal trace hk h⟩

end P0EFTJanusParentBulkSpectralResponseSeparation
end JanusFormal
