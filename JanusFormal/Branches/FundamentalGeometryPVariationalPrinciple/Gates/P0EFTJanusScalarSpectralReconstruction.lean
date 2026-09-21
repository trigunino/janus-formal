import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusParentBulkSpectralResponseSeparation

/-!
# Three regular spectral samples reconstruct one coupled scalar bulk mode

For the fixed pencil `a - z`, positivity of `a` makes `0, -1, -2` regular.
Their responses determine the bulk coefficient, squared normal coupling and
normal boundary coefficient whenever that coupling is nonzero. The remaining
sign is precisely a bulk sign change on the plane `trace = 0`.

The normal response alone leaves trace coefficients unseen. Adding two mixed
samples and one trace sample reconstructs the full two-sector parent modulo a
common bulk sign. All results retain fixed spectral normalization and concern
a finite-dimensional parent, not selection of a local Janus theory or terminal
T08 closure.
-/

namespace JanusFormal
namespace P0EFTJanusScalarSpectralReconstruction

set_option autoImplicit false

open P0EFTJanusParentBulkHelmholtzReciprocity
open P0EFTJanusParentBulkSpectralResponseSeparation

/-- Three samples determine a single-pole scalar response with nonzero residue. -/
theorem three_samples_reconstruct_scalar_response
    (a₁ a₂ d₁ d₂ c₁ c₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hd₁ : d₁ ≠ 0)
    (h₀ : c₁ - d₁ / a₁ = c₂ - d₂ / a₂)
    (h₁ : c₁ - d₁ / (a₁ + 1) = c₂ - d₂ / (a₂ + 1))
    (h₂ : c₁ - d₁ / (a₁ + 2) = c₂ - d₂ / (a₂ + 2)) :
    a₁ = a₂ ∧ d₁ = d₂ ∧ c₁ = c₂ := by
  have hA₁ : a₁ ≠ 0 := ne_of_gt ha₁
  have hA₂ : a₂ ≠ 0 := ne_of_gt ha₂
  have hA₁₁ : a₁ + 1 ≠ 0 := by linarith
  have hA₂₁ : a₂ + 1 ≠ 0 := by linarith
  have hA₁₂ : a₁ + 2 ≠ 0 := by linarith
  have hA₂₂ : a₂ + 2 ≠ 0 := by linarith
  field_simp [hA₁, hA₂] at h₀
  field_simp [hA₁₁, hA₂₁] at h₁
  field_simp [hA₁₂, hA₂₂] at h₂
  have hc : c₁ = c₂ := by nlinarith only [h₀, h₁, h₂]
  subst c₂
  have hd : d₁ = d₂ := by nlinarith only [h₀, h₁]
  subst d₂
  have ha : a₁ = a₂ := by
    apply mul_left_cancel₀ hd₁
    nlinarith only [h₀]
  exact ⟨ha, rfl, rfl⟩

/-- No pole occurs at any of the three reconstruction samples. -/
theorem reconstruction_samples_regular (parent : ParentBulkTwoSectorData)
    (hPositive : 0 < parent.bulkCoefficient) :
    parent.bulkCoefficient - 0 ≠ 0 ∧
      parent.bulkCoefficient - (-1) ≠ 0 ∧
      parent.bulkCoefficient - (-2) ≠ 0 := by
  constructor
  · simpa using ne_of_gt hPositive
  constructor <;> linarith

/-- The observable normal response reconstructs exactly these three coefficients. -/
theorem three_normal_samples_reconstruct_coefficients
    (first second : ParentBulkTwoSectorData)
    (hFirst : 0 < first.bulkCoefficient)
    (hSecond : 0 < second.bulkCoefficient)
    (hCoupled : first.bulkToNormal ≠ 0)
    (hZero : normalizedNormalSpectralResponse first 0 =
      normalizedNormalSpectralResponse second 0)
    (hOne : normalizedNormalSpectralResponse first (-1) =
      normalizedNormalSpectralResponse second (-1))
    (hTwo : normalizedNormalSpectralResponse first (-2) =
      normalizedNormalSpectralResponse second (-2)) :
    first.bulkCoefficient = second.bulkCoefficient ∧
      first.bulkToNormal ^ 2 = second.bulkToNormal ^ 2 ∧
      first.boundaryNormal = second.boundaryNormal := by
  apply three_samples_reconstruct_scalar_response _ _ _ _ _ _ hFirst hSecond
    (pow_ne_zero 2 hCoupled)
  · simpa [normalizedNormalSpectralResponse] using hZero
  · simpa [normalizedNormalSpectralResponse] using hOne
  · simpa [normalizedNormalSpectralResponse] using hTwo

/-- With the trace input zero, the only remaining ambiguity is bulk sign. -/
theorem three_normal_samples_identify_normal_plane_up_to_bulk_sign
    (first second : ParentBulkTwoSectorData)
    (hFirst : 0 < first.bulkCoefficient)
    (hSecond : 0 < second.bulkCoefficient)
    (hCoupled : first.bulkToNormal ≠ 0)
    (hZero : normalizedNormalSpectralResponse first 0 =
      normalizedNormalSpectralResponse second 0)
    (hOne : normalizedNormalSpectralResponse first (-1) =
      normalizedNormalSpectralResponse second (-1))
    (hTwo : normalizedNormalSpectralResponse first (-2) =
      normalizedNormalSpectralResponse second (-2)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∀ bulk normal : ℝ,
        parentAction first bulk normal 0 =
          parentAction second (ε * bulk) normal 0 := by
  rcases three_normal_samples_reconstruct_coefficients first second
    hFirst hSecond hCoupled hZero hOne hTwo with ⟨ha, hb, hc⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with hb | hb
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro bulk normal
    simp [parentAction, ha, hb, hc]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro bulk normal
    simp only [parentAction, ha, hb, hc]
    ring

/-- Mixed entry of the symmetric two-sector spectral response. -/
noncomputable def normalizedMixedSpectralResponse
    (parent : ParentBulkTwoSectorData) (z : ℝ) : ℝ :=
  parent.boundaryMixing -
    parent.bulkToNormal * parent.bulkToTrace / (parent.bulkCoefficient - z)

/-- Trace entry of the two-sector spectral response. -/
noncomputable def normalizedTraceSpectralResponse
    (parent : ParentBulkTwoSectorData) (z : ℝ) : ℝ :=
  parent.boundaryTrace - parent.bulkToTrace ^ 2 / (parent.bulkCoefficient - z)

/-- Once the pole is known, two samples determine the residue and constant. -/
theorem two_samples_reconstruct_fixed_pole
    (a d₁ d₂ c₁ c₂ : ℝ) (ha : 0 < a)
    (h₀ : c₁ - d₁ / a = c₂ - d₂ / a)
    (h₁ : c₁ - d₁ / (a + 1) = c₂ - d₂ / (a + 1)) :
    d₁ = d₂ ∧ c₁ = c₂ := by
  have hA : a ≠ 0 := ne_of_gt ha
  have hA₁ : a + 1 ≠ 0 := by linarith
  field_simp [hA] at h₀
  field_simp [hA₁] at h₁
  have hc : c₁ = c₂ := by nlinarith only [h₀, h₁]
  subst c₂
  exact ⟨by nlinarith only [h₀], rfl⟩

private theorem couplings_determine_common_sign
    (b₁ b₂ t₁ t₂ : ℝ) (hNonzero : b₁ ≠ 0)
    (hSquare : b₁ ^ 2 = b₂ ^ 2) (hMixed : b₁ * t₁ = b₂ * t₂) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ b₂ = ε * b₁ ∧ t₂ = ε * t₁ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hSquare.symm with hb | hb
  · have ht : t₂ = t₁ := by
      apply mul_left_cancel₀ hNonzero
      simpa [hb] using hMixed.symm
    exact ⟨1, Or.inl rfl, by simpa using hb, by simpa using ht⟩
  · have ht : t₂ = -t₁ := by
      apply mul_left_cancel₀ hNonzero
      rw [hb] at hMixed
      nlinarith only [hMixed]
    exact ⟨-1, Or.inr rfl, by simpa using hb, by simpa using ht⟩

/-- Three normal, two mixed and one trace samples reconstruct every coefficient,
with the same sign ambiguity on both bulk couplings. -/
theorem six_samples_reconstruct_parent_up_to_bulk_sign
    (first second : ParentBulkTwoSectorData)
    (hFirst : 0 < first.bulkCoefficient)
    (hSecond : 0 < second.bulkCoefficient)
    (hCoupled : first.bulkToNormal ≠ 0)
    (hNormalZero : normalizedNormalSpectralResponse first 0 =
      normalizedNormalSpectralResponse second 0)
    (hNormalOne : normalizedNormalSpectralResponse first (-1) =
      normalizedNormalSpectralResponse second (-1))
    (hNormalTwo : normalizedNormalSpectralResponse first (-2) =
      normalizedNormalSpectralResponse second (-2))
    (hMixedZero : normalizedMixedSpectralResponse first 0 =
      normalizedMixedSpectralResponse second 0)
    (hMixedOne : normalizedMixedSpectralResponse first (-1) =
      normalizedMixedSpectralResponse second (-1))
    (hTraceZero : normalizedTraceSpectralResponse first 0 =
      normalizedTraceSpectralResponse second 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      second.bulkCoefficient = first.bulkCoefficient ∧
      second.bulkToNormal = ε * first.bulkToNormal ∧
      second.bulkToTrace = ε * first.bulkToTrace ∧
      second.boundaryNormal = first.boundaryNormal ∧
      second.boundaryMixing = first.boundaryMixing ∧
      second.boundaryTrace = first.boundaryTrace ∧
      ∀ bulk normal trace : ℝ,
        parentAction second bulk normal trace =
          parentAction first (ε * bulk) normal trace := by
  rcases three_normal_samples_reconstruct_coefficients first second
    hFirst hSecond hCoupled hNormalZero hNormalOne hNormalTwo with ⟨ha, hb, hc⟩
  have hMix := two_samples_reconstruct_fixed_pole first.bulkCoefficient
    (first.bulkToNormal * first.bulkToTrace)
    (second.bulkToNormal * second.bulkToTrace)
    first.boundaryMixing second.boundaryMixing hFirst
    (by simpa [normalizedMixedSpectralResponse, ← ha] using hMixedZero)
    (by simpa [normalizedMixedSpectralResponse, ← ha] using hMixedOne)
  rcases couplings_determine_common_sign _ _ _ _ hCoupled hb hMix.1 with
    ⟨ε, hSign, hn, ht⟩
  have hSquare : ε ^ 2 = 1 := by
    rcases hSign with h | h <;> rw [h] <;> norm_num
  have htSquare : first.bulkToTrace ^ 2 = second.bulkToTrace ^ 2 := by
    rw [ht, mul_pow, hSquare, one_mul]
  have hTrace : second.boundaryTrace = first.boundaryTrace := by
    simp only [normalizedTraceSpectralResponse, sub_zero, ← ha, ← htSquare]
      at hTraceZero
    linarith only [hTraceZero]
  refine ⟨ε, hSign, ha.symm, hn, ht, hc.symm, hMix.2.symm, hTrace, ?_⟩
  intro bulk normal trace
  simp only [parentAction, ← ha, hn, ht, ← hc, ← hMix.2, hTrace,
    mul_pow, hSquare, one_mul]
  ring

end P0EFTJanusScalarSpectralReconstruction
end JanusFormal
