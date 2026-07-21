import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAsymptoticMatrixValuationCriterion4D

/-! # Matrix valuation criterion with inactive eventually-zero entries -/

namespace JanusFormal
namespace P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusSignedNormalizedInversePowerDivergence4D
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

/-- Active entries have a certified nonzero leading asymptotic; inactive
entries vanish on a punctured neighborhood of zero. -/
structure ActiveAsymptoticMatrixData where
  entry : Fin 4 → Fin 4 → Real → Real
  active : Fin 4 → Fin 4 → Prop
  leadingCoefficient : Fin 4 → Fin 4 → Real
  leadingOrder : Fin 4 → Fin 4 → Nat
  leading_nonzero : ∀ i j, active i j → leadingCoefficient i j ≠ 0
  normalized_tendsto : ∀ i j, active i j →
    Tendsto (fun t => entry i j t * (t ^ leadingOrder i j)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (leadingCoefficient i j))
  inactive_eventually_zero : ∀ i j, ¬ active i j →
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), entry i j t = 0

def normalizedEntry (data : ActiveAsymptoticMatrixData) (i j : Fin 4)
    (t : Real) : Real :=
  data.entry i j t * (t ^ data.leadingOrder i j)⁻¹

def transportedEntry (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) (i j : Fin 4) (t : Real) : Real :=
  t ^ frameExponent i * data.entry i j t * (t ^ frameExponent j)⁻¹

def transportedMatrix (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) (t : Real) : Matrix4 :=
  fun i j => transportedEntry data frameExponent i j t

def valuationLimit (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) : Matrix4 := by
  classical
  exact fun i j => if data.active i j then
    if frameExponent j = frameExponent i + data.leadingOrder i j then
      data.leadingCoefficient i j else 0 else 0

def ActiveValuationsNonnegative (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) : Prop :=
  ∀ i j, data.active i j →
    frameExponent j ≤ frameExponent i + data.leadingOrder i j

private theorem transportedEntry_eq_normalized_positive
    (data : ActiveAsymptoticMatrixData) (frameExponent : Fin 4 → Nat)
    (i j : Fin 4) {t : Real} (ht : t ≠ 0)
    (h : frameExponent j ≤ frameExponent i + data.leadingOrder i j) :
    transportedEntry data frameExponent i j t = normalizedEntry data i j t *
      t ^ (frameExponent i + data.leadingOrder i j - frameExponent j) := by
  have hf : data.entry i j t =
      normalizedEntry data i j t * t ^ data.leadingOrder i j := by
    simp [normalizedEntry, ht]
  rw [transportedEntry, hf, pow_sub₀ t ht h]
  field_simp [pow_ne_zero _ ht]
  ring

private theorem transportedEntry_eq_normalized_inverse
    (data : ActiveAsymptoticMatrixData) (frameExponent : Fin 4 → Nat)
    (i j : Fin 4) {t : Real} (ht : t ≠ 0)
    (h : frameExponent i + data.leadingOrder i j ≤ frameExponent j) :
    transportedEntry data frameExponent i j t = normalizedEntry data i j t *
      (t ^ (frameExponent j - (frameExponent i + data.leadingOrder i j)))⁻¹ := by
  have hf : data.entry i j t =
      normalizedEntry data i j t * t ^ data.leadingOrder i j := by
    simp [normalizedEntry, ht]
  rw [transportedEntry, hf]
  field_simp [pow_ne_zero _ ht]
  have hp : t ^ frameExponent i * t ^ data.leadingOrder i j *
      t ^ (frameExponent j - (frameExponent i + data.leadingOrder i j)) =
      t ^ frameExponent j := by
    rw [← pow_add, ← pow_add, Nat.add_sub_of_le h]
  calc
    t ^ frameExponent i * normalizedEntry data i j t *
        t ^ data.leadingOrder i j *
        t ^ (frameExponent j - (frameExponent i + data.leadingOrder i j)) =
      normalizedEntry data i j t *
        (t ^ frameExponent i * t ^ data.leadingOrder i j *
          t ^ (frameExponent j - (frameExponent i + data.leadingOrder i j))) := by ring
    _ = _ := by rw [hp]

theorem transportedMatrix_tendsto (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat)
    (hValuation : ActiveValuationsNonnegative data frameExponent) :
    Tendsto (transportedMatrix data frameExponent) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (valuationLimit data frameExponent)) := by
  have hEntries : ∀ i j, Tendsto
      (fun t => transportedEntry data frameExponent i j t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (valuationLimit data frameExponent i j)) := by
    intro i j
    by_cases hActive : data.active i j
    · rw [valuationLimit, if_pos hActive]
      have hNorm := data.normalized_tendsto i j hActive
      change Tendsto (normalizedEntry data i j) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (data.leadingCoefficient i j)) at hNorm
      by_cases heq : frameExponent j = frameExponent i + data.leadingOrder i j
      · rw [if_pos heq]
        apply hNorm.congr'
        filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [heq] using (transportedEntry_eq_normalized_positive data frameExponent
          i j ht.ne' (hValuation i j hActive)).symm
      · rw [if_neg heq]
        have hlt : frameExponent j < frameExponent i + data.leadingOrder i j :=
          lt_of_le_of_ne (hValuation i j hActive) heq
        have hPow := positivePower_tendsto_zero (Nat.sub_pos_of_lt hlt)
        simpa using (hNorm.mul hPow).congr' (by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact (transportedEntry_eq_normalized_positive data frameExponent i j
            ht.ne' (hValuation i j hActive)).symm)
    · rw [valuationLimit, if_neg hActive]
      apply tendsto_const_nhds.congr'
      filter_upwards [data.inactive_eventually_zero i j hActive] with t ht
      simp [transportedEntry, ht]
  have hPi : Tendsto
      (fun t i j => transportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fun i j => valuationLimit data frameExponent i j)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    exact hEntries i
  exact hPi

theorem transportedMatrix_no_finite_limit_of_negative_active_entry
    (data : ActiveAsymptoticMatrixData) (frameExponent : Fin 4 → Nat)
    {i j : Fin 4} (hActive : data.active i j)
    (hNegative : frameExponent i + data.leadingOrder i j < frameExponent j)
    (candidate : Matrix4) :
    ¬ Tendsto (transportedMatrix data frameExponent) (nhdsWithin 0 (Set.Ioi 0))
      (nhds candidate) := by
  intro hMatrix
  have hNoFinite := normalized_mul_inversePower_no_finite_limit
    (normalizedEntry data i j) (data.normalized_tendsto i j hActive)
    (data.leading_nonzero i j hActive) (Nat.sub_pos_of_lt hNegative) (candidate i j)
  apply hNoFinite
  have hEntry := (continuous_id.matrix_elem i j).tendsto candidate
  apply (hEntry.comp hMatrix).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact transportedEntry_eq_normalized_inverse data frameExponent i j ht.ne' hNegative.le

/-- Active valuations are exactly the obstruction to a finite matrix limit;
eventually-zero inactive entries impose no condition. -/
theorem activeValuationsNonnegative_iff_exists_finite_limit
    (data : ActiveAsymptoticMatrixData) (frameExponent : Fin 4 → Nat) :
    ActiveValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto (transportedMatrix data frameExponent) (nhdsWithin 0 (Set.Ioi 0))
          (nhds candidate) := by
  constructor
  · intro hValuation
    exact ⟨valuationLimit data frameExponent,
      transportedMatrix_tendsto data frameExponent hValuation⟩
  · rintro ⟨candidate, hCandidate⟩ i j hActive
    by_contra hValuation
    exact transportedMatrix_no_finite_limit_of_negative_active_entry data frameExponent
      hActive (Nat.lt_of_not_ge hValuation) candidate hCandidate

end
end P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D
end JanusFormal
