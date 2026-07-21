import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSignedNormalizedInversePowerDivergence4D

/-! # Matrix valuation criterion for finite monomial sums -/

namespace JanusFormal
namespace P0EFTJanusFinitePolynomialMatrixValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusFiniteMonomialLeadingValuation4D
open P0EFTJanusSignedNormalizedInversePowerDivergence4D
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

abbrev Matrix4 := P0EFTJanusMatrixSquareRootFrechetSylvester.Matrix4

structure FinitePolynomialMatrixData (ι : Type*) where
  tail : Finset ι
  leadingCoefficient : Fin 4 → Fin 4 → Real
  leadingOrder : Fin 4 → Fin 4 → Nat
  coefficient : Fin 4 → Fin 4 → ι → Real
  order : Fin 4 → Fin 4 → ι → Nat
  leading_nonzero : ∀ i j, leadingCoefficient i j ≠ 0
  tail_higher : ∀ i j index, index ∈ tail →
    leadingOrder i j < order i j index

def finitePolynomialTransportedEntry {ι : Type*}
    (data : FinitePolynomialMatrixData ι) (frameExponent : Fin 4 → Nat)
    (i j : Fin 4) (t : Real) : Real :=
  t ^ frameExponent i *
    finiteMonomialSum data.tail (data.leadingCoefficient i j)
      (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t *
    (t ^ frameExponent j)⁻¹

def finitePolynomialTransportedMatrix {ι : Type*}
    (data : FinitePolynomialMatrixData ι) (frameExponent : Fin 4 → Nat)
    (t : Real) : Matrix4 :=
  fun i j => finitePolynomialTransportedEntry data frameExponent i j t

def finitePolynomialLimit {ι : Type*} (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat) : Matrix4 :=
  fun i j => if frameExponent j = frameExponent i + data.leadingOrder i j then
    data.leadingCoefficient i j else 0

def FinitePolynomialValuationsNonnegative {ι : Type*}
    (data : FinitePolynomialMatrixData ι) (frameExponent : Fin 4 → Nat) : Prop :=
  ∀ i j, frameExponent j ≤ frameExponent i + data.leadingOrder i j

private theorem transportedEntry_eq_normalized_positive {ι : Type*}
    (data : FinitePolynomialMatrixData ι) (frameExponent : Fin 4 → Nat)
    (i j : Fin 4) {t : Real} (ht : t ≠ 0)
    (h : frameExponent j ≤ frameExponent i + data.leadingOrder i j) :
    finitePolynomialTransportedEntry data frameExponent i j t =
      normalizedFiniteMonomialSum data.tail (data.leadingCoefficient i j)
        (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t *
      t ^ (frameExponent i + data.leadingOrder i j - frameExponent j) := by
  have hFactor := finiteMonomialSum_div_leadingPower data.tail
    (data.leadingCoefficient i j) (data.leadingOrder i j)
    (data.coefficient i j) (data.order i j)
    (fun index hi => (data.tail_higher i j index hi).le) ht
  have hf : finiteMonomialSum data.tail (data.leadingCoefficient i j)
      (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t =
      normalizedFiniteMonomialSum data.tail (data.leadingCoefficient i j)
        (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t *
        t ^ data.leadingOrder i j := by
    exact (div_eq_iff (pow_ne_zero _ ht)).mp hFactor
  rw [finitePolynomialTransportedEntry, hf, pow_sub₀ t ht h]
  field_simp [pow_ne_zero _ ht]
  ring

private theorem transportedEntry_eq_normalized_inverse {ι : Type*}
    (data : FinitePolynomialMatrixData ι) (frameExponent : Fin 4 → Nat)
    (i j : Fin 4) {t : Real} (ht : t ≠ 0)
    (h : frameExponent i + data.leadingOrder i j ≤ frameExponent j) :
    finitePolynomialTransportedEntry data frameExponent i j t =
      normalizedFiniteMonomialSum data.tail (data.leadingCoefficient i j)
        (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t *
      (t ^ (frameExponent j -
        (frameExponent i + data.leadingOrder i j)))⁻¹ := by
  have hFactor := finiteMonomialSum_div_leadingPower data.tail
    (data.leadingCoefficient i j) (data.leadingOrder i j)
    (data.coefficient i j) (data.order i j)
    (fun index hi => (data.tail_higher i j index hi).le) ht
  have hf : finiteMonomialSum data.tail (data.leadingCoefficient i j)
      (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t =
      normalizedFiniteMonomialSum data.tail (data.leadingCoefficient i j)
        (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t *
        t ^ data.leadingOrder i j := by
    exact (div_eq_iff (pow_ne_zero _ ht)).mp hFactor
  rw [finitePolynomialTransportedEntry, hf]
  field_simp [pow_ne_zero _ ht]
  have hp : t ^ frameExponent i * t ^ data.leadingOrder i j *
      t ^ (frameExponent j - (frameExponent i + data.leadingOrder i j)) =
      t ^ frameExponent j := by
    rw [← pow_add, ← pow_add, Nat.add_sub_of_le h]
  calc
    t ^ frameExponent i *
          normalizedFiniteMonomialSum data.tail (data.leadingCoefficient i j)
            (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t *
        t ^ data.leadingOrder i j *
      t ^ (frameExponent j - (frameExponent i + data.leadingOrder i j)) =
      normalizedFiniteMonomialSum data.tail (data.leadingCoefficient i j)
        (data.leadingOrder i j) (data.coefficient i j) (data.order i j) t *
        (t ^ frameExponent i * t ^ data.leadingOrder i j *
          t ^ (frameExponent j - (frameExponent i + data.leadingOrder i j))) := by ring
    _ = _ := by rw [hp]

theorem finitePolynomialTransportedMatrix_tendsto {ι : Type*}
    (data : FinitePolynomialMatrixData ι) (frameExponent : Fin 4 → Nat)
    (hValuation : FinitePolynomialValuationsNonnegative data frameExponent) :
    Tendsto (finitePolynomialTransportedMatrix data frameExponent)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finitePolynomialLimit data frameExponent)) := by
  have hEntries : ∀ i j, Tendsto
      (fun t => finitePolynomialTransportedEntry data frameExponent i j t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finitePolynomialLimit data frameExponent i j)) := by
    intro i j
    have hNorm := normalizedFiniteMonomialSum_tendsto_leadingCoefficient
      data.tail (data.leadingCoefficient i j) (data.leadingOrder i j)
      (data.coefficient i j) (data.order i j) (data.tail_higher i j)
    by_cases heq : frameExponent j = frameExponent i + data.leadingOrder i j
    · rw [finitePolynomialLimit, if_pos heq]
      apply hNorm.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [heq] using (transportedEntry_eq_normalized_positive
        data frameExponent i j ht.ne' (hValuation i j)).symm
    · have hlt : frameExponent j < frameExponent i + data.leadingOrder i j :=
        lt_of_le_of_ne (hValuation i j) heq
      have hPow := positivePower_tendsto_zero (Nat.sub_pos_of_lt hlt)
      simpa [finitePolynomialLimit, heq] using (hNorm.mul hPow).congr' (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (transportedEntry_eq_normalized_positive data frameExponent i j
          ht.ne' (hValuation i j)).symm)
  have hPi : Tendsto
      (fun t i j => finitePolynomialTransportedMatrix data frameExponent t i j)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fun i j => finitePolynomialLimit data frameExponent i j)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    exact hEntries i
  exact hPi

theorem finitePolynomialTransportedMatrix_no_finite_limit_of_negativeEntry
    {ι : Type*} (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat) {i j : Fin 4}
    (hNegative : frameExponent i + data.leadingOrder i j < frameExponent j)
    (candidate : Matrix4) :
    ¬ Tendsto (finitePolynomialTransportedMatrix data frameExponent)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  intro hMatrix
  have hNorm := normalizedFiniteMonomialSum_tendsto_leadingCoefficient
    data.tail (data.leadingCoefficient i j) (data.leadingOrder i j)
    (data.coefficient i j) (data.order i j) (data.tail_higher i j)
  have hNoFinite := normalized_mul_inversePower_no_finite_limit _ hNorm
    (data.leading_nonzero i j) (Nat.sub_pos_of_lt hNegative) (candidate i j)
  apply hNoFinite
  have hEntry := (continuous_id.matrix_elem i j).tendsto candidate
  apply (hEntry.comp hMatrix).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact transportedEntry_eq_normalized_inverse data frameExponent i j ht.ne'
    hNegative.le

theorem finitePolynomialValuationsNonnegative_iff_exists_finite_limit
    {ι : Type*} (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat) :
    FinitePolynomialValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto (finitePolynomialTransportedMatrix data frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  constructor
  · intro hValuation
    exact ⟨finitePolynomialLimit data frameExponent,
      finitePolynomialTransportedMatrix_tendsto data frameExponent hValuation⟩
  · rintro ⟨candidate, hCandidate⟩ i j
    by_contra hValuation
    exact finitePolynomialTransportedMatrix_no_finite_limit_of_negativeEntry
      data frameExponent (Nat.lt_of_not_ge hValuation) candidate hCandidate

end
end P0EFTJanusFinitePolynomialMatrixValuationCriterion4D
end JanusFormal
